(* Copyright (c) 2023 Microsoft Research, Anton Lorenzen, Wouter Swierstra *)

From Equations Require Import Equations.
From fip_iris Require Import lang.
Require Import Program.

Inductive tree : Set :=
| Leaf
| Node (rk : Z) (l : tree) (x : Z) (r : tree).

Create HintDb trees.

Inductive root_tree : Set :=
| Root (rk : Z) (l : tree) (x : Z) (r : tree).

Definition to_tree (r : root_tree) : tree :=
  match r with
  | Root rk l x r => Node rk l x r
  end.

Definition is_higher_rank (rk1 rk2 : Z) (x1 x2 : Z) : bool :=
  bool_decide (rk2 < rk1)%Z || (bool_decide (rk1 = rk2)%Z && bool_decide (x1 < x2)%Z).

Definition heap_is_higher_rank : val :=
  rec: "is_higher_rank" "rk1" "rk2" "x1" "x2" :=
    ("rk2" < "rk1") || (("rk1" == "rk2") && ("x1" < "x2")).

Lemma heap_is_higher_rank_correct `{!heapGS Σ} (rk1 rk2 x1 x2 : Z) :
  {{{ True }}}
    heap_is_higher_rank #rk1 #rk2 #x1 #x2
  {{{ v, RET v; ∃ (b : bool), ⌜v = #b⌝ ∗ ⌜b = is_higher_rank rk1 rk2 x1 x2⌝ }}}.
Proof.
  wp_begin "H". unfold is_higher_rank.
  repeat case_bool_decide; iSteps.
Qed.

(* Recursive *)

Fixpoint smaller (i : Z) (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node rk l x r =>
    if bool_decide (x < i)%Z then
      Node rk l x (smaller i r)
    else
      smaller i l
  end.

Fixpoint bigger (i : Z) (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node rk l x r =>
    if bool_decide (x < i)%Z then
      bigger i r
    else
      Node rk (bigger i l) x r
  end.

Fixpoint rec_insert (i : Z) (rank : Z) (t : tree) : tree :=
  match t with
  | Node rnk l x r =>
    if is_higher_rank rnk rank x i
      then if bool_decide (x < i)%Z
        then Node rnk l x (rec_insert i rank r)
        else Node rnk (rec_insert i rank l) x r
      else if bool_decide (x = i)%Z then t
      else Node rank (smaller i t) i (bigger i t) 
  | Leaf => Node rank (smaller i t) i (bigger i t) 
  end.

Local Hint Unfold rec_insert : trees.

(* Bottom-up *)

Inductive zipper : Set :=
| NodeR (rk : Z) (l : tree) (x : Z) (r : zipper)
| NodeL (rk : Z) (l : zipper) (x : Z) (r : tree)
| Done.

Fixpoint rebuild (z : zipper) (t : tree) : tree :=
  match z with
  | NodeR rk l x up => rebuild up (Node rk l x t)
  | NodeL rk up x r => rebuild up (Node rk t x r)
  | Done => t
  end.

Fixpoint bu_unzip (t : tree) (k : Z) (zs : zipper) (zb : zipper) : (tree * tree) :=
  match t with
  | Node rk l x r =>
    if bool_decide (x < k)%Z then
      bu_unzip r k (NodeR rk l x zs) zb
    else
      bu_unzip l k zs (NodeL rk zb x r)
  | Leaf => (rebuild zs Leaf, rebuild zb Leaf)
  end.

Fixpoint bu_insert_go (t : tree) (rank : Z) (k : Z) (acc : zipper) : tree :=
  match t with
  | Node rk l x r =>
    if is_higher_rank rk rank x k
      then if bool_decide (x < k)%Z
        then bu_insert_go r rank k (NodeR rk l x acc)
        else bu_insert_go l rank k (NodeL rk acc x r)
    else if bool_decide (x = k)%Z then rebuild acc t
    else match bu_unzip t k Done Done with
      | (s,b) => rebuild acc (Node rank s k b)
      end
  | Leaf => rebuild acc (Node rank Leaf k Leaf)
  end.

Definition bu_insert (t : tree) (rank : Z) (k : Z) : tree :=
  bu_insert_go t rank k Done.

Local Hint Unfold rebuild bu_insert_go bu_insert : trees.

(* Top-down *)

Inductive ctx0 : Set :=
| Node0 (rk : Z) (z : ctx0) (x : Z) (r : tree)
| Node2 (rk : Z) (l : tree) (x : Z) (z : ctx0)
| Node0' (rk : Z) (* Hole *) (x : Z) (r : tree)
| Node2' (rk : Z) (l : tree) (x : Z) (* Hole *).

Inductive ctx : Set :=
| Ctx0 (z : ctx0)
| Hole.

Fixpoint comp0 (z1 z2 : ctx0) : ctx0 :=
  match z1 with
  | Node0 rk zl x r => Node0 rk (comp0 zl z2) x r
  | Node2 rk l x zr => Node2 rk l x (comp0 zr z2)
  | Node0' rk x r => Node0 rk z2 x r
  | Node2' rk l x => Node2 rk l x z2 
  end.

Definition comp' (z1 : ctx) (z2 : ctx0) : ctx0 :=
  match z1 with
  | Ctx0 z1 => comp0 z1 z2
  | Hole => z2
  end.

Definition comp (z1 : ctx) (z2 : ctx0) : ctx :=
  Ctx0 (comp' z1 z2).

Fixpoint plug0 (z : ctx0) (t : tree) : tree :=
  match z with
  | Node0 rk zl x r => Node rk (plug0 zl t) x r
  | Node2 rk l x zr => Node rk l x (plug0 zr t)
  | Node0' rk x r => Node rk t x r
  | Node2' rk l x => Node rk l x t
  end.

Definition plug (z : ctx) (t : tree) : tree :=
  match z with
  | Ctx0 z => plug0 z t
  | Hole => t
  end.

Lemma comp_plug (z : ctx) (z' : ctx0) (t : tree)
  : plug (comp z z') t = plug z (plug (Ctx0 z') t).
Proof.
    destruct z.
    - induction z; simpl; try (unfold plug, comp in IHz; rewrite IHz); done.
    - unfold plug, comp; done.
Qed.

Fixpoint size (t : tree) :=
  match t with
  | Leaf => 0
  | Node rk l x r => S (size l + size r)
  end.

Fixpoint td_right (t : tree) (k : Z) (acc : ctx) :=
  match t with
  | Node rk l x r =>
    if bool_decide (x >= k)%Z then (t, acc)
    else td_right r k (comp acc (Node2' rk l x))
  | Leaf => (t, acc)
  end.

Lemma td_right_size (t: tree) (k : Z) : forall acc,
  size (td_right t k acc).1 <= size t.
Proof.
  induction t.
  - simpl. lia.
  - unfold td_right. case_bool_decide.
    + simpl. lia.
    + intro acc. specialize IHt2 with (comp acc (Node2' rk t1 x)).
      fold td_right. simpl. lia.
Qed.

Fixpoint td_left (t : tree) (k : Z) (acc : ctx) : tree * ctx :=
  match t with
  | Node rk l x r =>
    if bool_decide (x < k)%Z then (t, acc)
    else td_left l k (comp acc (Node0' rk x r))
  | Leaf => (t, acc)
  end.

Lemma td_left_size (t: tree) (k : Z) : forall acc,
  size (td_left t k acc).1 <= size t.
Proof.
  induction t.
  - simpl. lia.
  - unfold td_left. case_bool_decide.
    + simpl. lia.
    + intro acc. specialize IHt1 with (comp acc (Node0' rk x t2)).
      fold td_left. simpl. lia.
Qed.

Equations? td_unzip (t : tree) (k : Z) (lctx rctx : ctx) : tree * tree by wf (size t) lt :=
  td_unzip (Node rk l x r) k lctx rctx :=
    match decide (x < k)%Z with
    | left H =>
      td_unzip (td_right (Node rk l x r) k lctx).1 k
               (td_right (Node rk l x r) k lctx).2 rctx
    | right H =>
      td_unzip (td_left (Node rk l x r) k rctx).1 k lctx
               (td_left (Node rk l x r) k rctx).2
    end;
  td_unzip Leaf _ lctx rctx :=
    (plug lctx Leaf, plug rctx Leaf).
Proof.
  - case_bool_decide; pose proof (td_right_size r k (comp lctx (Node2' rk l x))); lia.
  - case_bool_decide; pose proof (td_left_size l k (comp rctx (Node0' rk x r))); lia.
Qed.

Fixpoint td_insert_go (t : tree) (rank : Z) (k : Z) (acc : ctx) : tree :=
  match t with
  | Node rk l x r =>
      if is_higher_rank rk rank x k then
        if bool_decide (x < k)%Z
        then td_insert_go r rank k (comp acc (Node2' rk l x))
        else td_insert_go l rank k (comp acc (Node0' rk x r))
      else if bool_decide (x = k)%Z then plug acc t
      else
        let (l, r) := td_unzip t k Hole Hole
        in plug acc (Node rank l k r)
  | Leaf => plug acc (Node rank Leaf k Leaf)
  end.

Definition td_insert (t : tree) (rank : Z) (k : Z) : tree :=
  td_insert_go t rank k Hole.

Local Hint Unfold td_insert td_insert_go : trees.

(* Proof of equivalence *)

Lemma smaller_bigger_is_bu_unzip (i : Z) : forall t z1 z2,
  (rebuild z1 (smaller i t), rebuild z2 (bigger i t)) = bu_unzip t i z1 z2.
Proof.
  induction t; unfold smaller; unfold bigger; unfold bu_unzip. reflexivity. case_bool_decide.
  - fold bu_unzip. intros. rewrite <- IHt2. reflexivity.
  - fold bu_unzip. intros. rewrite <- IHt1. reflexivity.
Qed.

Lemma rec_is_bu_go (i rank : Z) : forall t z,
  rebuild z (rec_insert i rank t) = bu_insert_go t rank i z.
Proof.
  induction t; autounfold with trees. reflexivity.
  destruct (is_higher_rank rk rank x i).
  - case_bool_decide.
    + fold bu_insert_go. intros. rewrite <- IHt2. reflexivity.
    + fold bu_insert_go. intros. rewrite <- IHt1. reflexivity.
  - case_bool_decide.
    + reflexivity.
    + rewrite <- smaller_bigger_is_bu_unzip. reflexivity.
Qed.

Lemma rec_is_bu (i rank : Z) (t : tree) : rec_insert i rank t = bu_insert t rank i.
Proof.
  unfold bu_insert. rewrite <- rec_is_bu_go. reflexivity.
Qed.

Lemma td_right_id (i : Z) : forall t z1 z2,
  td_unzip (td_right t i z1).1 i (td_right t i z1).2 z2 = td_unzip t i z1 z2.
Proof.
  intros. destruct t. reflexivity. unfold td_right. case_bool_decide.
  - reflexivity.
  - fold td_right. simp td_unzip. case_decide.
    + unfold td_right. case_bool_decide. lia. fold td_right. reflexivity.
    + lia.
Qed.

Lemma td_right_step {i rk x : Z} (H : (x < i)%Z) : forall t1 t2 z1 z2,
  td_unzip (td_right (Node rk t1 x t2) i z1).1 i
    (td_right (Node rk t1 x t2) i z1).2 z2
  = td_unzip t2 i (comp z1 (Node2' rk t1 x)) z2.
Proof.
  intros. unfold td_right. case_bool_decide.
  - lia.
  - fold td_right. rewrite (td_right_id). reflexivity.
Qed.

Lemma td_left_id (i : Z) : forall t z1 z2,
  td_unzip (td_left t i z2).1 i z1 (td_left t i z2).2 = td_unzip t i z1 z2.
Proof.
  intros. destruct t. reflexivity. unfold td_left. case_bool_decide.
  - reflexivity.
  - fold td_left. simp td_unzip. case_decide.
    + lia.
    + unfold td_left. case_bool_decide. lia. fold td_left. reflexivity.
Qed.

Lemma td_left_step {i rk x : Z} (H : (x >= i)%Z) : forall t1 t2 z1 z2,
  td_unzip (td_left (Node rk t1 x t2) i z2).1 i z1
    (td_left (Node rk t1 x t2) i z2).2
  = td_unzip t1 i z1 (comp z2 (Node0' rk x t2)).
Proof.
  intros. unfold td_left. case_bool_decide.
  - lia.
  - fold td_left. rewrite (td_left_id). reflexivity.
Qed.

Lemma smaller_bigger_is_td_unzip (i : Z) : forall t z1 z2,
  (plug z1 (smaller i t), plug z2 (bigger i t)) = td_unzip t i z1 z2.
Proof.
  induction t; unfold smaller; unfold bigger.
  reflexivity. intros. simp td_unzip. case_bool_decide; case_decide; try lia.
  - rewrite (td_right_step H). rewrite <- IHt2. rewrite comp_plug. reflexivity.
  - rewrite (td_left_step H). rewrite <- IHt1. rewrite comp_plug. reflexivity.
Qed.

Lemma rec_is_td_go (i rank : Z) : forall t z,
  plug z (rec_insert i rank t) = td_insert_go t rank i z.
Proof.
  induction t; autounfold with trees. reflexivity.
  destruct (is_higher_rank rk rank x i).
  - case_bool_decide.
    + fold td_insert_go. intros. rewrite <- IHt2. rewrite comp_plug. reflexivity.
    + fold td_insert_go. intros. rewrite <- IHt1. rewrite comp_plug. reflexivity.
  - case_bool_decide.
    + reflexivity.
    + now rewrite <- smaller_bigger_is_td_unzip.
Qed.

Lemma rec_is_td (i rank : Z) (t : tree) : rec_insert i rank t = td_insert t rank i.
Proof.
  unfold td_insert. rewrite <- rec_is_td_go. reflexivity.
Qed.

Lemma td_is_bu (i rank : Z) (t : tree) : bu_insert t rank i = td_insert t rank i.
Proof. now rewrite <- rec_is_bu, rec_is_td. Qed.

(* Properties of zip trees *)

(* TODO: fix *)

Inductive all (P : Z -> Type) : tree -> Type :=
| all_leaf : all P Leaf
| all_node : forall {l : tree} {rnk x : Z} {r : tree},
             all P l -> P x -> all P r -> all P (Node rnk l x r).

Local Hint Constructors all : trees.

Lemma all_impl {P Q : Z → Set} {t : tree} (H : all P t) (f : forall x : Z, P x → Q x) : all Q t.
Proof.
  induction t; [ now trivial with trees | ].
  inversion H; now auto with trees.
Qed.

Local Hint Resolve all_impl : trees.
Local Hint Unfold insert : trees.
Inductive in_tree (x : Z) : tree -> Type :=
  | in_root : forall {l r : tree} {rnk : Z}, in_tree x (Node rnk l x r)
  | in_left : forall {l r : tree} {y rnk : Z},
      in_tree x l -> in_tree x (Node rnk l y r)
  | in_right : forall {l r : tree} {y rnk : Z},
      in_tree x r -> in_tree x (Node rnk l y r).

Local Hint Constructors in_tree : trees.

Lemma in_tree_all (P : Z -> Type) {t : tree} {x : Z} :
  in_tree x t -> all P t -> P x.
  Proof.  
  induction t as [ | rnk l IHl k r IHr].
  - intros H; now inversion H.
  - intros elem allP; inversion elem; inversion allP; subst; try assumption.
    now apply IHl.
    now apply IHr.
  Qed.

Lemma not_in_left {l r : tree} {x rnk k : Z} :
  (in_tree k (Node rnk l x r) -> False) -> (in_tree k l -> False).
  intros fresh elem; apply fresh; now apply in_left.
Qed.  

Lemma not_in_right {l r : tree} {x rnk k : Z} :
  (in_tree k (Node rnk l x r) -> False) -> (in_tree k r -> False).
  intros fresh elem; apply fresh; now apply in_right.
Qed.

Local Hint Resolve not_in_right not_in_left.

Lemma smaller_all {P : Z -> Type} {k : Z} {t : tree} :
  all P t -> all P (smaller k t).
  intro H; induction t as [ | rnk l IHl x r IHr]; [now constructor | ].
  inversion H; unfold smaller; case_bool_decide; subst.
  - constructor; try assumption. fold smaller. now apply IHr.
  - fold smaller. now apply IHl.
  Qed.

Lemma bigger_all {P : Z -> Type} {k  : Z} {t : tree} :
  all P t -> all P (bigger k t).
  intro H; induction t as [ | rnk l IHl x r IHr]; [now constructor | ].
  inversion H; unfold bigger; case_bool_decide; subst.
  - fold bigger. now apply IHr.
  - constructor; try assumption. now apply IHl.
  Qed.

Local Hint Resolve smaller_all bigger_all.

Lemma rec_insert_all {P : Z -> Type} {k rank : Z} {t : tree} :
  all P t -> P k -> all P (rec_insert k rank t).
Proof.
intros H pk; induction t as [ | rnk l IHl x r IHr].
- inversion H; constructor; trivial.
- inversion H; unfold rec_insert.
  destruct (is_higher_rank rnk rank x k).
  case_bool_decide; fold rec_insert.
  + constructor; try assumption; now apply IHr.
  + constructor; try assumption; now apply IHl.
  + case_bool_decide.
    * constructor;  assumption.
    * repeat constructor; try assumption.
      all: try apply smaller_all; try assumption.
      all: apply bigger_all; try assumption.
Qed.

Inductive is_bst : tree -> Type :=
| is_bst_leaf : is_bst Leaf
| is_bst_node : forall {x rnk : Z} {l r : tree},
    is_bst l -> all (fun y => Z.lt y x) l ->
    is_bst r -> all (fun y => Z.lt x y) r ->
    is_bst (Node rnk l x r).

Lemma smaller_bst (t : tree) (k : Z) (bst_t : is_bst t) 
   : is_bst (smaller k t).
Proof.
  induction t as [ | rnk l IHl x r IHr].
  - constructor.
  - unfold smaller; case_bool_decide; fold smaller.
    * inversion bst_t; constructor; subst; try assumption.
      apply IHr; try assumption.
      now apply smaller_all.
    * inversion bst_t; subst.
      now apply IHl.
Qed.      

Lemma smaller_is_smaller (t : tree) (k : Z) (bst_t : is_bst t) :
  all (fun y => Z.lt y k) (smaller k t).
  Proof.
    induction t as [ | rnk l IHl x r IHr].
    - constructor.
    - unfold smaller; case_bool_decide; fold smaller.
      * inversion bst_t as [ | x' rnk' l' r' bst_l all_l bst_r all_r ]; subst.
        constructor; [ apply (all_impl all_l); simpl; lia | lia | ].
        now apply IHr.
      * inversion bst_t; now apply IHl.
  Qed.

Lemma bigger_bst (t : tree) (k : Z) (bst_t : is_bst t) 
   : is_bst (bigger k t).
  induction t as [ | rnk l IHl x r IHr].
  - constructor.
  - unfold bigger; case_bool_decide; fold bigger.
    * inversion bst_t; subst.
      now apply IHr.
    * inversion bst_t; constructor; subst; try assumption.
      apply IHl; try assumption.
      now apply bigger_all.
  Qed.

Lemma bigger_is_bigger ( t : tree) (k : Z) (bst_t : is_bst t)
  (fresh : (in_tree k t -> False)) :
  all (fun y => Z.lt k y) (bigger k t).
  Proof.
    induction t as [ | rnk l IHl x r IHr].
    - constructor.
    - unfold bigger; case_bool_decide; fold bigger.
      * inversion bst_t; subst; apply IHr; try assumption.
        intro elem_r; apply fresh; auto with trees.
      * inversion bst_t as [ | x' rnk' l' r' bst_l all_l bst_r all_r ]; subst.
        constructor.
        apply IHl; try assumption.
        auto with trees.
        destruct (dec_eq x k).
        + subst. exfalso. apply fresh; constructor.
        + lia.
        + apply (all_impl all_r); simpl; intros; lia.
  Qed.

Lemma bst_left {l r : tree} {rank x y : Z} :
  is_bst (Node rank l x r) ->
  in_tree y (Node rank l x r) ->
  (y < x)%Z ->
  in_tree y l.
  Proof.
    intros bst elem lt.
    inversion elem; subst.
      - lia.
      - assumption.
      - inversion bst as [ | a b c d B0 B1 B2 B3]; subst.
        assert (x < y)%Z by (apply (in_tree_all _ H0); assumption). lia.
  Qed.

Lemma bst_right {l r : tree} {rank x y : Z} :
  is_bst (Node rank l x r) ->
  in_tree y (Node rank l x r) ->
  (x < y)%Z ->
  in_tree y r.
  Proof.
    intros bst elem lt.
    inversion elem; subst.
      - lia.
      - inversion bst; subst.
        assert (y < x)%Z.
        apply (in_tree_all (λ y : Z, (y < x)%Z) H0); assumption.
        lia.
      - assumption.
  Qed.
  
Lemma smaller_elem (t : tree) (k y : Z) :
  in_tree y t ->
  (y < k)%Z ->
  is_bst t ->
  in_tree y (smaller k t).
  Proof.
    intros H lt bst.
    induction t as [ | rnk l IHl x r IHr]; [ inversion H | ].
    unfold smaller; case_bool_decide; fold smaller.
    - inversion H; subst.
      * constructor.
      * now apply in_left.
      * apply in_right. apply IHr; try assumption. now inversion bst.
    - inversion H; subst.
      * contradiction.
      * apply IHl; inversion bst; assumption.
      * inversion bst; subst.
        assert (x < y)%Z by apply (in_tree_all _ H2 X2).
        lia.
   Qed.

Lemma bigger_elem (t : tree) (k y : Z) :
  in_tree y t ->
  (k < y)%Z ->
  is_bst t ->
  in_tree y (bigger k t).
  Proof.
    intros elem lt bst.
    induction t as [ | rnk l IHl x r IHr]; [ inversion elem | ].
    unfold bigger; case_bool_decide; fold bigger; subst.
    - inversion elem; subst.
      * lia.
      * inversion bst; subst.
        assert (y < x)%Z by apply (in_tree_all _ H1 X0).
        lia.
      * apply IHr; inversion bst; assumption.
    - inversion elem; subst.
      * constructor.
      * apply in_left.
        apply IHl; inversion bst; assumption.
      * now apply in_right.
  Qed.
  
Lemma unzip_elems (t : tree) (rank k y : Z) :
  in_tree y t  ->
  is_bst t ->
  in_tree y (Node rank (smaller k t) k (bigger k t)).
  Proof.
    intros inT bst; induction t as [ | rnk l IHl x r IHr]; [now inversion inT | ].
    destruct (Ztrichotomy_inf k y) as [[lt | eq] | gt].
    - apply in_right.
      now apply (bigger_elem).
    - subst; now constructor.
    - apply in_left.
      apply (smaller_elem); try assumption.
      lia.
  Qed.

Lemma preserves_elems (t : tree) (y k rank : Z) :
  is_bst t ->
  in_tree y t -> in_tree y (rec_insert k rank t).
  intros bst H; induction t as [ | rnk l IHl x r IHr]; inversion bst.
  + inversion H.
  + unfold rec_insert.
    destruct (is_higher_rank rnk rank x k); fold rec_insert.
    - case_bool_decide; inversion H; subst.
      * constructor.
      * now apply in_left.
      * apply in_right; now apply IHr.
      * constructor.
      * apply in_left; now apply IHl.
      * now apply in_right. 
    - case_bool_decide; subst.
      * assumption.
      * now apply unzip_elems.
  Qed. 

  
Lemma rec_insert_bst (t : tree) (k rank : Z) (bst_t : is_bst t)
  (fresh : (in_tree k t -> False))
  : is_bst (rec_insert k rank t).
Proof.
  autounfold with trees. induction t as [ | rnk l IHl x r IHr].
  - constructor; now eauto with trees.
  - fold smaller bigger rec_insert in *;
      case_bool_decide; destruct (is_higher_rank rnk rank x k);
      inversion bst_t; subst.
    * constructor; try assumption.
      apply IHr; eauto with trees.
      now apply rec_insert_all. 
    * case_bool_decide; [ assumption | ].
      constructor.
      now apply smaller_bst.
      now apply smaller_is_smaller.
      now apply bigger_bst.
      now apply bigger_is_bigger.
    * constructor; try assumption.
      apply IHl; auto with trees.
      apply rec_insert_all; try assumption.
      destruct (dec_eq x k).
        + subst. exfalso. apply fresh; constructor.
        + lia.
    * case_bool_decide; [ assumption | ].
      constructor.
      now apply smaller_bst.
      now apply smaller_is_smaller.
      now apply bigger_bst.
      now apply bigger_is_bigger.
  Qed.



