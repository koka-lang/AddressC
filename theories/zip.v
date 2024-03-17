(* Copyright (c) 2023 Wouter Swierstra, Microsoft Research, Anton Lorenzen *)

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
  wp_begin "H". unfold is_higher_rank. repeat case_bool_decide; iSteps.
Qed.

(* Recursive *)

Fixpoint smaller (i : Z) (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node rk l x r =>
    if bool_decide (x < i)%Z then
      Node rk l x (smaller i r)
    else if bool_decide (x > i)%Z then
      smaller i l
    else l
  end.

Fixpoint bigger (i : Z) (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node rk l x r =>
    if bool_decide (x < i)%Z then
      bigger i r
    else if bool_decide (x > i)%Z then
      Node rk (bigger i l) x r
    else r
  end.

Fixpoint rec_insert (i : Z) (rank : Z) (t : tree) : tree :=
  match t with
  | Node rnk l x r =>
    if is_higher_rank rnk rank x i
    then if bool_decide (x < i)%Z
         then Node rnk l x (rec_insert i rank r)
         else Node rnk (rec_insert i rank l) x r
    else if bool_decide (x = i)%Z
         then t
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

Inductive ctx : Set :=
| Hole
| Node0 (rk : Z) (l : ctx) (x : Z) (r : tree)
| Node2 (rk : Z) (l : tree) (x : Z) (r : ctx).

Fixpoint comp (z1 : ctx) (z2 : ctx) :=
  match z1 with
  | Node0 rk zl x r => Node0 rk (comp zl z2) x r
  | Node2 rk l x zr => Node2 rk l x (comp zr z2)
  | Hole => z2
  end.

Fixpoint plug (z : ctx) (t : tree) : tree :=
  match z with
  | Node0 rk zl x r => Node rk (plug zl t) x r
  | Node2 rk l x zr => Node rk l x (plug zr t)
  | Hole => t
  end.

Lemma comp_plug (z1 : ctx) (z2 : ctx) (t : tree)
  : plug (comp z1 z2) t = plug z1 (plug z2 t).
Proof.
  induction z1.
  - simpl; done.
  - simpl; rewrite IHz1; done.
  - simpl; rewrite IHz1; done.
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
    else td_right r k (comp acc (Node2 rk l x Hole))
  | Leaf => (t, acc)
  end.

Lemma td_right_size (t: tree) (k : Z) : forall acc,
  size (td_right t k acc).1 <= size t.
Proof.
  induction t.
  - simpl. lia.
  - unfold td_right. case_bool_decide.
    + simpl. lia.
    + intro acc. specialize IHt2 with (comp acc (Node2 rk t1 x Hole)).
      fold td_right. simpl. lia.
Qed.

Fixpoint td_left (t : tree) (k : Z) (acc : ctx) : tree * ctx :=
  match t with
  | Node rk l x r =>
    if bool_decide (x < k)%Z then (t, acc)
    else td_left l k (comp acc (Node0 rk Hole x r))
  | Leaf => (t, acc)
  end.

Lemma td_left_size (t: tree) (k : Z) : forall acc,
  size (td_left t k acc).1 <= size t.
Proof.
  induction t.
  - simpl. lia.
  - unfold td_left. case_bool_decide.
    + simpl. lia.
    + intro acc. specialize IHt1 with (comp acc (Node0 rk Hole x t2)).
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
  - case_bool_decide; pose proof (td_right_size r k (comp lctx (Node2 rk l x Hole))); lia.
  - case_bool_decide; pose proof (td_left_size l k (comp rctx (Node0 rk Hole x r))); lia.
Qed.

Fixpoint td_insert_go (t : tree) (rank : Z) (k : Z) (acc : ctx) : tree :=
  match t with
  | Node rk l x r =>
      if is_higher_rank rk rank x k then
        if bool_decide (x < k)%Z
        then td_insert_go r rank k (comp acc (Node2 rk l x Hole))
        else td_insert_go l rank k (comp acc (Node0 rk Hole x r))
      else if bool_decide (x = k)%Z then plug acc t
      else
        let (l, r) := td_unzip t k Hole Hole
        in plug acc (Node rank l k r)
  | Leaf => plug acc (Node rank Leaf k Leaf)
  end.

Definition td_insert (t : tree) (rank : Z) (k : Z) : tree :=
  td_insert_go t rank k Hole.

Local Hint Unfold td_insert td_insert_go : trees.

(* Properties of zip trees *)

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
Inductive in_tree (x rank : Z) : tree -> Type :=
  | in_root : forall {l r : tree}, in_tree x rank (Node rank l x r)
  | in_left : forall {l r : tree} {y rnk : Z},
      in_tree x rank l -> in_tree x rank (Node rnk l y r)
  | in_right : forall {l r : tree} {y rnk : Z},
      in_tree x rank r -> in_tree x rank (Node rnk l y r).

Local Hint Constructors in_tree : trees.

Lemma in_tree_all (P : Z -> Type) {t : tree} {x rank : Z} :
  in_tree x rank t -> all P t -> P x.
  Proof.  
  induction t as [ | rnk l IHl k r IHr].
  - intros H; now inversion H.
  - intros elem allP; inversion elem; inversion allP; subst; try assumption.
    + now apply IHl.
    + now apply IHr.
Qed.

Lemma smaller_all {P : Z -> Type} {k : Z} {t : tree} :
  all P t -> all P (smaller k t).
  intro H; induction t as [ | rnk l IHl x r IHr]; [now constructor | ].
  inversion H; unfold smaller; case_bool_decide; subst.
  - constructor; try assumption. fold smaller. now apply IHr.
  - fold smaller. case_bool_decide.
    * now apply IHl.
    * assumption.
Qed.

Lemma bigger_all {P : Z -> Type} {k  : Z} {t : tree} :
  all P t -> all P (bigger k t).
  intro H; induction t as [ | rnk l IHl x r IHr]; [now constructor | ].
  inversion H; unfold bigger; case_bool_decide; subst.
  - fold bigger; now apply IHr.
  - case_bool_decide; fold bigger.
    + constructor; [ now apply IHl | assumption | assumption ].
    + assumption.
Qed.

Local Hint Resolve smaller_all bigger_all : trees.

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

Local Hint Resolve rec_insert_all : trees.

Inductive is_bst : tree -> Type :=
| is_bst_leaf : is_bst Leaf
| is_bst_node : forall {x rnk : Z} {l r : tree},
    is_bst l -> all (fun y => Z.le y x) l ->
    is_bst r -> all (fun y => Z.lt x y) r ->
    is_bst (Node rnk l x r).

Local Hint Constructors is_bst : trees.

Lemma smaller_bst (t : tree) (k : Z) (bst_t : is_bst t) 
   : is_bst (smaller k t).
Proof.
  induction t as [ | rnk l IHl x r IHr].
  - constructor.
  - unfold smaller; case_bool_decide; fold smaller.
    * inversion bst_t; constructor; subst; try assumption.
      + now apply IHr.
      + now apply smaller_all.
    * inversion bst_t; subst; case_bool_decide.
      + now apply IHl.
      + assumption.
Qed.      

Lemma smaller_is_smaller (t : tree) (k : Z) (bst_t : is_bst t) :
  all (fun y => Z.le y k) (smaller k t).
  Proof.
    induction t as [ | rnk l IHl x r IHr].
    - constructor.
    - unfold smaller; case_bool_decide; fold smaller.
      * inversion bst_t as [ | x' rnk' l' r' bst_l all_l bst_r all_r ]; subst.
        constructor; [ apply (all_impl all_l); simpl; lia | lia | ].
        now apply IHr.
      * inversion bst_t; case_bool_decide; [ now apply IHl | ].
        assert (x = k) by lia; subst; assumption.
  Qed.

Local Hint Resolve smaller_bst smaller_is_smaller : trees.
  
Lemma bigger_bst (t : tree) (k : Z) (bst_t : is_bst t) 
   : is_bst (bigger k t).
  induction t as [ | rnk l IHl x r IHr].
  - constructor.
  - unfold bigger; case_bool_decide; fold bigger.
    * inversion bst_t; subst.
      now apply IHr.
    * case_bool_decide.
      + inversion bst_t; constructor; subst; try assumption.
        now apply IHl.
        now apply bigger_all.
      + inversion bst_t; assumption.
Qed.

Lemma bigger_is_bigger ( t : tree) (k : Z) (bst_t : is_bst t) :
  all (fun y => Z.lt k y) (bigger k t).
  Proof.
    induction t as [ | rnk l IHl x r IHr].
    - constructor.
    - unfold bigger; case_bool_decide; fold bigger.
      * inversion bst_t; subst; apply IHr; try assumption.
      * inversion bst_t as [ | x' rnk' l' r' bst_l all_l bst_r all_r ]; subst.
        case_bool_decide.
        + constructor.
          now apply IHl.
          destruct (dec_eq x k).
          ++ lia.
          ++ lia.
          ++ apply (all_impl all_r); simpl; intros; lia.
        + assert (x = k) by lia; subst; assumption.
  Qed.

Local Hint Resolve bigger_bst bigger_is_bigger : trees.

Lemma bst_left {l r : tree} {rnk rank x y : Z} :
  is_bst (Node rnk l x r) ->
  in_tree y rank (Node rnk l x r) ->
  (Z.le y x)%Z ->
  sum (in_tree y rank l) (y = x /\ rank = rnk).
Proof.
  intros bst inT leq.
  inversion inT; subst.
  - right; now split.
  - now left. 
  - inversion bst; subst.
    assert (x < y)%Z.
    apply (in_tree_all (λ y : Z, (x < y)%Z) H0); try assumption.
    lia.
Qed.  

Lemma bst_left_strict {l r : tree} {rnk rank x y : Z} :
  is_bst (Node rnk l x r) ->
  in_tree y rank (Node rnk l x r) ->
  (Z.lt y x)%Z ->
  (in_tree y rank l).
Proof.
  intros bst inT leq.
  inversion inT; subst.
  - lia.
  - assumption.
  - inversion bst; subst.
    assert (x < y)%Z.
    apply (in_tree_all (λ y : Z, (x < y)%Z) H0); try assumption.
    lia.
Qed.

Lemma bst_right {l r : tree} {rnk rank x y : Z} :
  is_bst (Node rnk l x r) ->
  in_tree y rank (Node rnk l x r) ->
  (x < y)%Z ->
  in_tree y rank r.
  Proof.
    intros bst elem lt.
    inversion elem; subst.
      - lia.
      - inversion bst; subst.
        assert (y ≤ x)%Z.
        now apply (in_tree_all (λ y : Z, (y ≤ x)%Z) H0).
        lia.
      - assumption.
  Qed.

Local Hint Resolve bst_left bst_right : trees.
  
Lemma smaller_elem (t : tree) (k y rank : Z) :
  in_tree y rank t ->
  (Z.lt y k)%Z ->
  is_bst t ->
  in_tree y rank (smaller k t).
  Proof.
    intros H lt bst.
    induction t as [ | rnk l IHl x r IHr]; [ inversion H | ].
    unfold smaller; case_bool_decide; fold smaller.
    - inversion H; subst.
      * constructor.
      * now apply in_left.
      * apply in_right. apply IHr; try assumption. now inversion bst.
    - case_bool_decide.
      ++ inversion H; subst.
         assert (x = k) by lia; subst.
         exfalso; lia.
         apply IHl; try assumption.
         inversion bst; assumption.
         inversion bst; subst.
         assert (x < y)%Z.
         apply (in_tree_all (λ y : Z, (x < y)%Z) H3).
         assumption.
         lia.
      ++ assert (x = k) by lia; subst.
         clear H0; clear H1.
         destruct (bst_left bst H).
         lia.
         assumption.
         destruct a; lia.
Qed.


Lemma bigger_elem (t : tree) (k y rank : Z) :
  in_tree y rank t ->
  (k < y)%Z ->
  is_bst t ->
  in_tree y rank (bigger k t).
  Proof.
    intros elem lt bst.
    induction t as [ | rnk l IHl x r IHr]; [ inversion elem | ].
    unfold bigger; case_bool_decide; fold bigger; subst.
    - inversion elem; subst.
      * lia.
      * inversion bst; subst.
        assert (y ≤ x)%Z by apply (in_tree_all _ H1 X0).
        lia.
      * apply IHr; inversion bst; assumption.
    - inversion elem; subst; case_bool_decide.
        + constructor.
        + exfalso; lia.
        + apply in_left.
          apply IHl; inversion bst; assumption.
        + apply (bst_right bst elem).
          assert (x = k) by lia.
          subst; assumption.
        + now apply in_right.
        + assumption.
  Qed.

Local Hint Resolve smaller_elem bigger_elem : trees.

Inductive gt_rank (rank : Z) : tree -> Type :=
| gt_rank_leaf : gt_rank rank Leaf
| gt_rank_node : forall {x rnk : Z} {l r : tree},
    (rank > rnk)%Z ->
    gt_rank rank (Node rnk l x r).

Inductive ge_rank (rank : Z) : tree -> Type :=
| ge_rank_leaf : ge_rank rank Leaf
| ge_rank_node : forall {x rnk : Z} {l r : tree},
    (rank >= rnk)%Z ->
    ge_rank rank (Node rnk l x r).
                                         

Inductive is_zip : tree -> Type :=
| is_zip_leaf : is_zip Leaf
| is_zip_node : forall {x rank : Z} {l r : tree},
    gt_rank rank l ->
    ge_rank rank r ->
    is_zip l -> is_zip r -> is_zip (Node rank l x r).

Local Hint Constructors is_zip gt_rank ge_rank : trees.


Lemma zip_left : forall rank l x r, is_zip (Node rank l x r) -> is_zip l.
  intros rank l x r H; now inversion H.
  Qed.

Lemma zip_right : forall rank l x r, is_zip (Node rank l x r) -> is_zip r.
  intros rank l x r H; now inversion H.
  Qed.

Local Hint Resolve zip_left zip_right : trees.

Lemma higher_rank_true {rnk rank x k : Z} :
   (true = is_higher_rank rnk rank x k) -> (rank ≤ rnk)%Z.
Proof.
  unfold is_higher_rank.
  repeat case_bool_decide; simpl; intros; try lia.
Qed.  

Lemma higher_rank_false {rnk rank x k : Z} :
   (false = is_higher_rank rnk rank x k) -> (rank >= rnk)%Z.
  unfold is_higher_rank.
  repeat case_bool_decide; simpl; intros; try lia.
Qed.

Lemma gt_rank_trans {r r' : Z} {t : tree} (gtr : gt_rank r t) :
  (r <= r')%Z -> gt_rank r' t.
  inversion gtr; constructor; lia.
  Qed.

Lemma ge_rank_trans {r r' : Z} {t : tree} (gtr : ge_rank r t) :
  (r <= r')%Z -> ge_rank r' t.
  inversion gtr; constructor; lia.
  Qed.

Lemma unzip_elems (t : tree) (rank rnk k y  : Z) :
  in_tree y rank t ->
  is_bst t ->
  (y ≠ k) ->
  in_tree y rank
    (Node rnk (smaller k t) k (bigger k t)).
  intros inT isBst fresh.
  induction t as [ | rnk' l IHl x r IHr].
  - inversion inT.
  - destruct (Ztrichotomy_inf y k) as [[lt | eq] | gt].
    + apply in_left.
      apply smaller_elem; assumption.
    + subst. exfalso; intuition.
    + apply in_right; apply bigger_elem; assumption || lia.
Qed.

Lemma preserves_elems (t : tree) (y k rnk rank : Z) :
  is_bst t ->
  (y ≠ k) ->  
  in_tree y rank t -> in_tree y rank (rec_insert k rnk t).
  intros bst inT elem; induction t as [ | rnk' l IHl x r IHr]; inversion bst.
  + inversion elem.
  + unfold rec_insert.
    destruct (is_higher_rank rnk' rnk x k); fold rec_insert.
    - case_bool_decide; inversion elem; subst; eauto with trees.
    - case_bool_decide; subst; eauto with trees.
      now apply unzip_elems.
Qed. 

Local Hint Resolve rec_insert_all smaller_bst smaller_is_smaller
      bigger_is_bigger bigger_bst : trees.

Lemma rec_insert_bst (t : tree) (k rank : Z) (bst_t : is_bst t)
  : is_bst (rec_insert k rank t).
Proof.
  autounfold with trees. induction t as [ | rnk l IHl x r IHr].
  - constructor; now eauto with trees.
  - fold smaller bigger rec_insert in *;
      destruct (is_higher_rank rnk rank x k).
    * case_bool_decide; inversion bst_t; subst; constructor; eauto with trees.
      apply rec_insert_all; assumption || lia.
    *  case_bool_decide; inversion bst_t; subst; constructor;
         eauto with trees.
Qed.

Lemma rec_insert_ge_rank
      (t : tree) {k rank rnk : Z} :
      (rank ≤ rnk)%Z -> ge_rank rnk t ->  ge_rank rnk (rec_insert k rank t).
  intros le_r le_t; induction t as [ | rnk' l IHl x r IHr].
  constructor; lia.
  unfold rec_insert.
  remember (is_higher_rank rnk' rank x k) as b;
    rename Heqb into rankCmp; destruct b; fold rec_insert.
  case_bool_decide; inversion le_t; subst; constructor; lia.
  case_bool_decide; subst; constructor.
  assert (rank >= rnk')%Z by apply (higher_rank_false rankCmp); now lia.
  assert (rank >= rnk')%Z by apply (higher_rank_false rankCmp); now lia.
Qed.

Lemma rec_insert_gt_rank
      (t : tree) {k rank rnk : Z} :
  (rnk > rank)%Z ->
  gt_rank rnk t ->  gt_rank rnk (rec_insert k rank t).
Proof.  
  intros gt_r gt_t; induction t as [ | rnk' l IHl x r IHr].
  + now constructor.
  + unfold rec_insert; remember (is_higher_rank rnk' rank x k) as b;
    rename Heqb into rankCmp; destruct b; fold rec_insert.
    case_bool_decide.
    - inversion gt_t; subst; constructor; lia.
    - constructor; unfold is_higher_rank in *; repeat case_bool_decide; try lia.
      inversion gt_t. lia.
    - case_bool_decide.
      ++ constructor.
         unfold is_higher_rank in *; repeat case_bool_decide; try lia.
      ++ inversion gt_t;  constructor.
         unfold is_higher_rank in *; repeat case_bool_decide; try lia.
Qed.

Lemma gt_rank_smaller {rank k : Z} {t : tree}
  (gt_t : gt_rank rank t) (zip_t : is_zip t) :
  gt_rank rank (smaller k t).
Proof.  
  induction t as [ | rnk l IHl x r IHr]; [ now constructor | ].
  unfold smaller; case_bool_decide; fold smaller.
  inversion gt_t; constructor; subst; try assumption.
  case_bool_decide; inversion zip_t; inversion gt_t; subst.
  + apply IHl; try assumption.
    assert (GT : gt_rank rnk l) by assumption.
    apply (gt_rank_trans GT); lia.
  + assert (GT : gt_rank rnk l) by assumption.
    eapply (gt_rank_trans GT); lia.
Qed.

Lemma ge_rank_bigger {rank k : Z} {t : tree}
      (ge_t : ge_rank rank t) (zip_t : is_zip t) :
  ge_rank rank (bigger k t).
  induction t as [ | rnk l IHl x r IHr]; [ now constructor | ].
  unfold bigger; case_bool_decide; fold bigger;
    inversion ge_t; inversion zip_t; subst.
  + apply IHr; [ | assumption].
    assert (GE : ge_rank rnk r) by assumption.
    apply (ge_rank_trans GE); lia.
  + case_bool_decide.
    ++ constructor; lia.
    ++ assert (GE : ge_rank rnk r) by assumption.
       apply (ge_rank_trans GE); lia.
Qed.

Lemma ge_gt  {rank rnk : Z} {t : tree} :
  gt_rank rank t -> (rnk >= rank)%Z -> ge_rank rnk t.
  intro H; inversion H; constructor; lia.
  Qed.

Lemma gt_ge  {rank rnk : Z} {t : tree} :
  ge_rank rank t -> (rnk > rank)%Z -> gt_rank rnk t.
  intro H; inversion H; constructor; lia.
  Qed.


Lemma ge_rank_smaller {rank k : Z} {t : tree}
      (ge_t : ge_rank rank t) (zip_t : is_zip t) :
  ge_rank rank (smaller k t).
  induction t as [ | rnk l IHl x r IHr]; [ now constructor | ].
  unfold smaller; case_bool_decide; fold smaller;
    inversion ge_t; inversion zip_t; subst.
  + constructor; assumption.
  + case_bool_decide.
    - apply IHl; try assumption.
      assert (GT : gt_rank rnk l) by assumption.
      now apply (ge_gt GT).
    - assert (GT : gt_rank rnk l) by assumption.
      assert (GE : ge_rank rnk l) by (apply (ge_gt GT); lia).
      apply (ge_rank_trans GE); lia.
Qed.

Lemma gt_rank_bigger {rank k : Z} {t : tree}
      (gt_rank_t : gt_rank rank t) (zip_t : is_zip t) :
      gt_rank rank (bigger k t).
Proof.
  induction t as [ | rnk l IHl x r IHr]; [ now constructor | ].
  unfold bigger; case_bool_decide; fold bigger;
   inversion gt_rank_t; inversion zip_t; subst.
  - apply IHr; try assumption.
    assert (GE : ge_rank rnk r) by assumption.
    now apply (gt_ge GE).
  - case_bool_decide.
    ++ constructor; assumption.
    ++ assert (GE : ge_rank rnk r) by assumption.
       now (apply (gt_ge GE)).
Qed.

Lemma smaller_zips {k : Z} {t : tree}
      (zip_t : is_zip t) : is_zip (smaller k t).
Proof.
  induction t as [ | rank l IHl x r IHr]; [ now constructor | ].
  unfold smaller; case_bool_decide; fold smaller.
  + constructor; inversion zip_t; subst; eauto with trees.
    now apply ge_rank_smaller.
  +  case_bool_decide; inversion zip_t.
    - now apply IHl. 
    - assumption.
Qed.

Lemma bigger_zips {k : Z} {t : tree} (zip_t : is_zip t)  :
  is_zip (bigger k t).
Proof.
  induction t as [ | rank l IHl x r IHr]; [ now constructor | ].
  unfold bigger; case_bool_decide; fold bigger; inversion zip_t; subst.
  + now apply IHr.
  + case_bool_decide; try assumption.
    constructor; try assumption.
      ++ apply gt_rank_bigger; try assumption.
      ++ apply IHl; assumption.
Qed.

Lemma rec_insert_zip
      (t : tree) (k rank : Z) (zip_t : is_zip t) 
  : is_zip (rec_insert k rank t).
  autounfold with trees; induction t as [ | rnk l IHl x r IHr].
  - constructor; now eauto with trees.
  - fold smaller bigger rec_insert in *.
    remember (is_higher_rank rnk rank x k) as b;
      rename Heqb into rankCmp; destruct b.
    + case_bool_decide; inversion zip_t; subst.
      * constructor; try assumption.
        ++ apply rec_insert_ge_rank; try assumption.
           now apply (higher_rank_true rankCmp).
        ++ apply IHr.
           assumption.
      * constructor; try assumption.
        ++ apply rec_insert_gt_rank; try assumption.
           unfold is_higher_rank in rankCmp; repeat case_bool_decide; lia.
        ++ apply IHl.
           assumption.
    + case_bool_decide; inversion zip_t; subst.
      * constructor; try assumption.
      * constructor.
        ++ assert (rank >= rnk)%Z by (apply (higher_rank_false rankCmp)).
           unfold smaller; case_bool_decide; fold smaller.
           unfold is_higher_rank in rankCmp; simpl in rankCmp.
           assert (rnkLeRank : (rnk ≤ rank)%Z) by lia.
           destruct (Z_le_lt_eq_dec _ _ rnkLeRank).
           constructor; try lia; subst.
           case_bool_decide; inversion rankCmp.
           case_bool_decide; inversion rankCmp.
           case_bool_decide.
           exfalso; now intuition.
           exfalso; now intuition.
           exfalso; now intuition.
           case_bool_decide.
           +++ apply gt_rank_smaller.
           assert (gt_rank rnk l) as GTRankL by assumption.
           apply (gt_rank_trans GTRankL); now lia. 
           assumption.
           +++ assert (x = k) by lia; contradiction.
        ++ apply ge_rank_bigger; constructor; try assumption.
           assert (rank >= rnk)%Z by (apply (higher_rank_false rankCmp)).
           trivial.
        ++ now apply smaller_zips.
        ++ now apply bigger_zips.
Qed.

Lemma ranks_non_increasing_ge {t : tree} {k rnk rank : Z} :
  is_zip t -> ge_rank rank t -> in_tree k rnk t -> (rnk <= rank)%Z.
Proof.
  induction t.
  - intros. inversion H1.
  - intros. inversion H1.
    + subst. inversion H0. lia.
    + inversion H; subst. assert (ge_rank rank t1).
      apply (ge_gt H11). now inversion H0. now apply IHt1.
    + inversion H; subst. inversion H0. assert (ge_rank rank t2).
      apply (ge_rank_trans H12). lia. now apply IHt2. 
Qed.

Lemma ranks_non_increasing_gt {t : tree} {k rnk rank : Z} :
  is_zip t -> gt_rank rank t -> in_tree k rnk t -> (rnk < rank)%Z.
Proof.
  induction t.
  - intros. inversion H1.
  - intros. inversion H1.
    + subst. inversion H0. lia.
    + inversion H; subst. inversion H0. assert (gt_rank rank t1).
      apply (gt_rank_trans H11). lia. now apply IHt1.
    + inversion H; subst. inversion H0. assert (gt_rank rank t2).
      inversion H12. now apply gt_rank_leaf. apply gt_rank_node. lia.
      now apply IHt2.
Qed.

Lemma fresh_key_below_correct_rank (x i rank rk : Z) (t1 t2 : tree)
  (zt : is_zip (Node rk t1 x t2)) (bt : is_bst (Node rk t1 x t2))
  (rankFromKey : ∀ rk0 : Z, in_tree i rk0 (Node rk t1 x t2) → rk0 = rank)
  (H : x ≠ i) (H0 : is_higher_rank rk rank x i = false)
  : forall x0 rk0, in_tree x0 rk0 (Node rk t1 x t2) -> x0 ≠ i.
Proof.
  intros. intro. subst. assert (rk0 = rank) by now apply (rankFromKey rk0).
  inversion H1.
  - lia.
  - inversion zt.
    assert (rk0 < rk)%Z by apply (ranks_non_increasing_gt H14 H12 H4).
    unfold is_higher_rank in H0. repeat case_bool_decide; try lia.
  - inversion zt. assert (rk0 <= rk)%Z by apply (ranks_non_increasing_ge H15 H13 H4).
    unfold is_higher_rank in H0. repeat case_bool_decide; try lia.
    subst. inversion bt. assert (x < i)%Z by apply (in_tree_all (λ y : Z, (x < y)%Z) H4 X2).
    contradiction.
Qed.

(* Proof of equivalence *)

Lemma smaller_bigger_is_bu_unzip (i : Z) (t : tree)
  (freshKey : (forall x rk, in_tree x rk t -> x ≠ i)) : forall z1 z2,
  (rebuild z1 (smaller i t), rebuild z2 (bigger i t)) = bu_unzip t i z1 z2.
Proof.
  induction t; unfold smaller; unfold bigger; unfold bu_unzip. reflexivity. case_bool_decide.
  - fold bu_unzip. intros. rewrite <- IHt2. reflexivity.
    intros. apply (freshKey x0 rk0). now apply in_right.
  - fold bu_unzip. case_bool_decide.
    + intros. rewrite <- IHt1. reflexivity.
      intros. apply (freshKey x0 rk0). now apply in_left.
    + exfalso. apply (freshKey x rk). now apply in_root. lia.
Qed.

Lemma rec_is_bu_go (i rank : Z) (t : tree) (zt : is_zip t) (bt : is_bst t)
  (rankFromKey : (forall rk, in_tree i rk t -> rk = rank))
  : forall z, rebuild z (rec_insert i rank t) = bu_insert_go t rank i z.
Proof.
  induction t; autounfold with trees. reflexivity.
  case_eq (is_higher_rank rk rank x i).
  - case_bool_decide.
    + fold bu_insert_go. intros. rewrite <- IHt2. reflexivity.
      now inversion zt. now inversion bt.
      intros. apply (rankFromKey rk0). now apply in_right.
    + fold bu_insert_go. intros. rewrite <- IHt1. reflexivity.
      now inversion zt. now inversion bt.
      intros. apply (rankFromKey rk0). now apply in_left.
  - case_bool_decide.
    + reflexivity.
    + intros. rewrite <- smaller_bigger_is_bu_unzip. reflexivity.
      now apply (fresh_key_below_correct_rank x i rank rk).
Qed.

Lemma rec_is_bu (i rank : Z) (t : tree) (zt : is_zip t) (bt : is_bst t)
  (rankFromKey : (forall rk, in_tree i rk t -> rk = rank))
  : rec_insert i rank t = bu_insert t rank i.
Proof.
  unfold bu_insert. now rewrite <- rec_is_bu_go.
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
  = td_unzip t2 i (comp z1 (Node2 rk t1 x Hole)) z2.
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
  = td_unzip t1 i z1 (comp z2 (Node0 rk Hole x t2)).
Proof.
  intros. unfold td_left. case_bool_decide.
  - lia.
  - fold td_left. rewrite (td_left_id). reflexivity.
Qed.

Lemma smaller_bigger_is_td_unzip (i : Z) (t : tree)
  (freshKey : (forall x rk, in_tree x rk t -> x ≠ i)) : forall z1 z2,
  (plug z1 (smaller i t), plug z2 (bigger i t)) = td_unzip t i z1 z2.
Proof.
  induction t; unfold smaller; unfold bigger.
  reflexivity. intros. simp td_unzip. case_bool_decide; case_decide; try lia.
  - rewrite (td_right_step H). rewrite <- IHt2. rewrite comp_plug. reflexivity.
    intros. apply (freshKey x0 rk0). now apply in_right.
  - rewrite (td_left_step H). rewrite <- IHt1. rewrite comp_plug. case_bool_decide.
    + reflexivity.
    + exfalso. apply (freshKey x rk). now apply in_root. lia.
    + intros. apply (freshKey x0 rk0). now apply in_left.
Qed.

Lemma rec_is_td_go (i rank : Z) (t : tree) (zt : is_zip t) (bt : is_bst t)
  (rankFromKey : (forall rk, in_tree i rk t -> rk = rank))
  : forall z, plug z (rec_insert i rank t) = td_insert_go t rank i z.
Proof.
  induction t; autounfold with trees. reflexivity.
  case_eq (is_higher_rank rk rank x i).
  - case_bool_decide.
    + fold td_insert_go. intros. rewrite <- IHt2. rewrite comp_plug. reflexivity.
      now inversion zt. now inversion bt.
      intros. apply (rankFromKey rk0). now apply in_right.
    + fold td_insert_go. intros. rewrite <- IHt1. rewrite comp_plug. reflexivity.
      now inversion zt. now inversion bt.
      intros. apply (rankFromKey rk0). now apply in_left.
  - case_bool_decide.
    + reflexivity.
    + intros. rewrite <- smaller_bigger_is_td_unzip. reflexivity.
      now apply (fresh_key_below_correct_rank x i rank rk).
Qed.

Lemma rec_is_td (i rank : Z) (t : tree) (zt : is_zip t) (bt : is_bst t)
  (rankFromKey : (forall rk, in_tree i rk t -> rk = rank))
  : rec_insert i rank t = td_insert t rank i.
Proof.
  unfold td_insert. now rewrite <- rec_is_td_go.
Qed.

Lemma td_is_bu (i rank : Z) (t : tree) (zt : is_zip t) (bt : is_bst t)
  (rankFromKey : (forall rk, in_tree i rk t -> rk = rank))
  : bu_insert t rank i = td_insert t rank i.
Proof. now rewrite <- rec_is_bu, rec_is_td. Qed.
