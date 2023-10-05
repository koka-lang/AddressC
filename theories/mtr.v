(* Copyright (c) 2023 Microsoft Research, Anton Lorenzen, Wouter Swierstra *)

From fip_iris Require Import lang tree.

Create HintDb trees.

(* Recursive *)

Fixpoint smaller (i : Z) (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node l x r =>
    if bool_decide (i = x)%Z then
      l
    else if bool_decide (i < x)%Z then
      smaller i l
    else
      Node l x (smaller i r)
  end.

Fixpoint bigger (i : Z) (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node l x r =>
    if bool_decide (i = x)%Z then
      r
    else if bool_decide (i < x)%Z then
      Node (bigger i l) x r
    else
      bigger i r
  end.

Definition rec_insert_go (i : Z) (t : tree) : root_tree :=
  Root (smaller i t) i (bigger i t).

Definition rec_insert (i : Z) (t : tree) : tree :=
  to_tree (rec_insert_go i t).

Local Hint Unfold smaller bigger rec_insert rec_insert_go : trees.

(* Bottom-up *)

Fixpoint move_to_root (z : zipper) (t : root_tree) : root_tree :=
    match t with
    | Root l x r =>
      match z with
      | Done => Root l x r
      | NodeL zl zx zr => move_to_root zl (Root l x (Node r zx zr))
      | NodeR zl zx zr => move_to_root zr (Root (Node zl zx l) x r)
      end
    end.

Fixpoint bu_insert_go (i : Z) (z : zipper) (t : tree) : root_tree :=
    match t with
    | Leaf => move_to_root z (Root Leaf i Leaf)
    | Node l x r =>
      if bool_decide (i = x)%Z then
        move_to_root z (Root l i r)
      else if bool_decide (i < x)%Z then
        bu_insert_go i (NodeL z x r) l
      else
        bu_insert_go i (NodeR l x z) r
    end.

Definition bu_insert (i : Z) (t : tree) : tree :=
  to_tree (bu_insert_go i Done t).

Local Hint Unfold bu_insert bu_insert_go : trees.

(* Top-down *)

Fixpoint td_insert_go (i : Z) (lctx : ctx) (rctx : ctx) (t : tree) : tree :=
    match t with
    | Node l x r =>
      if bool_decide (x = i)%Z then
        Node (plug lctx l) i (plug rctx r)
      else if bool_decide (i < x)%Z then
        td_insert_go i lctx (comp rctx (Node0 Hole x r)) l
      else
        td_insert_go i (comp lctx (Node2 l x Hole)) rctx r
    | Leaf => Node (plug lctx Leaf) i (plug rctx Leaf)
    end.

Definition td_insert (i : Z) (t : tree) : tree :=
  td_insert_go i Hole Hole t.

Local Hint Unfold td_insert td_insert_go : trees.

(* Proof of equivalence *)

Definition rec_is_bu_go (i : Z) (t : tree) (z : zipper)
  : move_to_root z (rec_insert_go i t) = bu_insert_go i z t.
Proof.
  generalize z. autounfold with trees. induction t; intros; [ done | ].
  repeat case_bool_decide.
  - done.
  - now rewrite <- IHt1.
  - now rewrite <- IHt2.
Qed.

Definition rec_is_bu (i : Z) (t : tree) : rec_insert i t = bu_insert i t.
Proof. autounfold with trees. now rewrite <- rec_is_bu_go. Qed.

Definition rec_insert_go_ctx (i : Z) (t : tree) (lctx : ctx) (rctx : ctx) : tree :=
  Node (plug lctx (smaller i t)) i (plug rctx (bigger i t)).

Local Hint Unfold rec_insert_go_ctx : trees.

Definition rec_is_td_go (i : Z) (t : tree) : forall lctx rctx,
   rec_insert_go_ctx i t lctx rctx = td_insert_go i lctx rctx t.
Proof.
  autounfold with trees. induction t; intros; [ done | ].
  repeat case_bool_decide; try (exfalso; lia).
  - done.
  - rewrite <- IHt1. now rewrite comp_plug.
  - rewrite <- IHt2. now rewrite comp_plug.
Qed.

Definition rec_is_td (i : Z) (t : tree) : rec_insert i t = td_insert i t.
Proof. autounfold with trees. now rewrite <- rec_is_td_go. Qed.

Definition td_is_bu (i : Z) (t : tree) : bu_insert i t = td_insert i t.
Proof. now rewrite <- rec_is_bu, rec_is_td. Qed.

(* Properties of mtr trees *)

Inductive all (P : Z -> Type) : tree -> Type :=
| all_leaf : all P Leaf
| all_node : forall {l : tree} {x : Z} {r : tree},
             all P l -> P x -> all P r -> all P (Node l x r).

Local Hint Constructors all : trees.

Lemma all_impl {P Q : Z → Set} {t : tree} (H : all P t) (f : forall x : Z, P x → Q x) : all Q t.
Proof.
  induction t; [ now trivial with trees | ].
  inversion H; now auto with trees.
Qed.

Local Hint Resolve all_impl : trees.

Lemma access_all {P : Z -> Type} {k : Z} {t : tree} :
  all P t -> P k -> all P (rec_insert k t).
Proof.
intros H pk. induction t as [ | l IHl x r IHr]; inversion H.
- constructor; trivial.
- autounfold with trees. repeat case_bool_decide.
  + now subst.
  + apply IHl in X. inversion X; subst.
    constructor; try constructor; eauto with trees.
  + apply IHr in X1. inversion X1; subst.
    constructor; try constructor; eauto with trees.
Qed.

Lemma access_root (k : Z) (t : tree) :
  get_root (rec_insert_go k t) = k.
Proof.
  autounfold with trees. induction t as [ | l IHl x r IHr];
  [ reflexivity | ]. repeat case_bool_decide; simpl; lia.
Qed.

Inductive bst : tree -> Type :=
| bst_leaf : bst Leaf
| bst_node : forall {x : Z} {l r : tree},
    bst l -> all (fun y => Z.lt y x) l ->
    bst r -> all (fun y => Z.lt x y) r ->
    bst (Node l x r).

Local Hint Constructors bst : trees.

Lemma rec_insert_bst (t : tree) (k : Z) (bst_t : bst t)
  : bst (rec_insert k t).
Proof.
  autounfold with trees. induction t as [ | l IHl x r IHr].
  - now eauto with trees.
  - repeat case_bool_decide.
    + now subst.
    + inversion bst_t as [ | x' l' r' bstl bl bstr br]. subst.
      assert (all (λ y : Z, Z.lt y x) (to_tree (rec_insert_go k l))) by
         (apply (access_all bl); lia).
      apply IHl in bstl. inversion bstl. inversion H1. subst.
      repeat (constructor; auto with trees).
      apply (all_impl br). intros. lia.
    + inversion bst_t as [ | x' l' r' bstl bl bstr br]. subst.
      assert (all (λ y : Z, Z.lt x y) (to_tree (rec_insert_go k r))) by
        (apply (access_all br); lia).
      apply IHr in bstr. inversion bstr. inversion H1. subst.
      repeat (constructor; auto with trees).
      apply (all_impl bl). intros. lia.
Qed.

Inductive in_tree (x : Z) : tree -> Type :=
| in_root : forall {l r : tree}, in_tree x (Node l x r)
| in_left : forall {l r : tree} {y : Z}, in_tree x l -> in_tree x (Node l y r)
| in_right : forall {l r : tree} {y : Z}, in_tree x r -> in_tree x (Node l y r).

Local Hint Constructors in_tree : trees.

Lemma preserves_elems (t : tree) (y k : Z)
  : in_tree y t -> in_tree y (rec_insert k t).
Proof.
  autounfold with trees. induction t as [ | l IHl x r IHr]; intros H.
  - inversion H.
  - repeat case_bool_decide.
    + now subst.
    + inversion H; subst; simpl to_tree; auto with trees.
      apply IHl in H3. inversion H3; auto with trees.
    + inversion H; subst; simpl to_tree; auto with trees.
      apply IHr in H3. inversion H3; auto with trees.
Qed.
