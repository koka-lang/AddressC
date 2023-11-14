(* Copyright (c) 2023 Microsoft Research, Anton Lorenzen *)

From fip_iris Require Import lang tree mtr.

Local Set Default Proof Using "Type*".
Context `{!heapGS Σ}.

Fixpoint is_tree (t : tree) (v : val) : iProp Σ :=
  match t with
  | Leaf => ⌜v = NULL⌝
  | Node l x r => ∃ (p : loc) l' r', ⌜v =  #p⌝ ∗ p ↦∗ [ #1; l'; #x; r'] ∗ is_tree l l' ∗ is_tree r r'
  end.

#[export]
Instance is_tree_leaf_hint t :
HINT ε₁ ✱ [- ; ⌜t = Leaf⌝] ⊫ [id]; is_tree t NULL ✱ [⌜t = Leaf⌝].
Proof. iSteps. Qed.

(* Diaframe deconstructs arrays like p ↦∗ [ l'; #x; r'] into parts,
   so we can only check that the components are correct. *)
#[export]
Instance is_tree_node_hint (p : loc) (x : Z) (l_r l_l : val) t :
HINT ε₁ ✱ [ l r; (p +ₗ 0) ↦ #1 ∗ (p +ₗ 1) ↦ l_l ∗ (p +ₗ 2) ↦ #x ∗ (p +ₗ 3) ↦ l_r ∗ is_tree l l_l ∗ is_tree r l_r ∗ ⌜t = Node l x r⌝]
  ⊫ [id]; is_tree t #p ✱ [⌜t = Node l x r⌝].
Proof. unfold is_tree, array. simpl. iSteps. Qed.

Definition is_root_tree (t : root_tree) (v : val) : iProp Σ :=
  match t with
  | Root l x r => ∃ (p : loc) l' r', ⌜v =  #p⌝ ∗ p ↦∗ [ #1; l'; #x; r'] ∗ is_tree l l' ∗ is_tree r r'
  end.

#[export]
Instance is_root_tree_root_hint (p : loc) (x : Z) (l_r l_l : val) t :
HINT ε₁ ✱ [ l r; (p +ₗ 0) ↦ #1 ∗ (p +ₗ 1) ↦ l_l ∗ (p +ₗ 2) ↦ #x ∗ (p +ₗ 3) ↦ l_r ∗ is_tree l l_l ∗ is_tree r l_r ∗ ⌜t = Root l x r⌝]
  ⊫ [id]; is_root_tree t #p ✱ [⌜t = Root l x r⌝].
Proof. unfold is_root_tree, array. simpl. iSteps. Qed.

Fixpoint is_zipper (z : zipper) (v : val) : iProp Σ :=
  match z with
  | Done => ⌜v = NULL⌝
  | NodeL z x r => ∃ (p : loc) z' r', ⌜v =  #p⌝ ∗ p ↦∗ [ #1; z'; #x; r'] ∗ is_zipper z z' ∗ is_tree r r'
  | NodeR l x z => ∃ (p : loc) z' l', ⌜v =  #p⌝ ∗ p ↦∗ [ #2; l'; #x; z'] ∗ is_zipper z z' ∗ is_tree l l'
  end.

#[export]
Instance is_zipper_done_hint t :
HINT ε₁ ✱ [- ; ⌜t = Done⌝] ⊫ [id]; is_zipper t NULL ✱ [⌜t = Done⌝].
Proof. iSteps. Qed.

#[export]
Instance is_zipper_node_hint (p : loc) t :
HINT ε₁ ✱ [ (tag : Z) z (x : Z) t' l_l l_r; (p +ₗ 0) ↦ #tag ∗ (p +ₗ 1) ↦ l_l ∗ (p +ₗ 2) ↦ #x ∗ (p +ₗ 3) ↦ l_r ∗
  (if Z.eqb tag 1 then is_zipper z l_l ∗ is_tree t' l_r ∗ ⌜t = NodeL z x t'⌝
                  else is_tree t' l_l ∗ is_zipper z l_r ∗ ⌜t = NodeR t' x z⌝ ∗ ⌜tag = 2⌝)]
  ⊫ [id]; is_zipper t #p ✱ [(if Z.eqb tag 1 then ⌜t = NodeL z x t'⌝
                                            else ⌜t = NodeR t' x z⌝)].
Proof. iSteps as (? ? ? ? ? ?) "H1 H2 H3 H4 H5". destruct (x =? 1)%Z eqn:H6;
       iDecompose "H5"; unfold array; iSteps. Qed.

Notation "e1 '->tag'" :=
  (Load (BinOp OffsetOp e1%E (Val (LitV (LitInt (Z.of_nat 0))))))
  (at level 20) : expr_scope.

Notation "e1 '->left'" :=
  (Load (BinOp OffsetOp e1%E (Val (LitV (LitInt (Z.of_nat 1))))))
  (at level 20) : expr_scope.

Notation "e1 '->key'" :=
  (Load (BinOp OffsetOp e1%E (Val (LitV (LitInt (Z.of_nat 2))))))
  (at level 20) : expr_scope.

Notation "e1 '->right'" :=
  (Load (BinOp OffsetOp e1%E (Val (LitV (LitInt (Z.of_nat 3))))))
  (at level 20) : expr_scope.