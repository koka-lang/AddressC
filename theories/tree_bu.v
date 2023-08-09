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

#[export]
Instance is_tree_node_hint (p : loc) (x : Z) (l_r l_l : val) t :
HINT p ↦∗ [ #1; l_l; #x; l_r] ✱ [ l r ; is_tree l l_l ∗ is_tree r l_r ∗ ⌜t = Node l x r⌝]
  ⊫ [id]; is_tree t #p ✱ [⌜t = Node l x r⌝].
Proof. iSteps. Qed.

Definition is_root_tree (t : root_tree) (v : val) : iProp Σ :=
  match t with
  | Root l x r => ∃ (p : loc) l' r', ⌜v =  #p⌝ ∗ p ↦∗ [ #1; l'; #x; r'] ∗ is_tree l l' ∗ is_tree r r'
  end.

#[export]
Instance is_root_tree_root_hint (p : loc) (x : Z) (l_r l_l : val) t :
HINT p ↦∗ [ #1; l_l; #x; l_r] ✱ [ l r ; is_tree l l_l ∗ is_tree r l_r ∗ ⌜t = Root l x r⌝]
  ⊫ [id]; is_root_tree t #p ✱ [⌜t = Root l x r⌝].
Proof. iSteps. Qed.

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
Instance is_zipper_nodel_hint (p : loc) (x : Z) (l_l l_r : val) t :
HINT p ↦∗ [ #1; l_l; #x; l_r] ✱ [l r ; is_zipper l l_l ∗ is_tree r l_r ∗ ⌜t = NodeL l x r⌝]
  ⊫ [id]; is_zipper t #p ✱ [⌜t = NodeL l x r⌝].
Proof. iSteps. Qed.

#[export]
Instance is_zipper_noder_hint (p : loc) (x : Z) (l_l l_r : val) t :
HINT p ↦∗ [ #2; l_l; #x; l_r] ✱ [l r ; is_tree l l_l ∗ is_zipper r l_r ∗ ⌜t = NodeR l x r⌝]
  ⊫ [id]; is_zipper t #p ✱ [⌜t = NodeR l x r⌝].
Proof. iSteps. Qed.

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