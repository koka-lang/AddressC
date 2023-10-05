(* Copyright (c) 2023 Microsoft Research, Anton Lorenzen *)

From fip_iris Require Import lang tree mtr.

Local Set Default Proof Using "Type*".
Context `{!heapGS Σ}.

Fixpoint is_tree (t : tree) (v : val) : iProp Σ :=
  match t with
  | Leaf => ⌜v = NULL⌝
  | Node l x r => ∃ (p : loc) l' r', ⌜v = #p⌝
    ∗ p ↦∗ [ l'; #x; r'] ∗ is_tree l l' ∗ is_tree r r'
  end.

#[export]
Instance is_tree_leaf_hint t :
HINT ε₁ ✱ [- ; ⌜t = Leaf⌝] ⊫ [id]; is_tree t NULL ✱ [⌜t = Leaf⌝].
Proof. iSteps. Qed.

#[export]
Instance is_tree_node_hint (p : loc) (x : Z) (l_r l_l : val) t :
HINT p ↦∗ [ l_l; #x; l_r] ✱ [ l r ; is_tree l l_l ∗ is_tree r l_r ∗ ⌜t = Node l x r⌝]
  ⊫ [id]; is_tree t #p ✱ [⌜t = Node l x r⌝].
Proof. iSteps. Qed.

Definition is_root_tree (t : root_tree) (v : val) : iProp Σ :=
  match t with
  | Root l x r => ∃ (p : loc) l' r', ⌜v =  #p⌝ ∗ p ↦∗ [ l'; #x; r'] ∗ is_tree l l' ∗ is_tree r r'
  end.

#[export]
Instance is_root_tree_root_hint (p : loc) (x : Z) (l_r l_l : val) t :
HINT p ↦∗ [ l_l; #x; l_r] ✱ [ l r ; is_tree l l_l ∗ is_tree r l_r ∗ ⌜t = Root l x r⌝]
  ⊫ [id]; is_root_tree t #p ✱ [⌜t = Root l x r⌝].
Proof. iSteps. Qed.

Definition harray (l : loc) (k : nat) (dq : dfrac) (vs : list val) : iProp Σ :=
  [∗ list] i ↦ v ∈ vs, ⌜i = k⌝ ∨ (l +ₗ i) ↦{dq} v.
  
Notation "l □↦∗ k dq vs" := (harray l k dq vs)
  (at level 20, k at level 1, dq custom dfrac  at level 1, format "l  □↦∗ k dq vs") : bi_scope.

Notation "□" := LitPoison.

Fixpoint is_ctx (z : ctx) (p : loc) (h : loc) : iProp Σ :=
  match z with
  | Hole => ⌜h = p⌝
  | Node0 l x r => ∃ (p' : loc) r', p ↦ #p' ∗ p' □↦∗ 0 [ #□; #x; r' ] ∗ is_ctx l (Loc.add p' 0%nat) h ∗ is_tree r r'
  | Node2 l x r => ∃ (p' : loc) l', p ↦ #p' ∗ p' □↦∗ 2 [ l'; #x; #□ ] ∗ is_ctx r (Loc.add p' 2%nat) h ∗ is_tree l l'
  end.

Definition is_ctx0 (z : ctx) (p' : loc) (h : loc) : iProp Σ :=
  match z with
  | Hole => ⌜false⌝
  | Node0 l x r => ∃ r', p' □↦∗ 0 [ #□; #x; r' ] ∗ is_ctx l (Loc.add p' 0%nat) h ∗ is_tree r r'
  | Node2 l x r => ∃ l', p' □↦∗ 2 [ l'; #x; #□ ] ∗ is_ctx r (Loc.add p' 2%nat) h ∗ is_tree l l'
  end.

#[export]
Instance is_ctx0_node0_hint (p : loc) (x : Z) (r' : val) (z : ctx) :
HINT (p +ₗ 1%nat) ↦∗ [ #x; r' ] ✱ [ r ; is_tree r r' ∗ ⌜z = Node0 Hole x r⌝]
  ⊫ [id]; is_ctx0 z p (p +ₗ 0%nat) ✱ [⌜z = Node0 Hole x r⌝].
Proof. iSteps. cbn. iSteps. Qed.

#[export]
Instance is_ctx0_node2_hint (p : loc) (x : Z) (l' : val) (z : ctx) :
HINT p ↦∗ [ l'; #x ] ✱ [ l ; is_tree l l' ∗ ⌜z = Node2 l x Hole⌝]
  ⊫ [id]; is_ctx0 z p (p +ₗ 2%nat) ✱ [⌜z = Node2 l x Hole⌝].
Proof. iSteps. cbn. iSteps. Qed.

#[export]
Instance is_ctx_hole_hint z p :
HINT ε₁ ✱ [- ; ⌜z = Hole⌝] ⊫ [id]; is_ctx z p p ✱ [⌜z = Hole⌝].
Proof. iSteps. Qed.

Lemma ctx_of_ctx0 (z : ctx) (p : loc) (h : loc) :
    (∃ (p' : loc), p ↦ #p' ∗ is_ctx0 z p' h) -∗ is_ctx z p h.
Proof.
  iIntros "[%p' [Hp Hz]]". iInduction z as [|z x r|l x z] "IH" forall (p h).
  - iDecompose "Hz".
  - iDecompose "Hz". iExists p', x. iSteps.
  - iDecompose "Hz". iExists p', x0. iSteps.
Qed.

Lemma tree_of_ctx (z : ctx) (t : tree) (zv : loc) (hv : loc) (tv : val) :
    is_ctx z zv hv ∗ hv ↦ tv ∗ is_tree t tv -∗ ∃ zv', zv ↦ zv' ∗ is_tree (plug z t) zv'.
Proof.
  iIntros "[Hz [Hhv Ht]]". iInduction z as [|z x r|l x z] "IH" forall (zv hv t).
  - iDecompose "Hz". iExists tv. iFrame.
  - iDecompose "Hz". iExists #x. iFrame.
    iAssert (∃ l', (Loc.add x 0%nat) ↦ l' ∗ is_tree (plug z t) l')%I with "[H5 Ht Hhv]" as "[%l' [Hl' Hl]]".
      { iSteps. }
    iExists x, l', x0. unfold array, harray. iSteps.
  - iDecompose "Hz". iExists #x0. iFrame.
    iAssert (∃ r', (Loc.add x0 2%nat) ↦ r' ∗ is_tree (plug z t) r')%I with "[H5 Ht Hhv]" as "[%r' [Hr' Hr]]".
      { iSteps. }
    iExists x0, x1, r'. unfold array, harray. iSteps.
Qed.

Lemma ctx0_of_ctx (z1 : ctx) (z2 : ctx) (zv1 : loc) (hv1 : loc) (zv2 : loc) (hv2 : loc) :
    is_ctx z1 zv1 hv1 ∗ hv1 ↦ #zv2 ∗ is_ctx0 z2 zv2 hv2 -∗ ∃ (zv1' : loc), zv1 ↦ #zv1' ∗ is_ctx0 (comp z1 z2) zv1' hv2.
Proof.
  iIntros "[Hz [Hhv Ht]]". iInduction z1 as [|z x r|l x z] "IH" forall (zv1 hv1 z2 zv2 hv2).
  - iDecompose "Hz". iExists zv2. iFrame.
  - iDecompose "Hz". iExists x. iFrame. iExists x0. iFrame.
    iApply (ctx_of_ctx0). iSteps.
  - iDecompose "Hz". iExists x0. iFrame. iExists x1. iFrame.
    iApply (ctx_of_ctx0). iSteps.
Qed.

Lemma ctx_of_ctx (z1 : ctx) (z2 : ctx) (zv1 : loc) (hv1 : loc) (zv2 : loc) (hv2 : loc) :
    is_ctx z1 zv1 hv1 ∗ hv1 ↦ #zv2 ∗ is_ctx0 z2 zv2 hv2 -∗ is_ctx (comp z1 z2) zv1 hv2.
Proof.
  iIntros "[Hz [Hhv Ht]]". iApply (ctx_of_ctx0). iApply (ctx0_of_ctx). iSteps.
Qed.

#[export]
Instance ctx_of_ctx_hint z1 z2 z' zv1 hv1 (zv2 : loc) hv2 :
HINT is_ctx z1 zv1 hv1 ✱ [- ; hv1 ↦ #zv2 ∗ is_ctx0 z2 zv2 hv2 ∗ ⌜z' = (comp z1 z2)⌝]
  ⊫ [id]; is_ctx z' zv1 hv2 ✱ [⌜z' = (comp z1 z2)⌝] | 100.
Proof.
  iStep. iSplitL. iApply (ctx_of_ctx). iFrame. done.
Qed.

#[export]
Instance tree_of_ctx_hint z t t' zv hv tv :
HINT is_ctx z zv hv ✱ [- ; hv ↦ tv ∗ is_tree t tv ∗ ⌜t' = plug z t⌝]
  ⊫ [id] zv'; zv ↦ zv' ✱ [ is_tree t' zv' ∗ ⌜t' = plug z t⌝].
Proof.
  iStartProof. simpl. iStep. iPoseProof (tree_of_ctx) as "?". iSteps.
Qed.

Notation "e1 '->left'" :=
  (Load (BinOp OffsetOp e1%E (Val (LitV (LitInt (Z.of_nat 0))))))
  (at level 20) : expr_scope.

Notation "e1 '->key'" :=
  (Load (BinOp OffsetOp e1%E (Val (LitV (LitInt (Z.of_nat 1))))))
  (at level 20) : expr_scope.

Notation "e1 '->right'" :=
  (Load (BinOp OffsetOp e1%E (Val (LitV (LitInt (Z.of_nat 2))))))
  (at level 20) : expr_scope.

Opaque is_ctx.
