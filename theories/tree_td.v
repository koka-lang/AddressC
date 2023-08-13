(* Copyright (c) 2023 Microsoft Research, Anton Lorenzen *)

From fip_iris Require Import lang tree mtr.

Local Set Default Proof Using "Type*".
Context `{!heapGS Σ}.

Fixpoint is_tree (t : tree) (v : val) : iProp Σ :=
  match t with
  | Leaf => ⌜v = NULL⌝
  | Node l x r => ∃ (p : loc) l' r', ⌜v = #p⌝ ∗ p ↦∗ [ l'; #x; r'] ∗ is_tree l l' ∗ is_tree r r'
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

Fixpoint is_ctx0 (z : ctx0) (p : loc) (h : loc) : iProp Σ :=
  match z with
  | Node0 z x r => ∃ (z' : loc) r', p ↦∗ [ #z'; #x; r'] ∗ is_ctx0 z z' h ∗ is_tree r r'
  | Node2 l x z => ∃ (z' : loc) l', p ↦∗ [ l'; #x; #z'] ∗ is_ctx0 z z' h ∗ is_tree l l'
  | Node0' x r  => ∃ r', ⌜h = Loc.add p 0%nat⌝ ∗ p □↦∗ 0 [ #□; #x; r' ] ∗ is_tree r r'
  | Node2' l x  => ∃ l', ⌜h = Loc.add p 2%nat⌝ ∗ p □↦∗ 2 [ l'; #x; #□ ] ∗ is_tree l l'
  end.

#[export]
Instance is_ctx0_node0'_hint (p : loc) (x : Z) (r' : val) (z : ctx0) :
HINT (p +ₗ Z.succ 0%nat) ↦∗ [ #x; r' ] ✱ [ r ; is_tree r r' ∗ ⌜z = Node0' x r⌝]
  ⊫ [id]; is_ctx0 z p (p +ₗ 0%nat) ✱ [⌜z = Node0' x r⌝].
Proof. iSteps. cbn. iSteps. Qed.

#[export]
Instance is_ctx0_node2'_hint (p : loc) (x : Z) (l' : val) (z : ctx0) :
HINT p ↦∗ [ l'; #x ] ✱ [ l ; is_tree l l' ∗ ⌜z = Node2' l x⌝]
  ⊫ [id]; is_ctx0 z p (p +ₗ 2%nat) ✱ [⌜z = Node2' l x ⌝].
Proof. iSteps. cbn. iSteps. Qed.

Definition is_ctx (z : ctx) (p : loc) (h : loc) : iProp Σ :=
  match z with
  | Ctx0 z' => ∃ (zv : loc), p ↦ #zv ∗ is_ctx0 z' zv h
  | Hole   => ⌜h = p⌝
  end.

#[export]
Instance is_ctx_hole_hint z p :
HINT ε₁ ✱ [- ; ⌜z = Hole⌝] ⊫ [id]; is_ctx z p p ✱ [⌜z = Hole⌝].
Proof. iSteps. Qed.

Lemma tree_of_ctx0 (z : ctx0) (t : tree) (zv : loc) (hv : loc) (tv : val) :
    is_ctx0 z zv hv ∗ hv ↦ tv ∗ is_tree t tv -∗ is_tree (plug0 z t) #zv.
Proof.
  iIntros "[Hz [Hhv Ht]]". iInduction z as [z x r|l x z|x r|l x] "IH" forall (zv hv t).
  - iDestruct "Hz" as (z' r') "[Hp [Hz Hr]]". iSteps.
  - iDestruct "Hz" as (z' l') "[Hp [Hz Hl]]". iSteps.
    unseal_diaframe => /=. iExists hv. iFrame. unfold is_ctx0 at 2. unfold harray. iApply "Hz".
  - iDestruct "Hz" as (r') "[Hh [Hp Hr]]". 
    iAssert ((zv +ₗ 0) ↦ tv)%I with "[Hh Hhv]" as "Hhv".
      { iDestruct "Hh" as %->. done. }
    iAssert (zv ↦∗ [ tv; #x; r'])%I with "[Hp Hhv]" as "Hp'".
      { unfold array, harray. iSteps. }
    iSteps.
  - iDestruct "Hz" as (l') "[Hh [Hp Hl]]".
    iAssert ((zv +ₗ 2) ↦ tv)%I with "[Hh Hhv]" as "Hhv".
      { iDestruct "Hh" as %->. done. }
    iAssert (zv ↦∗ [ l'; #x; tv ])%I with "[Hp Hhv]" as "Hp'".
      { unfold array, harray. iSteps. }
    iSteps.
Qed.

#[export]
Instance tree_of_ctx0_hint z t t' zv hv tv :
HINT is_ctx0 z zv hv ✱ [- ; hv ↦ tv ∗ is_tree t tv ∗ ⌜t' = plug0 z t⌝]
  ⊫ [id]; is_tree (plug0 z t) #zv ✱ [⌜t' = plug0 z t⌝].
Proof.
  iSteps. iSplitL. iApply (tree_of_ctx0). iFrame. done.
Qed.

Lemma tree_of_ctx (z : ctx) (t : tree) (zv : loc) (hv : loc) (tv : val) :
    is_ctx z zv hv ∗ hv ↦ tv ∗ is_tree t tv -∗ ∃ zv', zv ↦ zv' ∗ is_tree (plug z t) zv'.
Proof.
  iIntros "[Hz [Hhv Ht]]". iInduction z as [z|] "IH" forall (zv hv t); iStopProof; iSteps.
Qed.

Lemma ctx0_of_ctx0 (z1 : ctx0) (z2 : ctx0) (zv1 : loc) (hv1 : loc) (zv2 : loc) (hv2 : loc) :
    is_ctx0 z1 zv1 hv1 ∗ hv1 ↦ #zv2 ∗ is_ctx0 z2 zv2 hv2 -∗ is_ctx0 (comp0 z1 z2) zv1 hv2.
Proof.
  iIntros "[Hz [Hhv Ht]]". iInduction z1 as [z x r|l x z|x r|l x] "IH" forall (zv1 hv1 z2 zv2 hv2).
  - iDestruct "Hz" as (z' r') "[Hp [Hz Hr]]".
    iExists z', r'. iSteps.
  - iDestruct "Hz" as (z' l') "[Hp [Hz Hl]]".
    iExists z', l'. iSteps.
  - iDestruct "Hz" as (r') "[Hh [Hp Hr]]".
    iAssert ((zv1 +ₗ 0) ↦ #zv2)%I with "[Hh Hhv]" as "Hhv".
      { iDestruct "Hh" as %->. done. }
    iAssert (zv1 ↦∗ [ #zv2; #x; r' ])%I with "[Hp Hhv]" as "Hp'".
      { unfold array, harray. iSteps. }
    iExists zv2, r'. iSteps.
  - iDestruct "Hz" as (l') "[Hh [Hp Hl]]".
    iAssert ((zv1 +ₗ 2) ↦ #zv2)%I with "[Hh Hhv]" as "Hhv".
      { iDestruct "Hh" as %->. done. }
    iAssert (zv1 ↦∗ [ l'; #x; #zv2 ])%I with "[Hp Hhv]" as "Hp'".
      { unfold array, harray. iSteps. }
    iExists zv2, l'. iSteps.
Qed.

Lemma ctx0_of_ctx (z1 : ctx) (z2 : ctx0) (zv1 : loc) (hv1 : loc) (zv2 : loc) (hv2 : loc) :
    is_ctx z1 zv1 hv1 ∗ hv1 ↦ #zv2 ∗ is_ctx0 z2 zv2 hv2 -∗ ∃ (zv1' : loc), zv1 ↦ #zv1' ∗ is_ctx0 (comp' z1 z2) zv1' hv2.
Proof.
  iIntros "[Hz [Hhv Ht]]". iInduction z1 as [z|] "IH" forall (zv1 hv1 z2 zv2 hv2).
  - iSteps. iApply (ctx0_of_ctx0). iSteps.
  - iDestruct "Hz" as %->. iSteps.
Qed.

Lemma ctx_of_ctx (z1 : ctx) (z2 : ctx0) (zv1 : loc) (hv1 : loc) (zv2 : loc) (hv2 : loc) :
    is_ctx z1 zv1 hv1 ∗ hv1 ↦ #zv2 ∗ is_ctx0 z2 zv2 hv2 -∗ is_ctx (comp z1 z2) zv1 hv2.
Proof.
  iPoseProof (ctx0_of_ctx z1 z2) as "H". iSteps.
Qed.

#[export]
Instance ctx_of_ctx_hint z1 z2 z' zv1 hv1 (zv2 : loc) hv2 :
HINT is_ctx z1 zv1 hv1 ✱ [- ; hv1 ↦ #zv2 ∗ is_ctx0 z2 zv2 hv2 ∗ ⌜z' = (comp z1 z2)⌝]
  ⊫ [id]; is_ctx z' zv1 hv2 ✱ [⌜z' = (comp z1 z2)⌝] | 100.
Proof.
  iStep. iSplitL. iApply (ctx0_of_ctx). iFrame. done.
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
