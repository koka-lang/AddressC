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

(* Diaframe deconstructs arrays like p ↦∗ [ l'; #x; r'] into parts,
   so we can only check that the components are correct. *)
#[export]
Instance is_tree_node_hint (p : loc) (x : Z) (l_r l_l : val) t :
HINT ε₁ ✱ [ l r ; (p +ₗ 0) ↦ l_l ∗ (p +ₗ 1) ↦ #x ∗ (p +ₗ 2) ↦ l_r ∗ is_tree l l_l ∗ is_tree r l_r ∗ ⌜t = Node l x r⌝]
  ⊫ [id]; is_tree t #p ✱ [⌜t = Node l x r⌝].
Proof. iSteps. Qed.

(* We want to figure out if a tree is a Leaf or a Node from the "t != NULL" check.
   To achieve this, Ike Mulder wrote this typeclass inference code. *)
Definition is_tree_value_at (t' : tree) (treev : val) : Prop :=
  match t' with
  | Leaf => treev = NULL
  | Node l x r => ∃ (p : loc),
      treev = #p
  end.

#[export]
Instance is_tred_none t : MergablePersist (is_tree t NULL) (fun p Pin Pout =>
  TCAnd (TCEq Pin (empty_hyp_first))
        (TCEq Pout (bi_pure (t= Leaf)))) | 5.
Proof. unfold MergablePersist.
  move => p Pin Pout [-> ->].
  destruct t; iSteps. Qed. 

#[export]
Instance is_tred_always t tv : MergablePersist (is_tree t tv) (fun p Pin Pout =>
    TCAnd (TCEq Pin (empty_hyp_first))
          (TCEq Pout (bi_pure (is_tree_value_at t tv)))) | 50.
Proof. unfold MergablePersist. move => p Pin Pout [-> ->].
  destruct t; iSteps. Qed.

Lemma simplifytreenotnil t tv : 
  is_tree_value_at t tv ->
  SimplifyPureHyp (tv ≠ NULL) (exists (l : loc), tv = #l /\ exists l x r, t = Node l x r).
Proof. unfold SolveSepSideCondition, SimplifyPureHyp. destruct t; naive_solver. Qed.

#[export]
Hint Extern 4 (SimplifyPureHyp (_ ≠ NULL) _) => 
  eapply simplifytreenotnil; eauto : typeclass_instances.

Definition is_root_tree (t : root_tree) (v : val) : iProp Σ :=
  match t with
  | Root l x r => ∃ (p : loc) l' r', ⌜v =  #p⌝ ∗ p ↦∗ [ l'; #x; r'] ∗ is_tree l l' ∗ is_tree r r'
  end.

#[export]
Instance is_root_tree_root_hint (p : loc) (x : Z) (l_r l_l : val) t :
HINT ε₁ ✱ [ l r ; (p +ₗ 0) ↦ l_l ∗ (p +ₗ 1) ↦ #x ∗ (p +ₗ 2) ↦ l_r ∗ is_tree l l_l ∗ is_tree r l_r ∗ ⌜t = Root l x r⌝]
  ⊫ [id]; is_root_tree t #p ✱ [⌜t = Root l x r⌝].
Proof. unfold is_root_tree, array. simpl. iSteps. Qed.

Definition harray (l : loc) (k : nat) (dq : dfrac) (vs : list val) : iProp Σ :=
  [∗ list] i ↦ v ∈ vs, ⌜i = k⌝ ∨ (l +ₗ i) ↦{dq} v.
  
Notation "l □↦∗ k dq vs" := (harray l k dq vs)
  (at level 20, k at level 1, dq custom dfrac  at level 1, format "l  □↦∗ k dq vs") : bi_scope.

Notation "□" := LitPoison.

Fixpoint is_ctx (z : ctx) (p : loc) (h : loc) : iProp Σ :=
  match z with
  | Hole => ⌜h = p⌝
  | Node0 l x r => ∃ (p' : loc) r', p ↦ #p' ∗ p' □↦∗ 0 [ #□; #x; r' ] ∗ is_ctx l (p' +ₗ 0) h ∗ is_tree r r'
  | Node2 l x r => ∃ (p' : loc) l', p ↦ #p' ∗ p' □↦∗ 2 [ l'; #x; #□ ] ∗ is_ctx r (p' +ₗ 2) h ∗ is_tree l l'
  end.

Definition is_ctx0 (z : ctx) (p' : loc) (h : loc) : iProp Σ :=
  match z with
  | Hole => ⌜false⌝
  | Node0 l x r => ∃ r', p' □↦∗ 0 [ #□; #x; r' ] ∗ is_ctx l (Loc.add p' 0%nat) h ∗ is_tree r r'
  | Node2 l x r => ∃ l', p' □↦∗ 2 [ l'; #x; #□ ] ∗ is_ctx r (Loc.add p' 2%nat) h ∗ is_tree l l'
  end.

#[export]
Instance is_ctx0_node0_hint (p : loc) (x : Z) (r' : val) (z : ctx) :
HINT ε₁ ✱ [ r ; (p +ₗ 1%nat) ↦ #x ∗ (p +ₗ 2%nat) ↦ r' ∗ is_tree r r' ∗ ⌜z = Node0 Hole x r⌝]
  ⊫ [id]; is_ctx0 z p (p +ₗ 0%nat) ✱ [⌜z = Node0 Hole x r⌝].
Proof. iSteps. cbn. iSteps. Qed.

#[export]
Instance is_ctx0_node2_hint (p : loc) (x : Z) (l' : val) (z : ctx) :
HINT ε₁ ✱ [ l ; (p +ₗ 0%nat) ↦ l' ∗ (p +ₗ 1%nat) ↦ #x ∗ is_tree l l' ∗ ⌜z = Node2 l x Hole⌝]
  ⊫ [id]; is_ctx0 z p (p +ₗ 2%nat) ✱ [⌜z = Node2 l x Hole⌝].
Proof. iSteps. unfold array, harray. iSteps. Qed.

#[export]
Instance is_ctx_hole_hint z p :
HINT ε₁ ✱ [- ; ⌜z = Hole⌝] ⊫ [id]; is_ctx z p p ✱ [⌜z = Hole⌝].
Proof. iSteps. Qed.

Lemma ctx_of_ctx0 (z : ctx) (p : loc) (h : loc) :
    (∃ (p' : loc), p ↦ #p' ∗ is_ctx0 z p' h) -∗ is_ctx z p h.
Proof.
  iIntros "[%p' [? Hz]]". iInduction z as [] "" forall (p h); iDecompose "Hz"; iSteps.
Qed.

Lemma tree_of_ctx (z : ctx) (t : tree) (zv : loc) (hv : loc) (tv : val) :
    is_ctx z zv hv ∗ hv ↦ tv ∗ is_tree t tv -∗ ∃ zv', zv ↦ zv' ∗ is_tree (plug z t) zv'.
Proof.
  iIntros "[Hz [Hhv Ht]]". iInduction z as [|z x r|l x z] "IH" forall (zv hv t).
  - iDecompose "Hz". iSteps.
  - iDecompose "Hz" as (? ? ?) "H1 H2 H3 H4". iExists #x. iSteps.
    iPoseProof ("IH" $! (Loc.add x 0) hv t with "H3 Hhv Ht") as "[%l' [H1' H2']]".
    iExists l', x0. unfold array, harray. iSteps.
  - iDecompose "Hz" as (? ? ?) "H1 H2 H3 H4". iExists #x0. iSteps.
    iPoseProof ("IH" $! (Loc.add x0 2) hv t with "H3 Hhv Ht") as "[%r' [H1' H2']]".
    iExists x1, r'. unfold array, harray. iSteps.
Qed.

Lemma ctx0_of_ctx (z1 : ctx) (z2 : ctx) (zv1 : loc) (hv1 : loc) (zv2 : loc) (hv2 : loc) :
    is_ctx z1 zv1 hv1 ∗ hv1 ↦ #zv2 ∗ is_ctx0 z2 zv2 hv2 -∗ ∃ (zv1' : loc), zv1 ↦ #zv1' ∗ is_ctx0 (comp z1 z2) zv1' hv2.
Proof.
  iIntros "[Hz [Hhv Ht]]". iInduction z1 as [|z x r|l x z] "IH" forall (zv1 hv1 z2 zv2 hv2).
  - iDecompose "Hz". iExists zv2. iFrame.
  - iDecompose "Hz". iExists x. iFrame.
    iApply (ctx_of_ctx0). iSteps. repeat rewrite (Loc.add_0). iSteps.
  - iDecompose "Hz". iExists x0. iFrame.
    iApply (ctx_of_ctx0). iSteps. repeat rewrite (Loc.add_0). iSteps.
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
  iSteps. iPoseProof (tree_of_ctx z t zv hv) as "?". iSteps.
Qed.

#[export]
Instance tree_of_ctx_df_hint z t t' zv hv tv :
HINT is_ctx z zv hv ✱ [- ; hv ↦ tv ∗ is_tree t tv ∗ ⌜t' = plug z t⌝]
  ⊫ [id] zv' df; zv ↦{ df } zv' ✱ [ is_tree t' zv' ∗ ⌜t' = plug z t⌝].
Proof.
  iSteps. iPoseProof (tree_of_ctx z t zv hv) as "?". iSteps.
Qed.

Notation "e1 '->left'" :=
  (Load (BinOp OffsetOp e1%E (Val (LitV (LitInt (Z.of_nat 0))))))
  (at level 20) : expr_scope.

Notation "e1 '->key'" :=
  (Load (BinOp OffsetOp e1%E (Val (LitV (LitInt (Z.of_nat 1))))))
  (at level 20) : expr_scope.

Notation "e1 '->item'" :=
  (Load (BinOp OffsetOp e1%E (Val (LitV (LitInt (Z.of_nat 1))))))
  (at level 20) : expr_scope.

Notation "e1 '->right'" :=
  (Load (BinOp OffsetOp e1%E (Val (LitV (LitInt (Z.of_nat 2))))))
  (at level 20) : expr_scope.

Opaque is_ctx.
