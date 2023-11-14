(* Copyright (c) 2023 Microsoft Research, Anton Lorenzen *)

From fip_iris Require Import lang zip.
From Equations Require Import Equations.

Local Set Default Proof Using "Type*".
Context `{!heapGS Σ}.

(* Trees and contexts with ranks, similar to tree.v and tree_td.v *)

Fixpoint is_tree (t : tree) (v : val) : iProp Σ :=
  match t with
  | Leaf => ⌜v = NULL⌝
  | Node rk l x r => ∃ (p : loc) l' r', ⌜v =  #p⌝
    ∗ p ↦∗ [ #rk; l'; #x; r' ] ∗ is_tree l l' ∗ is_tree r r'
  end.

#[export]
Instance is_tree_leaf_hint t :
HINT ε₁ ✱ [- ; ⌜t = Leaf⌝] ⊫ [id]; is_tree t NULL ✱ [⌜t = Leaf⌝].
Proof. iSteps. Qed.

#[export]
Instance is_tree_node_hint (p : loc) (x rk : Z) (l_r l_l : val) t :
HINT p ↦∗ [ #rk; l_l; #x; l_r] ✱ [ l r ; is_tree l l_l ∗ is_tree r l_r ∗ ⌜t = Node rk l x r⌝]
  ⊫ [id]; is_tree t #p ✱ [⌜t = Node rk l x r⌝].
Proof. iSteps. Qed.

Definition harray (l : loc) (k : nat) (dq : dfrac) (vs : list val) : iProp Σ :=
  [∗ list] i ↦ v ∈ vs, ⌜i = k⌝ ∨ (l +ₗ i) ↦{dq} v.
  
Notation "l □↦∗ k dq vs" := (harray l k dq vs)
  (at level 20, k at level 1, dq custom dfrac  at level 1, format "l  □↦∗ k dq vs") : bi_scope.

Notation "□" := LitPoison.

Fixpoint is_ctx (z : ctx) (p : loc) (h : loc) : iProp Σ :=
  match z with
  | Hole => ⌜h = p⌝
  | Node0 rk l x r => ∃ (p' : loc) r', p ↦ #p' ∗ p' □↦∗ 1 [ #rk; #□; #x; r' ] ∗ is_ctx l (Loc.add p' 1%nat) h ∗ is_tree r r'
  | Node2 rk l x r => ∃ (p' : loc) l', p ↦ #p' ∗ p' □↦∗ 3 [ #rk; l'; #x; #□ ] ∗ is_ctx r (Loc.add p' 3%nat) h ∗ is_tree l l'
  end.

Definition is_ctx0 (z : ctx) (p' : loc) (h : loc) : iProp Σ :=
  match z with
  | Hole => ⌜false⌝
  | Node0 rk l x r => ∃ r', p' □↦∗ 1 [ #rk; #□; #x; r' ] ∗ is_ctx l (Loc.add p' 1%nat) h ∗ is_tree r r'
  | Node2 rk l x r => ∃ l', p' □↦∗ 3 [ #rk; l'; #x; #□ ] ∗ is_ctx r (Loc.add p' 3%nat) h ∗ is_tree l l'
  end.

#[export]
Instance is_ctx0_node0_hint (p : loc) (rk x : Z) (r' : val) (z : ctx) :
HINT (p +ₗ 2%nat) ↦∗ [ #x; r' ] ✱ [ r ; p ↦∗ [ #rk ] ∗ is_tree r r' ∗ ⌜z = Node0 rk Hole x r⌝]
  ⊫ [id]; is_ctx0 z p (p +ₗ 1%nat) ✱ [⌜z = Node0 rk Hole x r⌝].
Proof. iSteps. cbn. iSteps. Qed.

#[export]
Instance is_ctx0_node2_hint (p : loc) (rk x : Z) (l' : val) (z : ctx) :
HINT p ↦∗ [ #rk; l'; #x ] ✱ [ l ; is_tree l l' ∗ ⌜z = Node2 rk l x Hole⌝]
  ⊫ [id]; is_ctx0 z p (p +ₗ 3%nat) ✱ [⌜z = Node2 rk l x Hole⌝].
Proof. iSteps. cbn. iSteps. Qed.

#[export]
Instance is_ctx_hole_hint z p :
HINT ε₁ ✱ [- ; ⌜z = Hole⌝] ⊫ [id]; is_ctx z p p ✱ [⌜z = Hole⌝].
Proof. iSteps. Qed.

Lemma ctx_of_ctx0 (z : ctx) (p : loc) (h : loc) :
    (∃ (p' : loc), p ↦ #p' ∗ is_ctx0 z p' h) -∗ is_ctx z p h.
Proof.
  iIntros "[%p' [? Hz]]". iInduction z as [] "IH" forall (p h); iDecompose "Hz"; iSteps.
Qed.

Lemma tree_of_ctx (z : ctx) (t : tree) (zv : loc) (hv : loc) (tv : val) :
    is_ctx z zv hv ∗ hv ↦ tv ∗ is_tree t tv -∗ ∃ zv', zv ↦ zv' ∗ is_tree (plug z t) zv'.
Proof.
  iIntros "[Hz [Hhv Ht]]". iInduction z as [|rk z x r|rk l x z] "IH" forall (zv hv t).
  - iDecompose "Hz". iSteps.
  - iDecompose "Hz" as (? ?) "H1 H2 H3 H4". iExists #x. iFrame.
    iPoseProof ("IH" $! (Loc.add x 1) hv t with "H3 Hhv Ht") as "[%l' [H1' H2']]".
    iExists x, l', x0. unfold array, harray. iSteps.
  - iDecompose "Hz" as (? ?) "H1 H2 H3 H4". iExists #x0. iFrame.
    iPoseProof ("IH" $! (Loc.add x0 3) hv t with "H3 Hhv Ht") as "[%r' [H1' H2']]".
    iExists x0, x1, r'. unfold array, harray. iSteps.
Qed.

Lemma ctx0_of_ctx (z1 : ctx) (z2 : ctx) (zv1 : loc) (hv1 : loc) (zv2 : loc) (hv2 : loc) :
    is_ctx z1 zv1 hv1 ∗ hv1 ↦ #zv2 ∗ is_ctx0 z2 zv2 hv2 -∗ ∃ (zv1' : loc), zv1 ↦ #zv1' ∗ is_ctx0 (comp z1 z2) zv1' hv2.
Proof.
  iIntros "[Hz [Hhv Ht]]". iInduction z1 as [|rk z x r|rk l x z] "IH" forall (zv1 hv1 z2 zv2 hv2).
  - iDecompose "Hz". iExists zv2. iFrame.
  - iDecompose "Hz". iExists x. iFrame. iExists x0. iFrame.
    iApply (ctx_of_ctx0). iSteps. repeat rewrite (Loc.add_0). iSteps.
  - iDecompose "Hz". iExists x0. iFrame. iExists x1. iFrame.
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
  iStartProof. simpl. iStep. iPoseProof (tree_of_ctx z t zv hv) as "?". iSteps.
Qed.

#[export]
Instance tree_of_ctx_df_hint z t t' zv hv tv :
HINT is_ctx z zv hv ✱ [- ; hv ↦ tv ∗ is_tree t tv ∗ ⌜t' = plug z t⌝]
  ⊫ [id] zv' df; zv ↦{ df } zv' ✱ [ is_tree t' zv' ∗ ⌜t' = plug z t⌝].
Proof.
  iStartProof. simpl. iStep. iPoseProof (tree_of_ctx z t zv hv) as "?". iSteps.
Qed.

Opaque is_ctx.

Notation "e1 '->rank'" :=
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

Definition heap_unzip_td : val :=
  fun: (x, key, cur) {
    var: accl := &(x->left) in    (* ctx _ *)
    var: accr := &(x->right) in
    while: (cur != NULL) {    
      if: (cur->key < key) {
        ✲accl = cur;;             (* accl ++ ctx ... Node(rnk,l,x,_) *)
        repeat: { accl = &(cur->right);; cur = cur->right } 
        until: ((cur == NULL) || (cur->key >= key))
      } else {
        ✲accr = cur;;       
        repeat: { accr = &(cur->left);; cur = cur->left } 
        until: ((cur == NULL) || (cur->key < key))
      }
    };;
    ✲accl = NULL;;                  (* accl ++. Leaf *)
    ✲accr = NULL
  }.

Definition heap_td_insert : val :=
  fun: ( root, rank, key ) {
    var: cur := root in
    var: prev := &root in
    while: ( (cur != NULL) && heap_is_higher_rank (cur->rank) rank (cur->key) key ) {
      if: ( cur->key < key ) { prev = &(cur->right);; cur = cur->right }
      else {                   prev = &(cur->left) ;; cur = cur->left  }
    };;
    if: ( (cur != NULL) && (cur->key == key) ) {
      ret: root
    } else {
      var: x := AllocN #4 cur in
      x->rank = rank;;
      x->key = key;;
      ✲prev = x;;
      heap_unzip_td (&x) (&key) (&cur);;
      ret: root
    }
  }.

Lemma heap_right_correct (l r : tree) (rk k x : Z) (H : (x < k)%Z) (acc : ctx) (cur accl ref_k : loc) (tv : val) (accv h : loc) :
    {{{ cur ↦ tv ∗ is_tree (Node rk l x r) tv ∗ ref_k ↦ #k
      ∗ accl ↦ #h ∗ is_ctx acc accv h ∗ h ↦ tv }}}
        repeat: {
          #accl <- (✲#cur) +ₗ #3%nat;;
          #cur <- (✲#cur)〚3〛
        } until: ((✲#cur == NULL) || ((✲#cur)〚2〛>= (✲ #ref_k)))
    {{{ v, RET v; ∃ (h' : loc) tv', ⌜v = #()⌝ ∗
        cur ↦ tv' ∗ is_tree (td_right (Node rk l x r) k acc).1 tv' ∗ ref_k ↦ #k
      ∗ accl ↦ #h' ∗ h' ↦ tv' ∗ is_ctx (td_right (Node rk l x r) k acc).2 accv h' }}}.
Proof.
  iIntros (Φ). iIntros "[Hcur [Ht [Hk [Haccl [Hctx Hh]]]]]". iIntros "Hphi". 
  iDestruct "Ht" as (p' l' r') "[-> [Hp [Hl Hr]]]". wp_load.
  wp_store. wp_load. wp_load_offset. wp_store. wp_apply wp_wand_l.
  iSplitL "Hphi". iFrame. wp_apply (wp_while_inv
    (∃ t' acc' (h' : loc) curv,
            cur ↦ curv ∗ is_tree t' curv ∗ ref_k ↦ #k
            ∗ accl ↦ #h' ∗ h' ↦ curv ∗ is_ctx acc' accv h'
            ∗ ⌜td_right (Node rk l x r) k acc = td_right t' k acc'⌝)%I).
  - iModIntro. iIntros "H". iDestruct "H" as (t' acc' h' curv) "[Hcur [Ht' [? [Hlacc [Hh' [Hctx ->]]]]]]".
    wp_load. destruct t' as [|rk'' l'' x'' r''].
    + iDestruct "Ht'" as %->. wp_type.
    + iDestruct "Ht'" as (p l''' r''') "[-> [Hp [Hl Hr]]]".
      wp_heap. case_bool_decide.
      * wp_quit_loop. unfold td_right. case_bool_decide. iSteps. lia.
      * wp_enter_loop. wp_heap. iModIntro.
        iExists r'', (comp acc' (Node2 rk'' l'' x'' Hole)), _, r'''.
        iFrame. unfold array. iDecompose "Hp". iFrame. iSplit.
        { iApply (ctx_of_ctx _ _ _ h' p). iFrame.
          iExists l'''. unfold harray. iSteps. iAssumption. }
        { case_bool_decide. lia. done. }
  - iExists r, (comp acc (Node2 rk l x Hole)), (p' +ₗ 3%nat), r'.
    iFrame. unfold array. iDecompose "Hp". iFrame. iSplit.
    + iApply (ctx_of_ctx _ _ _ h p'). iFrame.
      iExists l'. unfold harray. iSteps. iAssumption.
    + case_bool_decide. lia. done.
Qed.

Global Instance heap_right_correct_instance (l r : tree) (rk k x : Z) (H : (x < k)%Z) (acc : ctx) (cur accl ref_k : loc) (tv : val) (accv h : loc) :
    SPEC {{ cur ↦ tv ∗ is_tree (Node rk l x r) tv ∗ ref_k ↦ #k
      ∗ accl ↦ #h ∗ is_ctx acc accv h ∗ h ↦ tv }}
        (repeat: {
          #accl <- (✲#cur) +ₗ #3%nat;;
          #cur <- (✲#cur)〚3〛
        } until: ((✲#cur == NULL) || ((✲#cur)〚2〛>= (✲ #ref_k))))%E
    {{ RET #(); ∃ (h' : loc) tv',
        cur ↦ tv' ∗ is_tree (td_right (Node rk l x r) k acc).1 tv' ∗ ref_k ↦ #k
      ∗ accl ↦ #h' ∗ h' ↦ tv' ∗ is_ctx (td_right (Node rk l x r) k acc).2 accv h' }}.
Proof. iStep. wp_apply (heap_right_correct with "[-]"). exact H. all: wp_type. Qed.

Lemma heap_left_correct (l r : tree) (rk k x : Z) (H : (x >= k)%Z) (acc : ctx) (cur accr ref_k : loc) (tv : val) (accv h : loc) :
    {{{ cur ↦ tv ∗ is_tree (Node rk l x r) tv ∗ ref_k ↦ #k
      ∗ accr ↦ #h ∗ is_ctx acc accv h ∗ h ↦ tv }}}
        repeat: {
          #accr <- (✲#cur) +ₗ #1%nat;;
          #cur <- (✲#cur)〚1〛
        } until: ((✲#cur == NULL) || ((✲#cur)〚2〛< (✲ #ref_k)))
    {{{ v, RET v; ∃ (h' : loc) tv', ⌜v = #()⌝ ∗
        cur ↦ tv' ∗ is_tree (td_left (Node rk l x r) k acc).1 tv' ∗ ref_k ↦ #k
      ∗ accr ↦ #h' ∗ h' ↦ tv' ∗ is_ctx (td_left (Node rk l x r) k acc).2 accv h' }}}.
Proof.
  iIntros (Φ). iIntros "[Hcur [Ht [Hk [Haccr [Hctx Hh]]]]]". iIntros "Hphi".
  iDestruct "Ht" as (p' l' r') "[-> [Hp [Hl Hr]]]". wp_load.
  wp_store. wp_load. wp_load_offset. wp_store. wp_apply wp_wand_l.
  iSplitL "Hphi". iFrame. wp_while
    (∃ t' acc' (h' : loc) curv,
            cur ↦ curv ∗ is_tree t' curv ∗ ref_k ↦ #k
            ∗ accr ↦ #h' ∗ h' ↦ curv ∗ is_ctx acc' accv h'
            ∗ ⌜td_left (Node rk l x r) k acc = td_left t' k acc'⌝)%I.
  - iModIntro. iIntros "H". iDestruct "H" as (t' acc' h' curv) "[Hcur [Ht' [? [Hlacc [Hh' [Hctx ->]]]]]]".
    wp_load. destruct t' as [|rk'' l'' x'' r''].
    + iDestruct "Ht'" as %->. wp_type.
    + iDestruct "Ht'" as (p l''' r''') "[-> [Hp [Hl Hr]]]".
      wp_heap. case_bool_decide.
      * wp_quit_loop. unfold td_left. case_bool_decide. iSteps. lia.
      * wp_enter_loop. wp_heap. iModIntro.
        iExists l'', (comp acc' (Node0 rk'' Hole x'' r'')), _, l'''.
        iFrame. unfold array. iDecompose "Hp". iFrame. iSplit.
        { iApply (ctx_of_ctx _ _ _ h' p). iFrame.
          iExists r'''. unfold harray. iSteps. iAssumption. }
        { case_bool_decide. lia. done. }
  - iExists l, (comp acc (Node0 rk Hole x r)), (p' +ₗ 1%nat), l'.
    iFrame. unfold array. iDecompose "Hp". iFrame. iSplit.
    + iApply (ctx_of_ctx _ _ _ h p'). iFrame.
      iExists r'. unfold harray. iSteps. iAssumption.
    + case_bool_decide. lia. done.
Qed.

Global Instance heap_left_correct_instance (t l r : tree) (rk k x : Z) (H : (x >= k)%Z) (acc : ctx) (cur accr ref_k : loc) (tv : val) (accv h : loc) :
    SPEC {{ cur ↦ tv ∗ is_tree (Node rk l x r) tv ∗ ref_k ↦ #k
      ∗ accr ↦ #h ∗ is_ctx acc accv h ∗ h ↦ tv }}
        (repeat: {
          #accr <- (✲#cur) +ₗ #1%nat;;
          #cur <- (✲#cur)〚1〛
        } until: ((✲#cur == NULL) || ((✲#cur)〚2〛< (✲ #ref_k))))%E
    {{ RET #(); ∃ (h' : loc) tv',
        cur ↦ tv' ∗ is_tree (td_left (Node rk l x r) k acc).1 tv' ∗ ref_k ↦ #k
      ∗ accr ↦ #h' ∗ h' ↦ tv' ∗ is_ctx (td_left (Node rk l x r) k acc).2 accv h' }}.
Proof. iStep. wp_apply (heap_left_correct with "[-]"). exact H. all: wp_type. Qed.

Lemma heap_unzip_correct (t : tree) (rk k : Z) (cur x px ref_k : loc) (tv : val) :
    {{{ cur ↦ tv ∗ is_tree t tv ∗ ref_k ↦ #k
      ∗ x ↦ #px ∗ px ↦∗ [ #rk; tv; #k; tv ] }}}
    heap_unzip_td #x #ref_k #cur
    {{{ v, RET v;
        is_tree (Node rk (td_unzip t k Hole Hole).1 k (td_unzip t k Hole Hole).2) #px }}}.
Proof.
  wp_begin "[Hcur [Ht [Hk [Hx Hpx]]]]". repeat wp_let.
  wp_load. wp_var lhole. wp_load. wp_var rhole. wp_while
    (∃ t' curv accl accr (lhole' rhole' : loc) lholev rholev,
      x ↦ #px ∗ (px +ₗ 0%nat) ↦ #rk ∗ (px +ₗ 2%nat) ↦ #k
      ∗ cur ↦ curv ∗ is_tree t' curv ∗ ref_k ↦ #k
      ∗ lhole ↦ #lhole' ∗ lhole' ↦ lholev ∗ is_ctx accl (px +ₗ 1%nat) lhole'
      ∗ rhole ↦ #rhole' ∗ rhole' ↦ rholev ∗ is_ctx accr (px +ₗ 3%nat) rhole'
      ∗ ⌜td_unzip t k Hole Hole = td_unzip t' k accl accr⌝)%I.
  - iModIntro. iIntros "H". iDestruct "H" as (t' curv accl accr lhole' rhole' lholev rholev) "[Hx [Hx0 [Hx2 [Hcur [Ht' [Hk [Hlhole [Hlhole' [Haccl [Hrhole [Hrhole' [Haccr ->]]]]]]]]]]]]".
    wp_load. destruct t' as [|rk'' l'' x'' r''].
    + iDestruct "Ht'" as %->. wp_type. unfold array. wp_type.
    + iDestruct "Ht'" as (pt lt rt) "[-> [Hpt [Hlt Hrt]]]". wp_pures.
      wp_enter_loop. wp_heap. case_bool_decide.
      { wp_pures. wp_load. wp_load. wp_store.
        wp_apply (heap_right_correct l'' r'' rk'' k x'' H accl with "[Hk Hcur Hpt Hlt Hrt Hlhole Haccl Hlhole']").
        { wp_type. }
        simp td_unzip. case_decide. wp_type. lia. }
      { wp_pures. wp_load. wp_load. wp_store.
        wp_apply (heap_left_correct l'' r'' rk'' k x'' H accr with "[Hk Hcur Hpt Hlt Hrt Hrhole Haccr Hrhole']").
        { wp_type. }
        simp td_unzip. case_decide. lia. wp_type. }
  - unfold array. wp_type.
Qed.

Lemma heap_td_insert_correct (k rank : Z) (tv : val) (t : tree) :
    {{{ is_tree t tv }}}
    heap_td_insert (ref tv) (ref #rank) (ref #k)
    {{{ v, RET v; is_tree (td_insert_go t rank k Hole) v }}}.
Proof.
  wp_begin "Ht"; root, ref_rank, ref_k. repeat wp_let.
  wp_load. wp_var cur. wp_var prev. wp_while
    (∃ t' curv acc (hole : loc),
      cur ↦ curv ∗ is_tree t' curv ∗ ref_rank ↦ #rank ∗ ref_k ↦ #k
      ∗ prev ↦ #hole ∗ hole ↦ curv ∗ is_ctx acc root hole
      ∗ ⌜td_insert_go t rank k Hole = td_insert_go t' rank k acc⌝)%I.
  - iModIntro. iIntros "H". iDestruct "H" as (t' curv acc hole) "[Hcur [Ht' [Hrank [Hk [Hprev [Hhole [Hacc ->]]]]]]]".
    wp_load. destruct t' as [|rk l xk r].
    + iDestruct "Ht'" as %->. wp_pures. wp_quit_loop.
      wp_pures. wp_load. wp_pures. wp_load. wp_alloc x' as "Hx'". { done. }
      wp_alloc x as "Hx". wp_heap.
      wp_apply (heap_unzip_correct Leaf rank k with "[Hcur Hx Hx' Hk]").
        { wp_type. }
      iIntros (v) "Ht". wp_heap.
      iPoseProof (tree_of_ctx acc _ root hole #x' with "[Hacc Hhole Ht]") as "[%t' [? Ht]]".
        { iFrame. }
      wp_heap. wp_type.
    + iDestruct "Ht'" as (p l' r') "[-> [Hp [Hl Hr]]]".
      wp_heap. wp_apply (heap_is_higher_rank_correct rk rank xk k). { done. }
      iIntros (v) "[%b [Hv Hb]]". unfold td_insert_go. destruct b;
      iDestruct "Hv" as %->; iDestruct "Hb" as %<-.
      * iRight. iSplit; first done. wp_heap.
        case_bool_decide; wp_heap; wp_type.
      * iLeft. iSplit; first done. wp_heap. case_bool_decide.
        { iPoseProof (tree_of_ctx acc (Node rk l k r) root hole #p with "[Hacc Hhole Hp Hl Hr]") as "[%t' [? Ht]]".
          { wp_type. } wp_heap. wp_type. }
        { wp_pures. wp_load. wp_alloc x' as "Hx'". { done. } wp_alloc x as "Hx". wp_heap.
          wp_apply (heap_unzip_correct (Node rk l xk r) rank k with "[Hcur Hp Hl Hr Hx Hx' Hk]").
            { wp_type. }
          iIntros (v) "Ht". wp_heap.
          iPoseProof (tree_of_ctx acc _ root hole #x' with "[Hacc Hhole Ht]") as "[%t' [? Ht]]".
            { iFrame. }
          wp_heap. iModIntro. case_bool_decide. { exfalso. apply H. now rewrite <- H0. }
          destruct (td_unzip (Node rk l xk r) k Hole Hole). wp_type. }
  - wp_type.
Qed.