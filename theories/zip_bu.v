(* Copyright (c) 2023 Microsoft Research, Anton Lorenzen *)

From fip_iris Require Import lang zip.

Fixpoint is_tree `{!heapGS Σ}  (t : tree) (v : val) : iProp Σ :=
  match t with
  | Leaf => ⌜v = NULL⌝
  | Node rk l x r => ∃ (p : loc) l' r', ⌜v =  #p⌝
    ∗ p ↦∗ [ #1; #rk; l'; #x; r'] ∗ is_tree l l' ∗ is_tree r r'
  end.

Section proof.

Local Set Default Proof Using "Type*".
Context `{!heapGS Σ}.

#[export]
Instance is_tree_leaf_hint t :
HINT ε₁ ✱ [- ; ⌜t = Leaf⌝] ⊫ [id]; is_tree t NULL ✱ [⌜t = Leaf⌝].
Proof. iSteps. Qed.

#[export]
Instance is_tree_node_hint (p : loc) (rk x : Z) (l_r l_l : val) t :
HINT ε₁ ✱ [ l r; (p +ₗ 0) ↦ #1 ∗ (p +ₗ 1) ↦ #rk ∗ (p +ₗ 2) ↦ l_l ∗ (p +ₗ 3) ↦ #x ∗ (p +ₗ 4) ↦ l_r ∗ is_tree l l_l ∗ is_tree r l_r ∗ ⌜t = Node rk l x r⌝]
  ⊫ [id]; is_tree t #p ✱ [⌜t = Node rk l x r⌝].
Proof. unfold is_tree, array. simpl. iSteps. Qed.

Fixpoint is_zipper `{!heapGS Σ}  (z : zipper) (v : val) : iProp Σ :=
  match z with
  | Done => ⌜v = NULL⌝
  | NodeL rk z x r => ∃ (p : loc) z' r', ⌜v =  #p⌝
    ∗ p ↦∗ [ #1; #rk; z'; #x; r' ] ∗ is_zipper z z' ∗ is_tree r r'
  | NodeR rk l x z => ∃ (p : loc) z' l', ⌜v =  #p⌝
    ∗ p ↦∗ [ #2; #rk; l'; #x; z' ] ∗ is_zipper z z' ∗ is_tree l l'
  end.

#[export]
Instance is_zipper_done_hint t :
HINT ε₁ ✱ [- ; ⌜t = Done⌝] ⊫ [id]; is_zipper t NULL ✱ [⌜t = Done⌝].
Proof. iSteps. Qed.

#[export]
Instance is_zipper_node_hint (p : loc) t :
HINT ε₁ ✱ [ (tag : Z) z (x rk : Z) t' l_l l_r; (p +ₗ 0) ↦ #tag ∗ (p +ₗ 1) ↦ #rk ∗(p +ₗ 2) ↦ l_l ∗ (p +ₗ 3) ↦ #x ∗ (p +ₗ 4) ↦ l_r ∗
  (if Z.eqb tag 1 then is_zipper z l_l ∗ is_tree t' l_r ∗ ⌜t = NodeL rk z x t'⌝
                  else is_tree t' l_l ∗ is_zipper z l_r ∗ ⌜t = NodeR rk t' x z⌝ ∗ ⌜tag = 2⌝)]
  ⊫ [id]; is_zipper t #p ✱ [(if Z.eqb tag 1 then ⌜t = NodeL rk z x t'⌝
                                            else ⌜t = NodeR rk t' x z⌝)].
Proof. iSteps as (? ? ? ? ? ? ?) "H1 H2 H3 H4 H5 H6". destruct (x =? 1)%Z eqn:H7;
       iDecompose "H6"; unfold array; iSteps. Qed.

Notation "e1 '->tag'" :=
  (Load (BinOp OffsetOp e1%E (Val (LitV (LitInt (Z.of_nat 0))))))
  (at level 20) : expr_scope.

Notation "e1 '->rank'" :=
  (Load (BinOp OffsetOp e1%E (Val (LitV (LitInt (Z.of_nat 1))))))
  (at level 20) : expr_scope.

Notation "e1 '->left'" :=
  (Load (BinOp OffsetOp e1%E (Val (LitV (LitInt (Z.of_nat 2))))))
  (at level 20) : expr_scope.

Notation "e1 '->key'" :=
  (Load (BinOp OffsetOp e1%E (Val (LitV (LitInt (Z.of_nat 3))))))
  (at level 20) : expr_scope.

Notation "e1 '->right'" :=
  (Load (BinOp OffsetOp e1%E (Val (LitV (LitInt (Z.of_nat 4))))))
  (at level 20) : expr_scope.

Definition heap_rebuild : val :=
  fun: ( zipper', tree' ) {
    while: ( true ) {
      if: ( zipper' == NULL ) {
        break
      } else {
        if: (zipper'->tag == #1) {
          var: tmp := zipper'->left in
          zipper'->left = tree';;
          tree' = zipper';;
          zipper' = tmp
        } else {
          var: tmp := zipper'->right in
          zipper'->tag = #1;;
          zipper'->right = tree';;
          tree' = zipper';;
          zipper' = tmp
        }
      }
    };;
    ret: tree'
  }.

Definition heap_unzip : val :=
  fun: ( tree', k ) {
    var: zs := NULL in
    var: zb := NULL in
    while: ( true ) {
      if: (tree' == NULL) {
        break
      } else {
        if: (tree'->key < k) {
          var: tmp := tree'->right in
          tree'->tag = #2;;
          tree'->right = zs;;
          zs = tree';;
          tree' = tmp
        } else {
          var: tmp := tree'->left in
          tree'->left = zb;;
          zb = tree';;
          tree' = tmp
        }
      }
    };;
    ret: Pair (heap_rebuild (&zs) (ref NULL)) (heap_rebuild (&zb) (ref NULL))
  }.

Definition heap_insert : val :=
  fun: ( tree', rank, k, acc ) {
    while: ( true ) {
      if: (tree' == NULL) {
        tree' = AllocN #5 NULL;;
        tree'->tag = #1;;
        tree'->rank = rank;;
        tree'->key = k;;
        break
      } else {
        if: ( heap_is_higher_rank (tree'->rank) rank (tree'->key) k ) {
          if: (tree'->key < k) {
            var: tmp := tree'->right in
            tree'->tag = #2;;
            tree'->right = acc;;
            acc = tree';;
            tree' = tmp
          } else {
            var: tmp := tree'->left in
            tree'->left = acc;;
            acc = tree';;
            tree' = tmp
          }
        } else {
          if: (tree'->key == k) {
            break
          } else {
            var: tmp := heap_unzip (ref tree') (ref k) in
            tree' = AllocN #5 NULL;;
            tree'->tag = #1;;
            tree'->rank = rank;;
            tree'->left = Fst tmp;;
            tree'->key = k;;
            tree'->right = Snd tmp;;
            break
          }
        }
      }
    };;
    ret: heap_rebuild (&acc) (&tree')
  }.

Lemma heap_rebuild_correct (z : zipper) (t : tree) (zv tv : val) (zipper tree : loc) :
    {{{ zipper ↦ zv ∗ is_zipper z zv ∗ tree ↦ tv ∗ is_tree t tv }}}
    heap_rebuild #zipper #tree
    {{{ v, RET v; is_tree (rebuild z t) v }}}.
Proof.
  wp_begin "[Hz Ht]". wp_while_true "H"
    (∃ t' treev, tree ↦ treev ∗ is_tree t' treev ∗ ⌜rebuild z t = t'⌝)%I
    (∃ t' z' treev zipperv,
            tree ↦ treev ∗ is_tree t' treev
            ∗ zipper ↦ zipperv ∗ is_zipper z' zipperv
            ∗ ⌜rebuild z t = rebuild z' t'⌝)%I.
  - iDecompose "H". now wp_heap.
  - iDestruct "H" as (? ? ? ?) "[? [? [? [Hz ->]]]]".
    destruct z'; iDecompose "Hz"; wp_type.
  - wp_type.
Qed.

Lemma heap_unzip_correct (t : tree) (k : Z) (tv : val) (tree ref_k : loc) :
    {{{ tree ↦ tv ∗ is_tree t tv ∗ ref_k ↦ #k }}}
    heap_unzip #tree #ref_k
    {{{ v, RET v; ∃ v1 v2, ⌜v = PairV v1 v2⌝
        ∗ is_tree (bu_unzip t k Done Done).1 v1 
        ∗ is_tree (bu_unzip t k Done Done).2 v2 }}}.
Proof.
  wp_begin "[Htree [Ht Hk]]". wp_let. wp_var s. wp_var b. wp_while_true "H"
    (∃ zs' zb' zsv zbv,
              s ↦ zsv ∗ is_zipper zs' zsv
            ∗ b ↦ zbv ∗ is_zipper zb' zbv
            ∗ ⌜bu_unzip t k Done Done = (rebuild zs' Leaf, rebuild zb' Leaf)⌝)%I
    (∃ t' zs' zb' treev zsv zbv,
            tree ↦ treev ∗ is_tree t' treev ∗ ref_k ↦ #k
            ∗ s ↦ zsv ∗ is_zipper zs' zsv
            ∗ b ↦ zbv ∗ is_zipper zb' zbv
            ∗ ⌜bu_unzip t k Done Done = bu_unzip t' k zs' zb'⌝)%I.
  - iDestruct "H" as (zs' zb' ? ?) "[Hs [Hzs [Hb [Hzb ->]]]]".
    wp_pures. wp_alloc H as "H".
    wp_apply (heap_rebuild_correct zb' Leaf with "[Hzb Hb H]"). { wp_type. }
    iIntros. wp_alloc H' as "H".
    wp_apply (heap_rebuild_correct zs' Leaf with "[Hzs Hs H]"). { wp_type. }
    wp_type.
  - iDestruct "H" as (t' ? ? ? ? ?) "[? [Ht' [? [? [? [? [? ->]]]]]]]".
    unfold bu_unzip. destruct t'; iDecompose "Ht'"; wp_type.
  - wp_type.
Qed.

Lemma heap_insert_correct (tv : val) (t : tree) (rank : Z) (k : Z)
  (zv : val) (z : zipper) :
    {{{ is_tree t tv ∗ is_zipper z zv }}}
    heap_insert (ref tv) (ref #rank) (ref #k) (ref zv)
    {{{ v, RET v; is_tree (bu_insert_go t rank k z) v }}}.
Proof.
  wp_begin "[Ht Hz]"; tree, ref_rank, ref_k, acc. wp_while_true "H"
    (∃ t' z' treev accv,
            tree ↦ treev ∗ is_tree t' treev ∗ ref_rank ↦ #rank ∗ ref_k ↦ #k
            ∗ acc ↦ accv ∗ is_zipper z' accv
            ∗ ⌜bu_insert_go t rank k z = rebuild z' t'⌝)%I
    (∃ t' z' treev accv,
            tree ↦ treev ∗ is_tree t' treev ∗ ref_rank ↦ #rank ∗ ref_k ↦ #k
            ∗ acc ↦ accv ∗ is_zipper z' accv
            ∗ ⌜bu_insert_go t rank k z = bu_insert_go t' rank k z'⌝)%I.
  - iDestruct "H" as (t' z' ? ?) "[? [? [? [? [? [? ->]]]]]]". wp_heap.
    wp_apply (heap_rebuild_correct z' t' with "[-]"). { wp_type. }
    wp_type.
  - iDestruct "H" as (t' z' ? ?) "[? [Ht [? [? [? [Hz ->]]]]]]".
    destruct t' as [|rk l x r].
    + iDecompose "Ht". wp_type.
    + iDestruct "Ht" as (p l' r') "[-> [Hp [Hl Hr]]]". wp_heap.
      wp_apply (heap_is_higher_rank_correct rk rank x k). { done. }
      iIntros (v) "[%b [Hv Hb]]". unfold bu_insert_go.
      destruct b; iDestruct "Hv" as %->; iDestruct "Hb" as %<-.
      { wp_type. }
      { wp_heap. if_decide.
        - wp_type.
        - wp_pures. wp_load. wp_alloc Hk as "Hk'". wp_load. wp_alloc Ht as "Ht'".
          wp_apply (heap_unzip_correct (Node rk l x r) k with "[Hp Hl Hr Hk' Ht']").
          { wp_type. } wp_type; now destruct bu_unzip. }
  - wp_type.
Qed.

End proof.
