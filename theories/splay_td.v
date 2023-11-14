(* Copyright (c) 2023 Microsoft Research, Anton Lorenzen *)

From fip_iris Require Import lang tree tree_td splay.

Definition rotate_right : val :=
  fun: ( tree' ) {
    var: l := tree'->left in
    tree'->left = l->right;;
    l->right = tree';;
    tree' = l
  }.

Definition rotate_left : val :=
  fun: ( tree' ) {
    var: r := tree'->right in
    tree'->right = r->left;;
    r->left = tree';;
    tree' = r
  }.

Definition link_left : val :=
  fun: ( tree', lhole ) {
    ✲lhole = tree';;
    lhole = &(tree'->right);;
    tree' = tree'->right
  }.

Definition link_right : val :=
  fun: ( tree', rhole ) {
    ✲rhole = tree';;
    rhole = &(tree'->left);;
    tree' = tree'->left
  }.

Definition assemble : val :=
  fun: ( tree', lhole, rhole, lctx, rctx ) {
    ✲lhole = tree'->left;;
    ✲rhole = tree'->right;;
    tree'->left = lctx;;
    tree'->right = rctx
  }.

Definition heap_td_insert : val :=
  fun: ( i, tree' ) {
    var: lctx := NULL in
    var: rctx := NULL in
    var: lhole := &lctx in
    var: rhole := &rctx in
    while: ( true ) {
      if: (tree' != NULL) {
        if: ( i == tree'->key) {
          break
        } else {
          if: ( i < tree'->key) {
            if: (tree'->left != NULL) {
              if: ( i == tree'->left->key) {
                link_right (&tree') (&rhole);;
                break
              } else {
                if: ( i < tree'->left->key) {
                  rotate_right (&tree');;
                  link_right (&tree') (&rhole)
                } else {
                  link_right (&tree') (&rhole);;
                  link_left (&tree') (&lhole)
                }
              }
            } else {
              var: l := tree'->left in
              l = AllocN #3 NULL;;
              l->key = i;;
              l->right = tree';;
              tree' = l;;
              break
            }
          } else {
            if: (tree'->right != NULL) {
              if: ( i == tree'->right->key) {
                link_left (&tree') (&lhole);;
                break
              } else {
                if: ( i > tree'->right->key) {
                  rotate_left (&tree');;
                  link_left (&tree') (&lhole)
                } else {
                  link_left (&tree') (&lhole);;
                  link_right (&tree') (&rhole)
                }
              }
            } else {
              var: r := tree'->right in
              r = AllocN #3 NULL;;
              r->left = tree';;
              r->key = i;;
              tree' = r;;
              break
            }
          }
        }
      } else {
        tree' = AllocN #3 NULL;;
        tree'->key = i;;
        break
      }
    };;
    assemble (&tree') (&lhole) (&rhole) (&lctx) (&rctx);;
    ret: tree'
  }.

Section proof.

Local Set Default Proof Using "Type*".
Context `{!heapGS Σ}.

Lemma heap_td_insert_correct (i : Z) (tv : val) (t : tree) :
    {{{ is_tree t tv }}}
    heap_td_insert (ref #i) (ref tv)
    {{{ v, RET v; is_tree (td_insert i t) v }}}.
Proof.
  wp_begin "Ht"; ref_i, tree.
  wp_alloc lctx as "Hlctx". wp_let. wp_alloc rctx as "Hrctx". wp_let.
  wp_var lhole. wp_var rhole. wp_while_true "H"
    (∃ lz' l (x : Z) rz' r treev (lhv rhv : loc) lhvv rhvv,
            tree ↦ treev ∗ is_tree (Node l x r) treev ∗ ref_i ↦ #i
            ∗ lhole ↦ #lhv ∗ lhv ↦ lhvv ∗ is_ctx lz' lctx lhv
            ∗ rhole ↦ #rhv ∗ rhv ↦ rhvv ∗ is_ctx rz' rctx rhv
            ∗ ⌜td_insert_go i Hole Hole t = (lz', Root l x r, rz')⌝)%I
    (∃ lz' rz' t' (lhv rhv : loc) lhvv rhvv treev,
            tree ↦ treev ∗ is_tree t' treev ∗ ref_i ↦ #i
            ∗ lhole ↦ #lhv ∗ lhv ↦ lhvv ∗ is_ctx lz' lctx lhv
            ∗ rhole ↦ #rhv ∗ rhv ↦ rhvv ∗ is_ctx rz' rctx rhv
            ∗ ⌜td_insert_go i Hole Hole t = td_insert_go i lz' rz' t'⌝)%I.
  - unfold td_insert. iDecompose "H". unfold assemble.
    wp_type. now rewrite H2.
  - iDestruct "H" as (? ? t' ? ? ? ? ?) "(? & Ht & ? & ? & ? & ? & ? & ? & ? & ->)".
    unfold rotate_right, rotate_left, link_right, link_left.
    destruct t' as [|l x r].
    + iDecompose "Ht". wp_heap. wp_type.
    + iDestruct "Ht" as (? ? ?) "(-> & ? & Hl & Hr)". wp_heap.
      unfold td_insert_go at 1. case_bool_decide; wp_heap. { wp_type. }
      { case_bool_decide; wp_heap.
        - destruct l; iDecompose "Hl".
          + wp_heap. wp_type.
          + wp_heap. case_bool_decide; wp_heap; wp_type.
        - destruct r; iDecompose "Hr".
          + wp_heap. wp_type.
          + wp_heap. case_bool_decide; wp_heap; wp_type; iExFalso; lia. }
  - wp_type.
Qed.

End proof.