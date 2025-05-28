(* Copyright (c) 2025 Microsoft Research, Anton Lorenzen *)

From fip_iris Require Import lang tree tree_td splay.

Definition rotate_right : val :=
  fun: ( t ) {
    var: temp := t->left in
    t->left = temp->right;;
    temp->right = t;;
    t = temp
  }.

Definition rotate_left : val :=
  fun: ( t ) {
    var: temp := t->right in
    t->right = temp->left;;
    temp->left = t;;
    t = temp
  }.

Definition link_left := fun: ( t, l ) {
    l->right = t;; l = t;; t = t->right
  }.

Definition link_right : val :=
  fun: ( t, r ) {
    r->left = t;;
    r = t;;
    t = t->left
  }.

Definition assemble : val :=
  fun: ( t, null, l, r ) {
    l->right = t->left;;
    r->left = t->right;;
    t->left = null->right;;
    t->right = null->left
  }.

Definition top_down_splay := fun: ( i, t ) {
    var: null := AllocN #3 NULL in
    var: l := null in var: r := null in
    while: ( true ) {
      if: (t != NULL) {
        if: ( i < t->item ) {
          if: (t->left != NULL) {
            if: ( i > t->left->item ) {
              link_right (&t) (&r);;
              link_left (&t) (&l)
            } else {
              if: ( i < t->left->item) {
                rotate_right (&t);;
                link_right (&t) (&r)
              } else {
                link_right (&t) (&r);;
                break
              }
            }
          } else {
            var: l := t->left in
            l = AllocN #3 NULL;;
            l->item = i;;
            l->right = t;;
            t = l;;
            break
          }
        } else {
          if: ( i == t->item) {
            break
          } else {
            if: (t->right != NULL) {
              if: ( i == t->right->item) {
                link_left (&t) (&l);;
                break
              } else {
                if: ( i > t->right->item) {
                  rotate_left (&t);;
                  link_left (&t) (&l)
                } else {
                  link_left (&t) (&l);;
                  link_right (&t) (&r)
                }
              }
            } else {
              var: r := t->right in
              r = AllocN #3 NULL;;
              r->left = t;;
              r->item = i;;
              t = r;;
              break
            }
          }
        }
      } else {
        t = AllocN #3 NULL;;
        t->item = i;;
        break
      }
    };;
    assemble (&t) (&null) (&l) (&r);;
    ret: t
  }.

Section proof.

Local Set Default Proof Using "Type*".
Context `{!heapGS Σ}.

Lemma heap_td_insert_correct (i : Z) (tv : val) (t' : tree) :
    {{{ is_tree t' tv }}}
    top_down_splay (ref #i) (ref tv)
    {{{ v, RET v; is_tree (td_insert i t') v }}}.
Proof.
  wp_begin "Ht"; ref_i, t.
  wp_alloc nullc. { lia. } wp_var null. wp_load. wp_var l. wp_load. wp_var r.
  wp_while_true "H"
    (∃ lz' l' (x : Z) rz' r' tv (lhv rhv nullv : loc) lhvv rhvv,
            t ↦ tv ∗ is_tree (Node l' x r') tv ∗ ref_i ↦ #i ∗ null ↦ #nullv
            ∗ l ↦ #lhv ∗ (lhv +ₗ 2) ↦ lhvv ∗ is_ctx lz' (nullv +ₗ 2) (lhv +ₗ 2)
            ∗ r ↦ #rhv ∗ (rhv +ₗ 0) ↦ rhvv ∗ is_ctx rz' (nullv +ₗ 0) (rhv +ₗ 0)
            ∗ ⌜td_insert_go i Hole Hole t' = (lz', Root l' x r', rz')⌝)%I
    (∃ lz' rz' t'' (lhv rhv nullv : loc) lhvv rhvv tv,
            t ↦ tv ∗ is_tree t'' tv ∗ ref_i ↦ #i ∗ null ↦ #nullv
            ∗ l ↦ #lhv ∗ (lhv +ₗ 2) ↦ lhvv ∗ is_ctx lz' (nullv +ₗ 2) (lhv +ₗ 2)
            ∗ r ↦ #rhv ∗ (rhv +ₗ 0) ↦ rhvv ∗ is_ctx rz' (nullv +ₗ 0) (rhv +ₗ 0)
            ∗ ⌜td_insert_go i Hole Hole t' = td_insert_go i lz' rz' t''⌝)%I.
  - unfold td_insert. iDecompose "H". unfold assemble.
    wp_type. now rewrite H2.
  - iDestruct "H" as (? ? t'' ? ? ? ? ? ?)
      "(? & Ht & ? & ? & ? & ? & ? & ? & ? & ? & ->)".
    unfold rotate_right, rotate_left, link_right, link_left.
    destruct t'' as [|l' x r'].
    + iDecompose "Ht". wp_heap. wp_type.
    + iDestruct "Ht" as (? ? ?) "(-> & ? & Hl & Hr)". wp_heap.
      unfold td_insert_go at 1.
      if_decide; wp_heap.
      * destruct l'; iDecompose "Hl".
        -- wp_heap. wp_type.
        -- if_decide; wp_heap.
           ++ wp_heap. wp_type.
           ++ wp_heap. if_decide; wp_heap; wp_type.
      * if_decide; wp_heap. wp_type.
        destruct r'; iDecompose "Hr".
          -- wp_heap. wp_type.
          -- wp_heap. if_decide; wp_heap; wp_type.
  - wp_type.
Qed.

End proof.