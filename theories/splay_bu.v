(* Copyright (c) 2023 Microsoft Research, Anton Lorenzen *)

From fip_iris Require Import lang tree tree_bu splay.

Definition rotate_right : val :=
  fun: ( z, t ) {
    var: tmp := z->left in
    z->tag = #1;;
    z->left = t->right;;
    t->right = z;;
    z = tmp
  }.

Definition rotate_left : val :=
  fun: (z, t) {
    var: tmp := z->right in
    z->tag = #1;;
    z->right = t->left;;
    t->left = z;;
    z = tmp
  }.

Definition heap_splay : val :=
  fun: (px, x) {
    while: ( true ) {
      if: (px == NULL) {
        break
      } else {
        if: (px->tag == #1) {
          var: gx := px->left in
          if: (gx == NULL) {
            rotate_right (&px) (&x)
          } else {
            if: (gx->tag == #1) {
              rotate_right (&gx) (&px);;
              rotate_right (&px) (&x);;
              px = gx
            } else {
              rotate_right (&px) (&x);;
              rotate_left (&px) (&x)
            }
          }
        } else {
          var: gx := px->right in
          if: (gx == NULL) {
            rotate_left (&px) (&x)
          } else {
            if: (gx->tag == #1) {
              rotate_left (&px) (&x);;
              rotate_right (&px) (&x)
            } else {
              rotate_left (&gx) (&px);;
              rotate_left (&px) (&x);;
              px = gx
            }
          }
        }
      }
    };;
    ret: x
  }.

Definition heap_bu_insert_pub : val :=
  fun: ( i,  tree' ) {
    var: zipper' := NULL in
    while: ( true ) {
      if: ( tree' == NULL ) {
        tree' = (AllocN #4 NULL);;
        tree'->tag = #1;;
        tree'->key = i;;
        break
      } else {
        if: ( i == tree'->key ) {
          break
        } else {
          var: tmp := NULL in
          (if: ( i < tree'->key ) {
            tmp = tree'->left;;
            tree'->left = zipper'
          } else {
            tmp = tree'->right;;
            tree'->tag = #2;;
            tree'->right = zipper'
          });;
          zipper' = tree';;
          tree' = tmp
        }
      }
    };;
    ret: heap_splay (&zipper') (&tree')
  }.

Definition heap_bu_insert : val :=
  fun: (i, tree') {
    var: zipper' := NULL in
    while: ( true ) {
      if: ( tree' == NULL ) {
        tree' = AllocN #4 NULL;;
        tree'->tag = #1;;
        tree'->key = i;;
        break
      } else {
        if: ( i == tree'->key) {
          break
        } else {
          if: ( i < tree'->key) {
            var: l := tree'->left in
            if: ( l == NULL ) {
              l = AllocN #4 NULL;;
              l->tag = #1;;
              l->key = i;;
              l->right = tree';;
              tree' = l;;
              break
            } else {
              if: ( i == l->key) {
                tree'->left = l->right;;
                l->right = tree';;
                tree' = l;;
                break
              } else {
                if: ( i < l->key) {
                  var: ll := l->left in
                  tree'->left = zipper';;
                  l->left = tree';;
                  zipper' = l;;
                  tree' = ll
                } else {
                  var: lr := l->right in
                  l->tag = #2;;
                  tree'->left = zipper';;
                  l->right = tree';;
                  zipper' = l;;
                  tree' = lr
                }
              }
            }
          } else {
            var: r := tree'->right in
            if: ( r == NULL ) {
              r = AllocN #4 NULL;;
              r->tag = #1;;
              r->left = tree';;
              r->key = i;;
              tree' = r;;
              break
            } else {
              if: ( i == r->key) {
                tree'->right = r->left;;
                r->left = tree';;
                tree' = r;;
                break
              } else {
                if: ( i < r->key) {
                  var: rl := r->left in
                  tree'->tag = #2;;
                  tree'->right = zipper';;
                  r->left = tree';;
                  zipper' = r;;
                  tree' = rl
                } else {
                  var: rr := r->right in
                  tree'->tag = #2;;
                  r->tag = #2;;
                  tree'->right = zipper';;
                  r->right = tree';;
                  zipper' = r;;
                  tree' = rr
                }
              }
            }
          }
        }
      }
    };;
    ret: heap_splay (&zipper') (&tree')
  }.

Section proof.

Local Set Default Proof Using "Type*".
Context `{!heapGS Σ}.

Lemma heap_splay_correct (z : zipper) (t : root_tree) (zv tv : val) (zipper tree : loc) :
    {{{ zipper ↦ zv ∗ is_zipper z zv ∗ tree ↦ tv ∗ is_root_tree t tv }}}
    heap_splay #zipper #tree
    {{{ v, RET v; is_root_tree (splay z t) v }}}.
Proof.
  wp_begin "[Hz Ht]". wp_while_true "H"
    (∃ t' treev, tree ↦ treev ∗ is_root_tree t' treev ∗ ⌜splay z t = t'⌝)%I
    (∃ t' z' treev zipperv,
            tree ↦ treev ∗ is_root_tree t' treev
            ∗ zipper ↦ zipperv ∗ is_zipper z' zipperv
            ∗ ⌜splay z t = splay z' t'⌝)%I.
  - iDecompose "H". now wp_heap. 
  - iDestruct "H" as (t' z' ? ?) "[? [Ht' [? [Hz ->]]]]".
    unfold rotate_right. unfold rotate_left. 
    destruct t' as [tl tx tr]. iDecompose "Ht'".
    destruct z' as [|lup lx lr|rl rx rup].
    + iDestruct "Hz" as %->. wp_heap. wp_type.
    + iDestruct "Hz" as (? ? ?) "[-> [? [Hup ?]]]". wp_heap.
      destruct lup; iDecompose "Hup"; wp_heap; wp_type.
    + iDestruct "Hz" as (? ? ?) "[-> [? [Hup ?]]]". wp_heap.
      destruct rup; iDecompose "Hup"; wp_heap; wp_type.
  - wp_type.
Qed.

Lemma heap_bu_insert_pub_correct (i : Z) (tv : val) (t : tree) :
    {{{ is_tree t tv }}}
    heap_bu_insert_pub (ref #i) (ref tv)
    {{{ v, RET v; is_tree (bu_insert_pub i t) v }}}.
Proof.
  wp_begin "Ht"; ref_i, tree. wp_var zipper. wp_while_true "H"
    (∃ t' z' treev zipperv,
            tree ↦ treev ∗ is_root_tree t' treev ∗ ref_i ↦ #i
            ∗ zipper ↦ zipperv ∗ is_zipper z' zipperv
            ∗ ⌜bu_insert_pub i t = to_tree (splay z' t')⌝)%I
    (∃ t' z' treev zipperv,
            tree ↦ treev ∗ is_tree t' treev ∗ ref_i ↦ #i
            ∗ zipper ↦ zipperv ∗ is_zipper z' zipperv
            ∗ ⌜bu_insert_pub i t = to_tree (bu_insert_pub_go i z' t')⌝)%I.
  - iDestruct "H" as (t' z' treev zipperv) "[? [Ht [? [? [Hz ->]]]]]". wp_heap.
    wp_apply (heap_splay_correct z' t' with "[-]"). { wp_type. }
    destruct (splay z' t'). wp_type.
  - iDestruct "H" as (t' ? ? ?) "[? [Ht [? [? [? ->]]]]]".
    unfold bu_insert_pub_go at 1. destruct t'; iDecompose "Ht".
    + wp_heap. wp_type.
    + wp_heap. case_bool_decide; wp_heap.
      { wp_type. } { case_bool_decide; wp_heap; wp_type. }
  - wp_type.
Qed.

Lemma heap_bu_insert_correct (i : Z) (tv : val) (t : tree) :
    {{{ is_tree t tv }}}
    heap_bu_insert (ref #i) (ref tv)
    {{{ v, RET v; is_tree (bu_insert i t) v }}}.
Proof.
  wp_begin "Ht"; ref_i, tree. wp_var zipper. wp_while_true "H"
    (∃ t' z' treev zipperv,
            tree ↦ treev ∗ is_root_tree t' treev ∗ ref_i ↦ #i
            ∗ zipper ↦ zipperv ∗ is_zipper z' zipperv
            ∗ ⌜bu_insert i t = to_tree (splay z' t')⌝)%I
    (∃ t' z' treev zipperv,
            tree ↦ treev ∗ is_tree t' treev ∗ ref_i ↦ #i
            ∗ zipper ↦ zipperv ∗ is_zipper z' zipperv
            ∗ ⌜bu_insert i t = to_tree (bu_insert_go i z' t')⌝)%I.
  - iDestruct "H" as (t' z' treev zipperv) "[? [Ht [? [? [Hz ->]]]]]". wp_heap.
    wp_apply (heap_splay_correct z' t' with "[-]"). { wp_type. }
    destruct (splay z' t'). wp_type.
  - iDestruct "H" as (t' z' ? ?) "[? [Ht [? [? [Hz ->]]]]]".
    destruct t' as [|l x r].
    + iDestruct "Ht" as %->. wp_heap. wp_type.
    + iDestruct "Ht" as (? ? ?) "[-> [? [Hl Hr]]]". wp_heap.
      unfold bu_insert_go at 1. case_bool_decide; wp_heap.
      { wp_type. }
      { case_bool_decide; wp_heap.
        - destruct l; iDecompose "Hl".
          + wp_heap. wp_type.
          + wp_heap. case_bool_decide; wp_heap.
            { wp_type. } { case_bool_decide; wp_heap; wp_type. }
        - destruct r; iDecompose "Hr".
          + wp_heap. wp_type.
          + wp_heap. case_bool_decide; wp_heap.
            { wp_type. } { case_bool_decide; wp_heap; wp_type. } }
  - wp_type.
Qed.

End proof.
