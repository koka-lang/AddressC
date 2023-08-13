(* Copyright (c) 2023 Microsoft Research, Anton Lorenzen *)

From fip_iris Require Import lang tree tree_bu mtr.

Definition rotate_right :=
  fun: ( t ) {
    var: l := t->left in
    var: lr := l->right in
    t->left = lr;;
    l->right = t;;
    t = l
  }.

Definition rotate_left :=
  fun: ( t ) {
    var: r := t->right in
    var: rl := r->left in
    t->right = rl;;
    r->left = t;;
    t = r
  }.

Definition heap_rebuild :=
  fun: ( zipper' , tree' ) {
    while: ( true ) {
      if: ( zipper' == NULL ) { break } else {
        if: ( zipper'->tag == #1 ) {
          var: up := zipper'->left in
          zipper'->left = tree';;
          rotate_right (&zipper');;
          zipper' = up
        } else {
          var: up := zipper'->right in
          zipper'->tag = #1;; (* set tag from NodeR to Node *)
          zipper'->right = tree';;
          rotate_left (&zipper');;
          zipper' = up
    } } };; ret: tree'
  }.

Definition heap_bu_insert :=
  fun: ( i, tree' ) {
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
          var: tmp := NULL in
          (if: ( i < tree'->key) {
            tmp = tree'->left;;
            tree'->left = zipper'
          } else {
            tmp = tree'->right;;
            tree'->tag = #2;;
            tree'->right = zipper'
          });;
          zipper' = tree';;
          tree' = tmp
    } } };; ret: ( heap_rebuild (&zipper') (&tree') )
  }.

Section proof.

Local Set Default Proof Using "Type*".
Context `{!heapGS Σ}.

Lemma heap_rebuild_correct (z : zipper) (t : root_tree) (zipper tree : loc) (zv tv : val) :
    {{{ zipper ↦ zv ∗ is_zipper z zv
      ∗ tree ↦ tv ∗ is_root_tree t tv }}}
    heap_rebuild #zipper #tree
    {{{ v, RET v; is_root_tree (move_to_root z t) v }}}.
Proof.
  wp_begin "[Hz Ht]". wp_while_true "H"
    (∃ t' treev, tree ↦ treev ∗ is_root_tree t' treev ∗ ⌜move_to_root z t = t'⌝)%I
    (∃ t' z' treev zipperv,
            tree ↦ treev ∗ is_root_tree t' treev
            ∗ zipper ↦ zipperv ∗ is_zipper z' zipperv
            ∗ ⌜move_to_root z t = move_to_root z' t'⌝)%I.
  - iSteps.
  - iDestruct "H" as (t' z' treev zipperv) "[? [Ht' [? [Hz ->]]]]".
    unfold rotate_right. unfold rotate_left.
    destruct t' as [l x r]. iDestruct "Ht'" as (p l' r') "[-> [? [? ?]]]".
    destruct z' as [|zl zx zr|zl zx zr].
    + iDestruct "Hz" as %->. wp_heap. wp_type.
    + iDestruct "Hz" as (zp z'' zr') "[-> [? [? ?]]]". wp_heap. wp_type.
    + iDestruct "Hz" as (zp zl' z'') "[-> [? [? ?]]]". wp_heap. wp_type.
  - iSteps.
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
            ∗ ⌜bu_insert i t = to_tree (move_to_root z' t')⌝)%I
    (∃ t' z' treev zipperv,
            tree ↦ treev ∗ is_tree t' treev ∗ ref_i ↦ #i
            ∗ zipper ↦ zipperv ∗ is_zipper z' zipperv
            ∗ ⌜bu_insert i t = to_tree (bu_insert_go i z' t')⌝)%I.
  - iDestruct "H" as (t' z' treev zipperv) "[? [Ht [? [? [Hz ->]]]]]". wp_heap.
    wp_apply (heap_rebuild_correct z' t' zipper tree zipperv treev with "[-]").
      { wp_type. }
    iFrame. iIntros (v) "H".  destruct (move_to_root z' t').
    iDestruct "H" as (p l' r') "[-> [? ?]]". wp_type.
  - iDestruct "H" as (t' z' treev zipperv) "[? [Ht [? [? [Hz ->]]]]]".
    unfold bu_insert_go at 1. destruct t' as [|l x r].
    + iDestruct "Ht" as %->. wp_heap. wp_type.
    + iDestruct "Ht" as (p l' r') "[-> [? [? ?]]]". wp_heap.
      case_bool_decide; wp_heap.
      { wp_type. }
      { case_bool_decide; wp_heap; wp_type. }
  - wp_type.
Qed.

End proof.