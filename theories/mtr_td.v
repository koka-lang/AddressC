(* Copyright (c) 2023 Microsoft Research, Anton Lorenzen *)

From fip_iris Require Import lang tree tree_td mtr.

Notation "e1 '->value'" :=
  (Load (BinOp OffsetOp e1%E (Val (LitV (LitInt (Z.of_nat 1))))))
  (at level 20) : expr_scope.

Definition heap_mtr_insert_td : val :=
  fun: ( name, root ) {
    var: left_dummy := NULL in
    var: right_dummy := NULL in
    var: node := root in
    var: left_hook := &left_dummy in
    var: right_hook := &right_dummy in
    while: ( true ) {
      if: ( node != NULL) {
        if: ( node->value == name ) {

          ✲left_hook = node->left;;
          ✲right_hook = node->right;;
          root = node;;
          break
        }         
        else {
          if: ( node->value > name ) 
          {

            ✲right_hook = node;;
            right_hook = &(node->left);;
            node = node->left
          } 
          
          else 
          {
            ✲left_hook = node;;
            left_hook = &(node->right);;
            node = node->right
      } } }
      else {
        ✲left_hook = NULL;;
        ✲right_hook = NULL;;
        root = AllocN #3 NULL;;
        root->value = name;;
        break
      }
    };;
    root->left = left_dummy;;
    root->right = right_dummy;;
    ret: root
  }.

Section proof.

Local Set Default Proof Using "Type*".
Context `{!heapGS Σ}.

Definition mtr_insert_td t k := td_insert k t.
Definition mtr_down_td t k accl accr := td_insert_go k accl accr t.

Lemma heap_td_insert_correct (k : Z) (tv : val) (t : tree) :
    {{{ is_tree t tv }}}
    heap_mtr_insert_td (ref #k) (ref tv)
    {{{ v, RET v; is_tree (mtr_insert_td t k) v }}}.
Proof.
  wp_begin "Ht"; name, root. wp_var left_dummy. wp_var right_dummy.
  wp_load. wp_var node. wp_var left_hook. wp_var right_hook.
  wp_while_true "H"
    (∃ l (x : Z) r left_dummy_v right_dummy_v (p : loc) left_dangling_v right_dangling_v,
            root ↦ #p ∗ p ↦∗ [left_dangling_v; #x; right_dangling_v]
            ∗ left_dummy ↦ left_dummy_v ∗ is_tree l left_dummy_v
            ∗ right_dummy ↦ right_dummy_v ∗ is_tree r right_dummy_v
            ∗ ⌜mtr_insert_td t k = Node l x r⌝)%I
    (∃ accl accr t' (left_hole right_hole : loc) left_hole_v right_hole_v root_v node_v,
            node ↦ node_v ∗ is_tree t' node_v
            ∗ root ↦ root_v ∗ name ↦ #k
            ∗ left_hook  ↦ #left_hole  ∗ left_hole  ↦ left_hole_v  ∗ is_ctx accl left_dummy  left_hole
            ∗ right_hook ↦ #right_hole ∗ right_hole ↦ right_hole_v ∗ is_ctx accr right_dummy right_hole
            ∗ ⌜mtr_insert_td t k = mtr_down_td t' k accl accr⌝)%I.
  - iDecompose "H". iSteps.                               (* The claim follows once the while-loop ends *)
  - iDecompose "H". rewrite H1.                                     (* Rewrite one functional tail-call *)
    unfold array. repeat (iSteps; try case_bool_decide).            (* Then the invariant is maintained *)
  - iSteps.                                             (* The preconditions of the while-loop are true *)
Qed.

End proof.