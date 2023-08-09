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

Lemma heap_td_insert_correct (i : Z) (tv : val) (t : tree) :
    {{{ is_tree t tv }}}
    heap_mtr_insert_td (ref #i) (ref tv)
    {{{ v, RET v; is_tree (td_insert i t) v }}}.
Proof.
  wp_begin "Ht"; name, root. wp_var left_dummy. wp_var right_dummy.
  wp_load. wp_var node. wp_var left_hook. wp_var right_hook. wp_while_true "H"
    (∃ l (x : Z) r lv rv (p : loc) lv' rv',
            root ↦ #p ∗ p ↦∗ [lv'; #x; rv']
            ∗ left_dummy ↦ lv ∗ is_tree l lv
            ∗ right_dummy ↦ rv ∗ is_tree r rv
            ∗ ⌜td_insert i t = Node l x r⌝)%I
    (∃ lz' rz' t' (lhv rhv : loc) lhvv rhvv rootv treev,
            node ↦ treev ∗ is_tree t' treev
            ∗ root ↦ rootv ∗ name ↦ #i
            ∗ left_hook ↦ #lhv ∗ lhv ↦ lhvv ∗ is_ctx lz' left_dummy lhv
            ∗ right_hook ↦ #rhv∗ rhv ↦ rhvv ∗ is_ctx rz' right_dummy rhv
            ∗ ⌜td_insert i t = td_insert_go i lz' rz' t'⌝)%I.
  - iDecompose "H". wp_heap. wp_type.
  - iDestruct "H" as (lz' ? t' ? ? ? ? ? ?) "[? [Ht H]]".
    iDecompose "H". rewrite H. unfold td_insert_go at 1.
    destruct t'; iDecompose "Ht".
    + wp_heap. wp_type.
    + wp_heap. case_bool_decide; wp_heap.
      { wp_type. } { case_bool_decide; wp_heap; wp_type. }
  - wp_type.
Qed.

End proof.