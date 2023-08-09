From Equations Require Import Equations.
From fip_iris Require Import lang.

Inductive tree : Set :=
| Leaf
| Node (l : tree) (x : Z) (r : tree).

Inductive zipper : Set :=
| Done
| NodeL (z : zipper) (x : Z) (r : tree)
| NodeR (z : zipper) (x : Z) (l : tree).

Inductive dir : Set := Down | Up.

Fixpoint rec_tmap (t : tree) :=
  match t with
  | Leaf => Leaf
  | Node l x r => Node (rec_tmap l) (x + 1) (rec_tmap r)
  end.

(* Show termination of tmap *)
Fixpoint tmap_steps_tree (arg : tree) : nat :=
  match arg with
  | Leaf => 1
  | Node l x r => 3 + (tmap_steps_tree l) + (tmap_steps_tree r)
  end.

Fixpoint tmap_steps_zipper (arg : zipper) : nat :=
  match arg with
  | Done => 0
  | NodeL z x r => 2 + (tmap_steps_zipper z) + (tmap_steps_tree r)
  | NodeR z x l => 1 + (tmap_steps_zipper z)
  end.

Definition tmap_steps (arg : dir * tree * zipper) : nat :=
  match arg with
  | (Down, t, z) => tmap_steps_tree t + tmap_steps_zipper z
  | (Up, t, z) => tmap_steps_zipper z
  end.

Equations? tmap (arg : dir * tree * zipper) : tree by wf (tmap_steps arg) lt :=
  tmap (Down, Leaf, z) := tmap (Up, Leaf, z);
  tmap (Down, Node l x r, z) := tmap (Down, l, NodeL z x r);
  tmap (Up, t, Done) := t;
  tmap (Up, l, NodeL z' x r) := tmap (Down, r, NodeR z' (x + 1) l);
  tmap (Up, r, NodeR z' x l) := tmap (Up, Node l x r, z').
Proof. all: simpl. all: lia. Qed.

Definition heap_tmap :=
  fun: ( tree' ) {
    var: dir' := NULL in
    var: zipper' := NULL in
    while: ( true ) {
      if: (dir' == NULL) {
        if: (tree' == NULL) {
            dir' = #1
        } else {
            var: tmp := tree' in
            tree' = tree'〚1〛;;
            tmp〚1〛= zipper';;
            zipper' = tmp
        }
      } else {
        if: (zipper' == NULL) {
          break
        } else {
          if: (zipper'〚0〛 == #1) {
            var: tmp := zipper'〚3〛 in
            dir' = NULL;;
            zipper'〚0〛 = #2;;
            zipper'〚2〛 = zipper'〚2〛 + #1;;
            zipper'〚3〛 = tree';;
            tree' = tmp
          } else {
            var: tmp := zipper'〚1〛 in
            zipper'〚0〛 = #1;;
            zipper'〚1〛 = zipper'〚3〛;;
            zipper'〚3〛 = tree';;
            tree' = zipper';;
            zipper' = tmp
          }
        }
      }
    };;
    ret: tree'
  }.

Section proof.

Local Set Default Proof Using "Type*".
Context `{!heapGS Σ}.

Fixpoint is_tree (t : tree) (v : val) : iProp Σ :=
  match t with
  | Leaf => ⌜v = NULL⌝
  | Node l x r => ∃ (p : loc) l' r', ⌜v =  #p⌝ ∗ p ↦∗ [ #1; l'; #x; r' ] ∗ is_tree l l' ∗ is_tree r r'
  end.

#[export]
Instance is_tree_leaf_hint t :
HINT ε₁ ✱ [- ; ⌜t = Leaf⌝] ⊫ [id]; is_tree t NULL ✱ [⌜t = Leaf⌝].
Proof. iSteps. Qed.

#[export]
Instance is_tree_node_hint (p : loc) (x : Z) (l_r l_l : val) t :
HINT p ↦∗ [ #1; l_l; #x; l_r] ✱ [ l r ; is_tree l l_l ∗ is_tree r l_r ∗ ⌜t = Node l x r⌝]
  ⊫ [id]; is_tree t #p ✱ [⌜t = Node l x r⌝].
Proof. iSteps. Qed.

Fixpoint is_zipper (z : zipper) (v : val) : iProp Σ :=
  match z with
  | Done => ⌜v = NULL⌝
  | NodeL z x r => ∃ (p : loc) z' r', ⌜v =  #p⌝ ∗ p ↦∗ [ #1; z'; #x; r' ] ∗ is_zipper z z' ∗ is_tree r r'
  | NodeR z x l => ∃ (p : loc) z' l', ⌜v =  #p⌝ ∗ p ↦∗ [ #2; z'; #x; l' ] ∗ is_zipper z z' ∗ is_tree l l'
  end.

#[export]
Instance is_zipper_done_hint t :
HINT ε₁ ✱ [- ; ⌜t = Done⌝] ⊫ [id]; is_zipper t NULL ✱ [⌜t = Done⌝].
Proof. iSteps. Qed.

#[export]
Instance is_zipper_nodel_hint (p : loc) (x : Z) (l_l l_r : val) t :
HINT p ↦∗ [ #1; l_l; #x; l_r] ✱ [l r ; is_zipper l l_l ∗ is_tree r l_r ∗ ⌜t = NodeL l x r⌝]
  ⊫ [id]; is_zipper t #p ✱ [⌜t = NodeL l x r⌝].
Proof. iSteps. Qed.

#[export]
Instance is_zipper_noder_hint (p : loc) (x : Z) (l_l l_r : val) t :
HINT p ↦∗ [ #2; l_r; #x; l_l] ✱ [r l ; is_tree l l_l ∗ is_zipper r l_r ∗ ⌜t = NodeR r x l⌝]
  ⊫ [id]; is_zipper t #p ✱ [⌜t = NodeR r x l⌝].
Proof. iSteps. Qed.

Definition is_dir (d : dir) (v : val) : iProp Σ :=
  match d with
  | Down => ⌜v = NULL⌝
  | Up => ⌜v = #1⌝
  end.

#[export]
Instance is_dir_down_hint t :
HINT ε₁ ✱ [- ; ⌜t = Down⌝] ⊫ [id]; is_dir t NULL ✱ [⌜t = Down⌝].
Proof. iSteps. Qed.

#[export]
Instance is_dir_up_hint t :
HINT ε₁ ✱ [- ; ⌜t = Up⌝] ⊫ [id]; is_dir t #1 ✱ [⌜t = Up⌝].
Proof. iSteps. Qed.

Lemma heap_tmap_correct (tv : val) (t : tree) :
    {{{ is_tree t tv }}} heap_tmap (ref tv) {{{ v, RET v; is_tree (tmap (Down, t, Done)) v }}}.
Proof.
  wp_begin "Ht"; tree. wp_var dir. wp_var zipper. wp_while_true "H"
    (∃ t' treev, tree ↦ treev ∗ is_tree t' treev ∗ ⌜t' = tmap (Down, t, Done)⌝)%I
    (∃ t' z' d' treev zipperv dirv,
            tree ↦ treev ∗ is_tree t' treev
            ∗ zipper ↦ zipperv ∗ is_zipper z' zipperv
            ∗ dir ↦ dirv ∗ is_dir d' dirv
            ∗ ⌜tmap (Down, t, Done) = tmap (d', t', z')⌝)%I.
  - iDecompose "H". now wp_heap.
  - iDestruct "H" as (t' z d ? ? ?) "[? [Ht [? [Hz [? [Hd ->]]]]]]".
    destruct d; iDecompose "Hd"; wp_heap.
    + destruct t'; iDecompose "Ht".
      { wp_heap. wp_type. now simp tmap. }
      { wp_heap. wp_type. now simp tmap. }
    + destruct z; iDecompose "Hz".
      { wp_heap. wp_type. }
      { wp_heap. wp_type. now simp tmap. }
      { wp_heap. wp_type. now simp tmap. }
  - wp_type.
Qed.

End proof.
