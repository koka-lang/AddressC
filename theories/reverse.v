From fip_iris Require Import lang.

Fixpoint reverse (xs : list Z) (acc : list Z) :=
  match xs with
  | [] => acc
  | x :: xs => reverse xs (x :: acc)
  end.

Fixpoint is_list `{!heapGS Σ}  (l : list Z) (v : val) : iProp Σ :=
  match l with
  | [] => ⌜v = NULL⌝
  | x :: xs => ∃ (p : loc) v', ⌜v =  #p⌝ ∗ p ↦∗ [ #x; v' ] ∗ is_list xs v'
  end.

Definition heap_reverse :=
  fun: ( curr ) {                  (* A function to reverse the list `curr` *)
    var: prev := NULL in           (* The accumulator starts out as empty *)
    while: (curr != NULL) {        (* Until we reach the end of the list: *)
      var: next := curr〚1〛 in     (* Store the tail of the list *)
      curr〚1〛 = prev;;            (* Set the tail to the accumulator *)
      prev = curr;;                (* The new cell is added to the accumulator *)
      curr = next                  (* Continue with the stored tail *)
    };;
    ret: prev                      (* Return the accumulator *)
  }.

Section proof.

Local Set Default Proof Using "Type*".
Context `{!heapGS Σ}.

#[export]
Instance is_list_nil_hint t :
HINT ε₁ ✱ [- ; ⌜t = []⌝] ⊫ [id]; is_list t NULL ✱ [⌜t = []⌝].
Proof. iSteps. Qed.

#[export]
Instance is_list_cons_hint (p : loc) (x : Z) (l_acc : val) t :
HINT p ↦∗ [ #x; l_acc] ✱ [ acc ; is_list acc l_acc ∗ ⌜t = x :: acc⌝]
  ⊫ [id]; is_list t #p ✱ [⌜t = x :: acc⌝].
Proof. iSteps. Qed.

Lemma heap_reverse_correct (xsv : val) (xs : list Z) :
    {{{ is_list xs xsv }}} heap_reverse (ref xsv) {{{ v, RET v; is_list (reverse xs []) v }}}.
Proof.
  wp_begin "Hxs"; curr. wp_var prev.          (* Set up the program with variables curr and prev *)
  wp_while (∃ xs' acc' prevv currv,           (* This is the main loop invariant: *)
    curr ↦ currv ∗ is_list xs' currv          (* - curr points to an Iris list corresponding to xs' *)
    ∗ prev ↦ prevv ∗ is_list acc' prevv       (* - prev points to an Iris list corresponding to acc' *)
    ∗ ⌜reverse xs [] = reverse xs' acc'⌝)%I.  (* - and xs', acc' correspond to one iteration of the functional program *)
  - iModIntro. iIntros "[%xs' [% [% [% [? [Hxs [? [? ->]]]]]]]]".
    destruct xs'; iDecompose "Hxs".           (* Split the current list as in the `match` statement *)
     { wp_type. }                             (* If the list is empty, the loop finishes and we are done *)
     { wp_heap.                               (* Otherwise, we evaluate `curr != NULL` *)
       wp_enter_loop.                         (* curr is not null and we enter the loop *)
       wp_heap.                               (* We complete the assignments of the main loop body *)
       wp_type. }                             (* We show that the loop invariant is maintained *)
  - wp_type.                                  (* We show that the loop invarint is true at the start. *)
Qed.

End proof.
