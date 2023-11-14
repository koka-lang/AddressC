(* Copyright (c) 2023 Microsoft Research, Anton Lorenzen *)

From fip_iris Require Import lang.

Fixpoint append (xs : list Z) (ys : list Z) (acc : list Z -> list Z) :=
  match xs with
  | [] => acc ys
  | x :: xs => append xs ys (compose acc (fun ys' => x :: ys'))
  end.

Definition heap_append : val :=
  fun: ( xs, ys ) {
    if: ( xs == NULL ) { 
      ret: ys
    } else {
      var: curr := &(xs〚1〛) in
      while: ((✲curr) != NULL) {
        curr = &((✲curr)〚1〛)
      };;
      ✲curr = ys;;
      ret: xs
    }
  }.

Section proof.

Local Set Default Proof Using "Type*".
Context `{!heapGS Σ}.

Fixpoint is_list (l : list Z) (v : val) : iProp Σ :=
  match l with
  | [] => ⌜v = NULL⌝
  | x :: xs => ∃ (p : loc) v', ⌜v =  #p⌝ ∗ p ↦∗ [ #x; v' ] ∗ is_list xs v'
  end.

#[export]
Instance is_list_nil_hint t :
HINT ε₁ ✱ [- ; ⌜t = []⌝] ⊫ [id]; is_list t NULL ✱ [⌜t = []⌝].
Proof. iSteps. Qed.

#[export]
Instance is_list_cons_hint (p : loc) (x : Z) (l_acc : val) t :
HINT p ↦∗ [ #x; l_acc] ✱ [ acc ; is_list acc l_acc ∗ ⌜t = x :: acc⌝]
  ⊫ [id]; is_list t #p ✱ [⌜t = x :: acc⌝].
Proof. iSteps. Qed.

Lemma heap_append_correct (xsv : val) (xs : list Z) (ysv : val) (ys : list Z) :
    {{{ is_list xs xsv ∗ is_list ys ysv }}}
    heap_append (ref xsv) (ref ysv)
    {{{ v, RET v; is_list (append xs ys (fun x => x)) v }}}.
Proof.
  wp_begin "[Hxs Hys]"; lxs, lys. destruct xs.
  - iDecompose "Hxs". wp_type.
  - iDestruct "Hxs" as (p v') "[-> [Hp Hxs]]". wp_load.
    wp_pures. wp_load. wp_var curr. wp_while
        (∃ xs' xsv acc' (p : loc) (currp : loc),
            lxs ↦ #p ∗ (∀ l currv, (currp ↦ currv ∗ is_list l currv) -∗ is_list (acc' l) #p) ∗
            lys ↦ ysv ∗ is_list ys ysv ∗
            curr ↦ #currp ∗ currp ↦ xsv ∗ is_list xs' xsv ∗
            ⌜append (z :: xs) ys (fun x => x) = append xs' ys acc'⌝)%I.
    + iModIntro. iIntros "H". iDestruct "H" as (xs' xsv acc p' currp) "H".
      iDestruct "H" as "[? [Hc [? [Hys [? [? [Hxs ->]]]]]]]". destruct xs' as [| x xx].
      { iDecompose "Hxs". wp_type. }
      { iDestruct "Hxs" as (p'' v'') "[-> [Hp Hxs]]".
        wp_heap. wp_enter_loop. wp_heap. iModIntro.
        iExists xx, _, (compose acc (fun ys' => x :: ys')), p', (p'' +ₗ 1%nat).
        unfold array at 1. iDecompose "Hp". iFrame. iSplitL.
        - iSteps. unfold array. iSteps.
        - done. }
    + iExists xs, _, (fun ys' => z :: ys'), p, (p +ₗ 1%nat).
      iFrame. unfold array. iDecompose "Hp". iFrame.
      iSplitL. unfold array. iSteps. iSteps. 
Qed.

End proof.