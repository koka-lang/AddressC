From fip_iris Require Import lang.

Inductive ctx0 : Set :=
| Cons  (x : Z) (z : ctx0)
| Cons' (x : Z) (* Hole *).

Inductive ctx : Set :=
| Ctx0 (z : ctx0)
| Hole.

Fixpoint comp0 (z1 z2 : ctx0) : ctx0 :=
  match z1 with
  | Cons  x zr => Cons x (comp0 zr z2)
  | Cons' x => Cons x z2 
  end.

Definition comp' (z1 : ctx) (z2 : ctx0) : ctx0 :=
  match z1 with
  | Ctx0 z1 => comp0 z1 z2
  | Hole => z2
  end.

Definition comp (z1 : ctx) (z2 : ctx0) : ctx :=
  Ctx0 (comp' z1 z2).

Fixpoint plug0 (z : ctx0) (t : list Z) : list Z :=
  match z with
  | Cons  x zr => x :: (plug0 zr t)
  | Cons' x => x :: t
  end.

Definition plug (z : ctx) (t : list Z) : list Z :=
  match z with
  | Ctx0 z => plug0 z t
  | Hole => t
  end.

Fixpoint append (xs : list Z) (ys : list Z) (acc : ctx) :=
  match xs with
  | [] => plug acc ys
  | x :: xs => append xs ys (comp acc (Cons' x))
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

Fixpoint is_ctx0 (z : ctx0) (p : loc) (h : loc) : iProp Σ :=
  match z with
  | Cons  x z => ∃ (z' : loc), p ↦∗ [ #x; #z' ] ∗ is_ctx0 z z' h
  | Cons' x => ⌜h = Loc.add p 1%nat⌝ ∗ (p +ₗ 0%nat) ↦ #x
  end.

Lemma tree_of_ctx0 (z : ctx0) (t : list Z) (zv : loc) (hv : loc) (tv : val) :
    is_ctx0 z zv hv ∗ hv ↦ tv ∗ is_list t tv -∗ is_list (plug0 z t) #zv.
Proof.
  iIntros "[Hz [Hhv Ht]]". iInduction z as [x z|x] "IH" forall (zv hv t).
  - iDecompose "Hz". iSteps.
  - iDestruct "Hz" as "[Hh Hp]".
    iAssert ((zv +ₗ 1) ↦ tv)%I with "[Hh Hhv]" as "Hhv".
      { iDestruct "Hh" as %->. done. }
    iAssert (zv ↦∗ [ #x; tv ])%I with "[Hp Hhv]" as "Hp'".
      { unfold array. iSteps. }
    iSteps.
Qed.

Lemma ctx0_of_ctx0 (z1 : ctx0) (z2 : ctx0) (zv1 : loc) (hv1 : loc) (zv2 : loc) (hv2 : loc) :
    is_ctx0 z1 zv1 hv1 ∗ hv1 ↦ #zv2 ∗ is_ctx0 z2 zv2 hv2 -∗ is_ctx0 (comp0 z1 z2) zv1 hv2.
Proof.
  iIntros "[Hz [Hhv Ht]]". iInduction z1 as [x z|x] "IH" forall (zv1 hv1 z2 zv2 hv2).
  - iDestruct "Hz" as (z') "[Hp Hz]". iSteps.
  - iDestruct "Hz" as "[Hh Hp]".
    iAssert ((zv1 +ₗ 1) ↦ #zv2)%I with "[Hh Hhv]" as "Hhv".
      { iDestruct "Hh" as %->. done. }
    iAssert (zv1 ↦∗ [ #x; #zv2 ])%I with "[Hp Hhv]" as "Hp'".
      { unfold array. iSteps. }
    iSteps.
Qed.

Lemma heap_append_correct (xsv : val) (xs : list Z) (ysv : val) (ys : list Z) :
    {{{ is_list xs xsv ∗ is_list ys ysv }}}
    heap_append (ref xsv) (ref ysv)
    {{{ v, RET v; is_list (append xs ys Hole) v }}}.
Proof.
  wp_begin "[Hxs Hys]"; lxs, lys. destruct xs.
  - iDestruct "Hxs" as %->. wp_heap. wp_type.
  - iDestruct "Hxs" as (p v') "[-> [Hp Hxs]]". wp_load.
    wp_pures. wp_load. wp_var curr. wp_while
        (∃ xs' xsv acc' (p : loc) (currp : loc),
            lxs ↦ #p ∗ is_ctx0 acc' p currp ∗
            lys ↦ ysv ∗ is_list ys ysv ∗
            curr ↦ #currp ∗ currp ↦ xsv ∗ is_list xs' xsv ∗
            ⌜append (z :: xs) ys Hole = append xs' ys (Ctx0 acc')⌝)%I.
    + iModIntro. iIntros "H". iDestruct "H" as (xs' xsv acc p' currp) "H".
      iDestruct "H" as "[? [Hc [? [Hys [? [? [Hxs ->]]]]]]]". destruct xs' as [| x xx].
      { iDestruct "Hxs" as %->. wp_heap. wp_quit_loop. wp_heap.
        iModIntro. unfold append. iApply tree_of_ctx0. iFrame. }
      { iDestruct "Hxs" as (p'' v'') "[-> [Hp Hxs]]".
        wp_heap. wp_enter_loop. wp_heap.
        iPoseProof (ctx0_of_ctx0 acc (Cons' x) p' currp p'') as "H".
        iModIntro. iExists xx, _, (comp0 acc (Cons' x)), p'. iSteps. }
    + iExists _, _, (Cons' z). iSteps.
Qed.

End proof.