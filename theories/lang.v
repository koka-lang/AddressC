(* Copyright (c) 2023 Microsoft Research, Anton Lorenzen *)

From fip_iris Require Import idents.

From iris.heap_lang Require Export proofmode class_instances.
From diaframe.heap_lang Require Export proof_automation.

From iris.proofmode Require Import intro_patterns coq_tactics reduction. 
From iris.program_logic Require Import weakestpre total_weakestpre.
From iris.heap_lang Require Import tactics.
Import interface.bi derived_laws.bi derived_laws_later.bi.

Notation "e1 == e2" := (BinOp EqOp e1%E e2%E) (at level 70, right associativity) : expr_scope.
Notation "e1 != e2" := (UnOp NegOp (BinOp EqOp e1%E e2%E)) (at level 70, right associativity) : expr_scope.
Notation "e1 < e2" := (BinOp LtOp e1%E e2%E) : expr_scope.
Notation "e1 <= e2" := (BinOp LeOp e1%E e2%E) : expr_scope.
Notation "e2 > e1" := (BinOp LtOp e1%E e2%E) : expr_scope.
Notation "e2 >= e1" := (BinOp LeOp e1%E e2%E) : expr_scope.

Notation "✲ e" := (Load e%E) (at level 30) : expr_scope.
Definition deref (e : expr) : expr := (match e with | Load e' => e' | _ => #LitPoison end).
Notation "& e" := (deref e%E) (at level 30) : expr_scope.
Notation "e1 = e2" := (Store (deref e1)%E e2%E) (at level 70) : expr_scope.
Notation "e1 <- e2" := (Store e1%E e2%E) (at level 80) : val_scope.

Definition NULL := (LitV (LitInt 0%nat)).

Notation "e1 〚 e2 〛" :=
  (Load (BinOp OffsetOp e1%E (Val (LitV (LitInt (Z.of_nat e2%E))))))
  (at level 20) : expr_scope.

Module Import Private.
Require Import Ltac2.Ltac2.

Notation "ident_to_string! x" := (
  match (fun (x : expr) => x) return String.string with y => ltac2:(
    let (lam : constr) := lazy_match! goal with [ _ := ?lam |- _ ] => lam end in
    let (s : constr) := constr_string_of_lambda lam in
    exact $s)
  end) (at level 10, only parsing).
End Private.

Notation "'var:' x := e1 'in' e2" :=
  (Lam (ident_to_string! x)%binder ((fun (x : expr) => e2%E) (Load (ident_to_string! x)%binder)) (Alloc e1%E))
  (at level 100, x at level 100, e1, e2 at level 200, right associativity,
   format "'[' 'var:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.

Notation "'var:' x := e1 'in' e2" :=
  (Lam x%binder e2%V (Alloc e1%V))
  (at level 100, x at level 100, e1, e2 at level 200, right associativity,
   format "'[' 'var:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : val_scope.

Notation "'if:' ( e1 ) { e2 } 'else' { e3 }" := (If e1%E e2%E e3%E)
  (at level 200, e1, e2, e3 at level 200) : expr_scope.

Definition while : val :=
  rec: "while" "cond" "body" :=
    if: ( "cond" #() ) {
      "body" #();;
      "while" "cond" "body"
    } else {
      #()
    }.
Notation "'while:' ( cnd ) { e }" := (while (λ: <>, cnd)%E (λ: <>, e)%E) : expr_scope. 
Notation "'while:' ( cnd ) { e }" := (while (λ: <>, cnd)%V (λ: <>, e)%V) : var_scope.
Notation "'repeat:' { e } 'until:' ( cnd )" := (Lam BAnon (while (λ: <>, ~ cnd)%E (λ: <>, e)%E) e%E) : expr_scope.
Notation "'repeat:' { e } 'until:' ( cnd )" := (Lam BAnon (while (λ: <>, ~ cnd)%V (λ: <>, e)%V) e%V) : var_scope.

Notation "'while:' ( 'true' ) { e }" :=
   (Lam "continue" (while (λ: <>, Load "continue")%E (λ: <>, e)%E)
     (Alloc #true)) : expr_scope. 
Notation "'while:' ( 'true' ) { e }" :=
   (Lam "continue" (while (λ: <>, Load "continue")%V (λ: <>, e)%V)
     (Alloc #true)) : var_scope. 

Notation "'fun:' ( a ) { e }" :=
  (LamV (ident_to_string! a)%binder
    ((fun a =>
      e%E)
    (Load (ident_to_string! a)%binder)))
  (at level 200, a at level 1, e at level 200,
   format "'[' 'fun:' ( a ) '/  ' { e } ']'").

Notation "'fun:' ( a , b ) { e }" :=
  (LamV (ident_to_string! a)%binder
    ((fun a =>
      (Lam (ident_to_string! b)%binder
        ((fun b =>
          e%E)
        (Load (ident_to_string! b)%binder))))
    (Load (ident_to_string! a)%binder)))
  (at level 200, a, b at level 1, e at level 200,
   format "'[' 'fun:' ( a , b ) '/  ' { e } ']'").

Notation "'fun:' ( a , b , c ) { e }" :=
  (LamV (ident_to_string! a)%binder
    ((fun a =>
      (Lam (ident_to_string! b)%binder
        ((fun b =>
          (Lam (ident_to_string! c)%binder
            ((fun c =>
              e%E)
            (Load (ident_to_string! c)%binder))))
        (Load (ident_to_string! b)%binder))))
    (Load (ident_to_string! a)%binder)))
  (at level 200, a, b, c at level 1, e at level 200,
   format "'[' 'fun:' ( a , b , c ) '/  ' { e } ']'").

Notation "'fun:' ( a , b , c , d ) { e }" :=
  (LamV (ident_to_string! a)%binder
    ((fun a =>
      (Lam (ident_to_string! b)%binder
        ((fun b =>
          (Lam (ident_to_string! c)%binder
            ((fun c =>
              (Lam (ident_to_string! d)%binder
                ((fun d =>
                  e%E)
                (Load (ident_to_string! d)%binder))))
            (Load (ident_to_string! c)%binder))))
        (Load (ident_to_string! b)%binder))))
    (Load (ident_to_string! a)%binder)))
  (at level 200, a, b, c, d at level 1, e at level 200,
   format "'[' 'fun:' ( a , b , c , d ) '/  ' { e } ']'").

Notation "'fun:' ( a , b , c , d , e ) { e2 }" :=
  (LamV (ident_to_string! a)%binder
    ((fun a =>
      (Lam (ident_to_string! b)%binder
        ((fun b =>
          (Lam (ident_to_string! c)%binder
            ((fun c =>
              (Lam (ident_to_string! d)%binder
                ((fun d =>
                  (Lam (ident_to_string! e)%binder
                    ((fun e =>
                      e2%E)
                    (Load (ident_to_string! e)%binder))))
                (Load (ident_to_string! d)%binder))))
            (Load (ident_to_string! c)%binder))))
        (Load (ident_to_string! b)%binder))))
    (Load (ident_to_string! a)%binder)))
  (at level 200, a, b, c, d, e at level 1, e2 at level 200,
   format "'[' 'fun:' ( a , b , c , d , e ) '/  ' { e2 } ']'").

Notation "'ret:' e" := e%E (at level 20) : expr_scope. 

Definition break : expr :=
  ✲"continue" = #false.

(* --------- Lemmas ----------- *)

Inductive continue : Set := Stop | Continue.
Definition is_continue `{!heapGS Σ} (c : continue) (v : val) : iProp Σ :=
  match c with
  | Stop => ⌜v = #false⌝
  | Continue => ⌜v = #true⌝
  end.

Section proofs.

Local Set Default Proof Using "Type*".
Context `{!heapGS Σ}.

#[export]
Instance is_continue_stop_hint t :
HINT ε₁ ✱ [- ; ⌜t = Stop⌝] ⊫ [id]; is_continue t #false ✱ [⌜t = Stop⌝].
Proof. iSteps. Qed.

#[export]
Instance is_continue_continue_hint t :
HINT ε₁ ✱ [- ; ⌜t = Continue⌝] ⊫ [id]; is_continue t #true ✱ [⌜t = Continue⌝].
Proof. iSteps. Qed.

(* Modified from tac_wp_load *)
Lemma tac_wp_load_offset Δ Δ' s E i K b l q v off vs Φ : 
  (list_lookup off vs = Some v) →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (b, l ↦∗{q} vs )%I →
  envs_entails Δ' (WP fill K (Val v) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (Load (LitV (LitLoc (Loc.add l off)))) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> Hl ?? Hi.
  rewrite -wp_bind. eapply wand_apply; first by apply wand_entails, wp_load_offset; apply Hl.
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  apply later_mono.
  destruct b; simpl.
  * iIntros "[#$ He]". iIntros "_". iApply Hi. iApply "He". iFrame "#".
  * by apply sep_mono_r, wand_mono.
Qed.
Lemma tac_twp_load_offset Δ s E i K b l q v off vs Φ :
  (list_lookup off vs = Some v) →
  envs_lookup i Δ = Some (b, l ↦∗{q} vs)%I →
  envs_entails Δ (WP fill K (Val v) @ s; E [{ Φ }]) →
  envs_entails Δ (WP fill K (Load (LitV (LitLoc (Loc.add l off)))) @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_unseal=> Hl ? Hi.
  rewrite -twp_bind. eapply wand_apply; first by apply wand_entails, twp_load_offset; apply Hl.
  rewrite envs_lookup_split //; simpl.
  destruct b; simpl.
  - iIntros "[#$ He]". iIntros "_". iApply Hi. iApply "He". iFrame "#".
  - iIntros "[$ He]". iIntros "Hl". iApply Hi. iApply "He". iFrame "Hl".
Qed.

(* Modified from tac_wp_store *)
Lemma tac_wp_store_offset Δ Δ' s E i K l v' off vs Φ :
  (is_Some (list_lookup off vs)) →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦∗ vs)%I →
  match envs_simple_replace i false (Esnoc Enil i (l ↦∗ <[off:=v']> vs)) Δ' with
  | Some Δ'' => envs_entails Δ'' (WP fill K (Val $ LitV LitUnit) @ s; E {{ Φ }})
  | None => False
  end →
  envs_entails Δ (WP fill K (Store (LitV (LitLoc (Loc.add l off))) (Val v')) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> Hl ???.
  destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
  rewrite -wp_bind. eapply wand_apply; first by eapply wand_entails, wp_store_offset; apply Hl.
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.
Lemma tac_twp_store_offset Δ s E i K l v' off vs Φ :
  (is_Some (list_lookup off vs)) →
  envs_lookup i Δ = Some (false, l ↦∗ vs)%I →
  match envs_simple_replace i false (Esnoc Enil i (l ↦∗ list_insert off v' vs)) Δ with
  | Some Δ' => envs_entails Δ' (WP fill K (Val $ LitV LitUnit) @ s; E [{ Φ }])
  | None => False
  end →
  envs_entails Δ (WP fill K (Store (LitV (LitLoc (Loc.add l off))) v') @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_unseal. intros Hl H H0.
  destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
  rewrite -twp_bind. eapply wand_apply; first by eapply wand_entails, twp_store_offset; apply Hl.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply sep_mono_r, wand_mono.
Qed.

(* See https://gitlab.mpi-sws.org/iris/c/-/blob/master/theories/c_translation/monad.v *)
Lemma wp_while R Φ c e :
  WP (while (λ: <>, c)%V (λ: <>, e)%V) @ R {{ Φ }} -∗
  WP (while (λ: <>, c)%E (λ: <>, e)%E) @ R {{ Φ }}.
Proof. iIntros "H". wp_pures. iAssumption. Qed.

Lemma wp_whileV R Φ c e :
  ▷ WP c @ R {{ v,
      ⌜v = #true⌝ ∧ (WP e @ R {{ _, (WP while (λ: <>, c)%V (λ: <>, e)%V @ R {{ Φ }})}})
    ∨ ⌜v = #false⌝ ∧ (Φ #()) }} -∗
  WP while (λ: <>, c)%V (λ: <>, e)%V @ R {{ Φ }}.
Proof.
iIntros "H". wp_lam. wp_pures. wp_apply (wp_wand with "H"). iIntros (v) "H".
iDestruct "H" as "[[-> H]|[-> H]]".
 - wp_if. wp_pures. wp_apply (wp_wand with "H"). iIntros (v) "H". wp_seq. iAssumption.
 - wp_if. iModIntro. iAssumption. 
Qed.

Lemma wp_whileV_inv (I : iProp Σ) R (Φ : val -> iProp Σ) c e :
  □ (I -∗ WP c @ R {{ v, (⌜v = #false⌝ ∧ (Φ #())) ∨
                         (⌜v = #true⌝ ∧ WP e @ R {{ _, I }}) }}) -∗
  I -∗
  WP while (λ: <>, c)%V (λ: <>, e)%V @ R {{ Φ }}.
Proof.
iIntros "#Hinv HI". iLöb as "IH". iApply wp_whileV. iNext.
iSpecialize ("Hinv" with "HI"). iApply (wp_wand with "Hinv").
iIntros (v) "[[-> H]|[-> H]] /="; first by auto.
iLeft. iSplit; first done. iApply (wp_wand with "H").
iIntros (_) "HI". iApply "IH". iAssumption.
Qed.

Lemma wp_while_inv (I : iProp Σ) R (Φ : val -> iProp Σ) c e :
  □ (I -∗ WP c @ R {{ v, (⌜v = #false⌝ ∧ (Φ #())) ∨
                         (⌜v = #true⌝ ∧ (WP e @ R {{ _, I }})) }}) -∗
  I -∗
  WP while (λ: <>, c)%E (λ: <>, e)%E @ R {{ Φ }}.
Proof.
iIntros "#Hinv HI". iApply wp_while. by iApply (wp_whileV_inv with "Hinv HI").
Qed.

End proofs.

(* --------- Tactics ----------- *)

Tactic Notation "wp_begin" constr(x1) :=
  let phi := fresh "Φ" in
  let Hphi := iFresh in
  iIntros (phi); iIntros x1; iIntros [IIdent Hphi];
  wp_rec; wp_apply wp_wand_l; iFrame; repeat wp_lam; clear phi.

Tactic Notation "wp_begin" constr(x1) ";" ident(x2) :=
  let phi := fresh "Φ" in
  let Hphi := iFresh in
  iIntros (phi); iIntros x1; iIntros [IIdent Hphi];
  wp_alloc x2;
  wp_rec; wp_apply wp_wand_l; iFrame; repeat wp_lam; clear phi.

Tactic Notation "wp_begin" constr(x1) ";" ident(x2) "," ident(x3) :=
  let phi := fresh "Φ" in
  let Hphi := iFresh in
  iIntros (phi); iIntros x1; iIntros [IIdent Hphi];
  wp_alloc x3; wp_alloc x2;
  wp_rec; wp_apply wp_wand_l; iFrame; repeat wp_lam; clear phi.

Tactic Notation "wp_begin" constr(x1) ";" ident(x2) "," ident(x3) "," ident(x4) :=
  let phi := fresh "Φ" in
  let Hphi := iFresh in
  iIntros (phi); iIntros x1; iIntros [IIdent Hphi];
  wp_alloc x4; wp_alloc x3; wp_alloc x2;
  wp_rec; wp_apply wp_wand_l; iFrame; repeat wp_lam; clear phi.

Tactic Notation "wp_begin" constr(x1) ";" ident(x2) "," ident(x3) "," ident(x4) "," ident(x5) :=
  let phi := fresh "Φ" in
  let Hphi := iFresh in
  iIntros (phi); iIntros x1; iIntros [IIdent Hphi];
  wp_alloc x5; wp_alloc x4; wp_alloc x3; wp_alloc x2;
  wp_rec; wp_apply wp_wand_l; iFrame; repeat wp_lam; clear phi.

Tactic Notation "wp_var" ident(x) :=
  wp_alloc x; wp_let.

Tactic Notation "wp_load_offset" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦∗{_} _)%I) => l end in
    iAssumptionCore || fail "wp_load_offset: cannot find" l "↦∗ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_load_offset _ _ _ _ _ K))
      |fail 1 "wp_load_offset: cannot find 'Load #(add l n)' in" e];
    cycle 1;
    [tc_solve
    |solve_mapsto ()
    |wp_finish
    |done]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_load_offset _ _ _ _ K))
      |fail 1 "wp_load_offset: cannot find 'Load #(add l n)' in" e];
    cycle 1;
    [solve_mapsto ()
    |wp_finish
    |done]
  | _ => fail "wp_load_offset: not a 'wp'"
  end.

Tactic Notation "wp_store_offset" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦∗{_} _)%I) => l end in
    iAssumptionCore || fail "wp_store_offset: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_store_offset _ _ _ _ _ K))
      |fail 1 "wp_store_offset: cannot find 'Store' in" e];
    cycle 1;
    [tc_solve
    |solve_mapsto ()
    |pm_reduce; first [wp_seq|wp_finish]
    |done]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_store_offset _ _ _ _ K))
      |fail 1 "wp_store_offset: cannot find 'Store' in" e];
    cycle 1;
    [solve_mapsto ()
    |pm_reduce; first [wp_seq|wp_finish]
    |done]
  | _ => fail "wp_store_offset: not a 'wp'"
  end.

Tactic Notation "wp_heap" :=
  repeat ( wp_pures
        || wp_load || wp_store
        || wp_load_offset || wp_store_offset
        || let x := fresh in (wp_alloc x; try done) ).

Tactic Notation "wp_type" :=
  iSteps; try (repeat case_bool_decide; iSteps).

Tactic Notation "wp_while" constr(Hinv) :=
  wp_apply (wp_while_inv Hinv).

Tactic Notation "wp_while_true" constr(H) constr(Hstop) constr(Hloop) :=
  let c := fresh in let continue := fresh in let continuev := fresh in
  let Htmp := iFresh in let Hbind := iFresh in let Hc := iFresh in 
  let pat1 :=constr:(IList [cons (IIdent Hbind) (cons (IIdent Htmp) nil)]) in
  let pat2 :=constr:(IList [cons (IIdent Hc) (cons (IIdent H) nil)]) in
  wp_var continue; wp_apply (wp_while_inv (∃ c continuev,
      continue ↦ continuev ∗ is_continue c continuev
      ∗ (match c with
        | Stop => Hstop
        | Continue => Hloop
        end)));
  [ iModIntro; iIntros Htmp; iDestruct Htmp as (c continuev) pat1;
    iDestruct Htmp as pat2; destruct c;
    iDestruct Hc as %->; wp_heap; iModIntro; [iLeft | iRight]; (iSplit; first by done)
  | iExists Continue, _; do 2 iStep
  ].

Tactic Notation "wp_enter_loop" :=
  iModIntro; iRight; iSplit; first done.

Tactic Notation "wp_quit_loop" :=
  iModIntro; iLeft; iSplit; first done.