(** * Kip Soundness *)
(** Progress and preservation for the split development. *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Ascii.
From Stdlib Require Import Floats.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Lia.
From KipCore Require Import Syntax.
From KipCore Require Import Static.
From KipCore Require Import StaticFacts.
From KipCore Require Import Dynamic.
From KipCore Require Import DynamicFacts.
Import ListNotations.
Open Scope string_scope.

(* ================================================================= *)
(** ** Local Automation for Preservation *)
(* ================================================================= *)

(** The following tactics package recurring proof plumbing in the
    preservation section.  They are [Local] because they depend on
    lemmas proved just above and would not be meaningful outside this
    section of the file.

    - [invert_plain_type]: destructs a [has_plain_type] existential
      and inverts the inner [has_type] derivation.  This is the
      standard opening move in preservation branches.
    - [rewrite_fun_entry_signature]: uses the appropriate overload-resolution
      lemma to learn that the signature variable equals the selected entry's
      signature, then substitutes.  This avoids naming the entry or
      signature hypotheses explicitly.
    - [solve_signature_arity_contradiction]: discharges goals where
      a fully aligned (or canonicalized) argument list is claimed to
      be a partial application -- an arithmetic impossibility.
    - [rewrite_ctor_ctx]: unifies two [Sc C = Some _]
      hypotheses via [ctor_ctx_deterministic]. *)

Local Ltac invert_plain_type Hplain :=
  let kres := fresh "kres" in
  let Hty := fresh "Hty" in
  destruct Hplain as [kres Hty];
  inversion Hty; subst; clear Hty.

Local Ltac rewrite_fun_entry_signature Henv :=
  first
    [ match goal with
      | Hresolve : full_app_resolves ?Se ?Sf ?Sc ?F ?mu ?f ?args ?entry,
        Hsig : In ?sigma (?Sf ?f),
        Hcand : full_app_candidate ?Se ?Sf ?Sc ?mu ?sigma ?args |- _ =>
          let Heq_signature := fresh "Heq_signature" in
          pose proof
            (fun_entry_ctx_full_resolves_signature _ _ _ _ _ _ _ _ _ Henv Hsig Hcand Hresolve)
            as Heq_signature;
          subst sigma
      end
    | match goal with
      | Hresolve : partial_app_resolves ?Se ?Sf ?Sc ?F ?mu ?f ?args ?entry ?indices,
        Hsig : In ?sigma (?Sf ?f),
        Hcand : partial_app_candidate ?Se ?Sf ?Sc ?mu ?sigma ?args ?indices_typed |- _ =>
          let Heq_signature := fresh "Heq_signature" in
          pose proof
            (fun_entry_ctx_partial_resolves_signature _ _ _ _ _ _ _ _ _ _ _ Henv Hsig Hcand Hresolve)
            as Heq_signature;
          subst sigma
      end ].

Local Ltac destruct_typed_full_app_resolves Henv :=
  first
    [ lazymatch goal with
      | Hstep : full_app_resolves ?Se ?Sf ?Sc ?F ?mu ?f ?args ?entry_runtime,
        Hsig : In ?sigma (?Sf ?f),
        Hmode : ?Se ?f = true -> ?mu = Eff,
        Hlen_theta : Datatypes.length ?theta = Datatypes.length (signature_tvars ?sigma),
        Halign : align_cases (extract_cases (signature_params ?sigma)) ?args ?args_aligned,
        Htyped_args : Forall2 ?R ?args_aligned (signature_params ?sigma) |- _ =>
          let entry_typed := fresh "entry_typed" in
          let Hresolve_typed := fresh "Hresolve_typed" in
          let Hifc := fresh "Hifc" in
          destruct (typed_full_app_resolves Se Sf Sc F mu f sigma theta args args_aligned
            Henv Hsig Hmode Hlen_theta Halign Htyped_args)
            as [entry_typed [Hresolve_typed Hifc]]
      end
    | lazymatch goal with
      | Hstep : partial_app_resolves ?Se ?Sf ?Sc ?F ?mu ?f ?args ?entry_runtime ?indices_runtime,
        Hsig : In ?sigma (?Sf ?f),
        Hmode : ?Se ?f = true -> ?mu = Eff,
        Hlen_theta : Datatypes.length ?theta = Datatypes.length (signature_tvars ?sigma),
        Halign : align_cases (extract_cases (signature_params ?sigma)) ?args ?args_aligned,
        Htyped_args : Forall2 ?R ?args_aligned (signature_params ?sigma) |- _ =>
          let entry_typed := fresh "entry_typed" in
          let Hresolve_typed := fresh "Hresolve_typed" in
          let Hifc := fresh "Hifc" in
          destruct (typed_full_app_resolves Se Sf Sc F mu f sigma theta args args_aligned
            Henv Hsig Hmode Hlen_theta Halign Htyped_args)
            as [entry_typed [Hresolve_typed Hifc]]
      end ].

Local Ltac destruct_typed_partial_app_resolves Henv :=
  first
    [ lazymatch goal with
      | Hstep : full_app_resolves ?Se ?Sf ?Sc ?F ?mu ?f ?args ?entry_runtime,
        Hsig : In ?sigma (?Sf ?f),
        Hmode : ?Se ?f = true -> ?mu = Eff,
        Hlen_theta : Datatypes.length ?theta = Datatypes.length (signature_tvars ?sigma),
        Hlt : Datatypes.length ?args < Datatypes.length (signature_params ?sigma),
        Hmatch : match_partial
          (extract_cases (signature_params ?sigma))
          (extract_cases ?args)
          ?indices,
        Htyped_args : Forall2 ?R ?args ?indices |- _ =>
          let entry_typed := fresh "entry_typed" in
          let Hresolve_typed := fresh "Hresolve_typed" in
          let Hifc := fresh "Hifc" in
          destruct (typed_partial_app_resolves Se Sf Sc F mu f sigma theta args indices
            Henv Hsig Hmode Hlen_theta Hlt Hmatch Htyped_args)
            as [entry_typed [Hresolve_typed Hifc]]
      end
    | lazymatch goal with
      | Hstep : partial_app_resolves ?Se ?Sf ?Sc ?F ?mu ?f ?args ?entry_runtime ?indices_runtime,
        Hsig : In ?sigma (?Sf ?f),
        Hmode : ?Se ?f = true -> ?mu = Eff,
        Hlen_theta : Datatypes.length ?theta = Datatypes.length (signature_tvars ?sigma),
        Hlt : Datatypes.length ?args < Datatypes.length (signature_params ?sigma),
        Hmatch : match_partial
          (extract_cases (signature_params ?sigma))
          (extract_cases ?args)
          ?indices,
        Htyped_args : Forall2 ?R ?args ?indices |- _ =>
          let entry_typed := fresh "entry_typed" in
          let Hresolve_typed := fresh "Hresolve_typed" in
          let Hifc := fresh "Hifc" in
          destruct (typed_partial_app_resolves Se Sf Sc F mu f sigma theta args indices
            Henv Hsig Hmode Hlen_theta Hlt Hmatch Htyped_args)
            as [entry_typed [Hresolve_typed Hifc]]
      end ].

Local Ltac destruct_progress_full_app_resolves Se Sf Sc F Henv :=
  lazymatch goal with
  | Hsig : In ?sigma (?Sf ?f),
    Hmode : ?Se ?f = true -> ?mu = Eff,
    Hlen_theta : Datatypes.length ?theta = Datatypes.length (signature_tvars ?sigma),
    Halign : align_cases (extract_cases (signature_params ?sigma)) ?args ?args_aligned,
    Htyped_args : Forall2 ?R ?args_aligned (signature_params ?sigma) |- _ =>
      let entry := fresh "entry" in
      let Hresolve := fresh "Hresolve" in
      let Hsignature := fresh "Hsignature" in
      destruct (typed_full_app_resolves Se Sf Sc F mu f sigma theta args args_aligned
        Henv Hsig Hmode Hlen_theta Halign Htyped_args)
        as [entry [Hresolve Hsignature]]
  end.

Local Ltac destruct_progress_partial_app_resolves Se Sf Sc F Henv :=
  lazymatch goal with
  | Hsig : In ?sigma (?Sf ?f),
    Hmode : ?Se ?f = true -> ?mu = Eff,
    Hlen_theta : Datatypes.length ?theta = Datatypes.length (signature_tvars ?sigma),
    Hlt : Datatypes.length ?args < Datatypes.length (signature_params ?sigma),
    Hmatch : match_partial
      (extract_cases (signature_params ?sigma))
      (extract_cases ?args)
      ?indices,
    Htyped_args : Forall2 ?R ?args ?indices |- _ =>
      let entry := fresh "entry" in
      let Hresolve := fresh "Hresolve" in
      let Hsignature := fresh "Hsignature" in
      destruct (typed_partial_app_resolves Se Sf Sc F mu f sigma theta args indices
        Henv Hsig Hmode Hlen_theta Hlt Hmatch Htyped_args)
        as [entry [Hresolve Hsignature]]
  end.

Local Ltac solve_signature_arity_contradiction :=
  exfalso;
  first [ eapply aligned_signature_args_not_partial; eassumption
        | eapply canonical_signature_args_not_partial; eassumption ].

Local Ltac solve_align_length :=
  eapply align_cases_length; eauto.

Local Ltac solve_canonical_args :=
  apply canonical_args_refl; solve_align_length.

Local Ltac solve_value_payloads :=
  eapply value_payloads_combine; [eauto | solve_align_length].

Local Ltac rewrite_ctor_ctx :=
  match goal with
  | Hsig : ?Sc ?C = Some ?sigma,
    Hsig_step : ?Sc ?C = Some ?sigma' |- _ =>
      let Heq_signature := fresh "Heq_signature" in
      pose proof
        (ctor_ctx_deterministic Sc C sigma sigma' Hsig Hsig_step)
        as Heq_signature;
      subst sigma'
  end.

Local Ltac pose_canonical_args_from_alignment :=
  lazymatch goal with
  | Halign : align_cases ?expected ?args ?args_aligned |- _ =>
      let canon := fresh "canon" in
      let Hcanon := fresh "Hcanon" in
      set (canon := combine args_aligned expected);
      assert (Hcanon : canonical_args expected args = Some canon)
        by (unfold canonical_args, canon; rewrite Halign; reflexivity)
  end.

Local Ltac unfold_local_bounds :=
  repeat match goal with
  | bound := combine _ _ |- _ => unfold bound in *
  end.

(** The main semantic-value lemma is proved by induction on an explicit size
    bound.  This avoids a fragile recursive proof over the typing or value
    derivations while still supporting recursive reasoning about value
    payload lists. *)
Lemma value_has_semantic_value_le :
  forall n Se Sf Sc F mu v tau,
    expr_size v <= n ->
    fun_entry_ctx_ok Se Sf Sc F ->
    value F Sc (Se:=Se) (Sf:=Sf) (mu:=mu) v ->
    has_plain_type Se Sf Sc [] mu v tau ->
    semantic_value Se Sf Sc mu tau v.
Proof.
  induction n as [|n IH]; intros Se Sf Sc F mu v tau Hsize Henv Hv Hplain.
  - destruct Hv; simpl in Hsize; lia.
  - destruct Hv.
    + destruct Hplain as [kres Hty].
      inversion Hty; subst.
      constructor.
    + destruct Hplain as [kres Hty].
      inversion Hty; subst.
      rewrite_ctor_ctx.
      match goal with
      | H : canonical_args (extract_cases (signature_params sigma)) args = Some args |- _ =>
          pose proof H as Hcanon_args
      end.
      match goal with
      | H : length theta = length (signature_tvars sigma) |- _ =>
          pose proof H as Hlen_theta
      end.
      match goal with
      | H : align_cases (extract_cases (signature_params sigma)) args args_aligned |- _ =>
          pose proof H as Halign_typed
      end.
      match goal with
      | H : Forall2 _ args_aligned (signature_params sigma) |- _ =>
          pose proof H as Htyped_args
      end.
      match goal with
      | H : Forall _ args |- _ =>
          pose proof H as Hvalue_args
      end.
      pose proof (typed_args_plain Se Sf Sc [] mu
        (combine (signature_tvars sigma) (List.map snd theta))
        args_aligned (signature_params sigma) Htyped_args) as Hargs_plain.
      pose proof (canonical_args_payload_eq
        (extract_cases (signature_params sigma)) args args_aligned args
        Halign_typed Hcanon_args) as Hpayloads_eq.
      pose proof (canonical_args_payloads
        (extract_cases (signature_params sigma)) args Hcanon_args) as Hcanon_align.
      pose proof (canonical_args_as_combine
        (extract_cases (signature_params sigma)) args (List.map fst args) args
        Hcanon_align Hcanon_args) as Hargs_canon.
      pose proof (value_labeled_args_payloads Se Sf F Sc mu args Hvalue_args)
        as Hpayload_values.
      rewrite <- Hpayloads_eq in Hargs_plain.
      rewrite Hargs_canon.
      clear Htyped_args Halign_typed Hpayloads_eq Hargs_canon.
      assert (Hsemantic_payloads :
        Forall2 (fun arg param =>
          semantic_value Se Sf Sc mu
            (apply_subst (combine (signature_tvars sigma) (List.map snd theta))
              (fst param))
            arg)
          (List.map fst args) (signature_params sigma)).
      {
        assert (Hpayload_sem :
          forall (payloads : list expr) (params : list signature_param),
            (forall arg, In arg payloads -> expr_size arg <= n) ->
            Forall (value F Sc (Se:=Se) (Sf:=Sf) (mu:=mu)) payloads ->
            Forall2 (fun arg (param : signature_param) =>
              has_plain_type Se Sf Sc [] mu arg
                (apply_subst (combine (signature_tvars sigma) (List.map snd theta))
                  (fst param)))
              payloads params ->
            Forall2 (fun arg (param : signature_param) =>
              semantic_value Se Sf Sc mu
                (apply_subst (combine (signature_tvars sigma) (List.map snd theta))
                  (fst param))
                arg)
              payloads params).
        {
          intros payloads params Hbound Hpayload_values0 Hpayload_plain.
          revert Hbound Hpayload_values0.
          induction Hpayload_plain as [|arg param payloads params Harg_plain Hrest IHpayload];
            intros Hbound Hpayload_values0.
          - inversion Hpayload_values0; constructor.
          - inversion Hpayload_values0 as [|arg0 payloads0 Hv_arg Hpayload_values']; subst.
            constructor.
            + eapply IH.
              * apply Hbound. left. reflexivity.
              * exact Henv.
              * exact Hv_arg.
              * exact Harg_plain.
            + eapply IHpayload; eauto.
              intros arg' Hin. apply Hbound. right. exact Hin.
        }
        eapply Hpayload_sem
          with (payloads := List.map fst args)
               (params := signature_params sigma); eauto.
        intros arg Hin.
        apply in_map_iff in Hin as [[arg0 c0] [Harg_eq Hin_args]].
        subst arg.
        pose proof (in_sum_map_le (expr * case_label)
          (fun p => expr_size (fst p)) args (arg0, c0) Hin_args) as Harg_size.
        simpl in Hsize. lia.
      }
      eapply SV_Ctor with (sigma := sigma) (theta := theta)
        (args_aligned := List.map fst args).
      * exact H.
      * exact Hlen_theta.
      * exact Hcanon_align.
      * exact Hsemantic_payloads.
    + destruct Hplain as [kres Hty].
      inversion Hty; subst.
      * match goal with
        | H : partial_app_resolves Se Sf Sc F mu f args entry indices |- _ =>
            pose proof H as Hresolve
        end.
        match goal with
        | H : In sigma (Sf f) |- _ =>
            pose proof H as Hsig_typed
        end.
        match goal with
        | H : (Se f = true -> mu = Eff) |- _ =>
            pose proof H as Hmode_typed
        end.
        match goal with
        | H : length theta = length (signature_tvars sigma) |- _ =>
            pose proof H as Hlen_typed
        end.
        match goal with
        | H : align_cases (extract_cases (signature_params sigma)) args args_aligned |- _ =>
            pose proof H as Halign_typed
        end.
        match goal with
        | H : Forall2 _ args_aligned (signature_params sigma) |- _ =>
            pose proof H as Htyped_args
        end.
        destruct (fun_entry_ctx_complete_entry _ _ _ _ _ _ Henv Hsig_typed)
          as [entry_sigma [Hin_sigma Hiface_sigma]].
        pose proof (fun_entry_ctx_entry_monomorphic _ _ _ _ _ _ Henv Hin_sigma) as Hmono_entry.
        assert (Hmono_sigma : monomorphic_signature sigma).
        {
          rewrite <- Hiface_sigma.
          exact Hmono_entry.
        }
        assert (Hcand : full_app_candidate Se Sf Sc mu sigma args)
          by (eapply typed_full_app_candidate_mono; eauto).
        exfalso.
        eapply full_candidate_not_partial_resolved; eauto.
      * match goal with
        | H : In sigma (Sf f) |- _ =>
            pose proof H as Hsig_typed
        end.
        match goal with
        | H : (Se f = true -> mu = Eff) |- _ =>
            pose proof H as Hmode_typed
        end.
        match goal with
        | H : length theta = length (signature_tvars sigma) |- _ =>
            pose proof H as Hlen_typed
        end.
        match goal with
        | H : length args < length (signature_params sigma) |- _ =>
            pose proof H as Hlt
        end.
        match goal with
        | H : match_partial _ _ _ |- _ =>
            pose proof H as Hmatch_partial
        end.
        match goal with
        | H : Forall2 _ args ?indices_typed |- _ =>
            pose proof H as Htyped_args
        end.
        match goal with
        | H : Forall _ args |- _ =>
            pose proof H as Hvalue_args
        end.
        assert (Hsemantic_args_gen :
          forall (args' : list (expr * case_label)) indices',
            (forall arg, In arg args' -> expr_size (fst arg) <= n) ->
            Forall2 (fun arg idx =>
              exists param kres_i,
                nth_error (signature_params sigma) idx = Some param /\
                has_type Se Sf Sc [] mu (fst arg)
                  (apply_subst (combine (signature_tvars sigma) (List.map snd theta))
                    (fst param), kres_i))
              args' indices' ->
            Forall (fun p : expr * case_label =>
              value F Sc (Se:=Se) (Sf:=Sf) (mu:=mu) (fst p)) args' ->
            Forall2 (fun arg idx =>
              exists param,
                nth_error (signature_params sigma) idx = Some param /\
                semantic_value Se Sf Sc mu
                  (apply_subst (combine (signature_tvars sigma) (List.map snd theta))
                    (fst param))
                  (fst arg))
              args' indices').
        {
          intros args' indices' Hbound Htyped_args' Hvalue_args'.
          revert Hbound Hvalue_args'.
          induction Htyped_args' as [|[arg c] idx args'' idxs'' Hhead Hrest IHargs];
            intros Hbound Hvalue_args'.
          - inversion Hvalue_args'; constructor.
          - inversion Hvalue_args' as [|[arg0 c0] args0 Hv_arg Hvalue_args'']; subst.
            constructor.
            + destruct Hhead as [param [kres_i [Hnth Harg]]].
              exists param; split; [exact Hnth|].
              eapply IH.
              * apply Hbound. left. reflexivity.
              * exact Henv.
              * exact Hv_arg.
              * apply has_type_plain in Harg. exact Harg.
            + eapply IHargs; eauto.
              intros arg' Hin. apply Hbound. right. exact Hin.
        }
        lazymatch type of Htyped_args with
        | Forall2 _ _ ?indices_typed =>
            assert (Hsemantic_args :
              Forall2 (fun arg idx =>
                exists param,
                  nth_error (signature_params sigma) idx = Some param /\
                  semantic_value Se Sf Sc mu
                    (apply_subst (combine (signature_tvars sigma) (List.map snd theta))
                      (fst param))
                    (fst arg))
                args indices_typed)
        end.
        {
          eapply Hsemantic_args_gen; eauto.
          intros arg Hin.
          pose proof (in_sum_map_le (expr * case_label)
            (fun p => expr_size (fst p)) args arg Hin) as Harg_size.
          simpl in Hsize. lia.
        }
        eapply SV_PartialApp with (sigma := sigma) (theta := theta); eauto.
Qed.

(** Every closed dynamic value inhabits the corresponding semantic-value
    relation.  This connects the operational [value] judgment used by
    progress with the semantic exhaustiveness predicates used by [T_App] and
    [T_Match]. *)
Lemma value_has_semantic_value :
  forall Se Sf Sc F mu v tau,
    fun_entry_ctx_ok Se Sf Sc F ->
    value F Sc (Se:=Se) (Sf:=Sf) (mu:=mu) v ->
    has_plain_type Se Sf Sc [] mu v tau ->
    semantic_value Se Sf Sc mu tau v.
Proof.
  intros Se Sf Sc F mu v tau Henv Hv Hplain.
  eapply value_has_semantic_value_le with (n := expr_size v); eauto.
Qed.

(** Pointwise lifting of [value_has_semantic_value] across payload lists. *)
Lemma plain_value_payloads_semantic :
  forall Se Sf Sc F mu payloads params,
    fun_entry_ctx_ok Se Sf Sc F ->
    Forall (value F Sc (Se:=Se) (Sf:=Sf) (mu:=mu)) payloads ->
    Forall2 (fun arg (param : signature_param) =>
      has_plain_type Se Sf Sc [] mu arg (fst param))
      payloads params ->
    Forall2 (fun arg (param : signature_param) =>
      semantic_value Se Sf Sc mu (fst param) arg)
      payloads params.
Proof.
  intros Se Sf Sc F mu payloads params Henv Hpayload_values Hplain_payloads.
  revert Hpayload_values.
  induction Hplain_payloads as [|arg param payloads params Harg_plain Hrest IH];
    intros Hpayload_values.
  - inversion Hpayload_values; constructor.
  - inversion Hpayload_values as [|arg0 payloads0 Hv_arg Hpayload_values']; subst.
    constructor.
    + eapply value_has_semantic_value; eauto.
    + eapply IH; eauto.
Qed.

(* ================================================================= *)
(** ** Progress and Preservation *)
(* ================================================================= *)

(** *** Progress *)

(** Every well-typed closed expression is either a value or can step.

    The proof proceeds by fixpoint induction on the typing derivation
    ([fix Hprog 5]).  The most interesting cases are:
    - [T_App] (full application): canonicalize the arguments, then
      either all argument payloads are values (use semantic clause
      exhaustiveness to beta-reduce), or some argument can step
      (payload congruence).
    - [T_App_Partial]: all arguments are values (return a partial
      application value), or some argument can step.
    - [T_Ctor]: same structure as [T_App] but without beta-reduction.

    The argument-progress sub-proofs use nested fixpoint inductions
    ([fix Hpayloads_gen] / [fix Hargs_gen]) because the argument
    lists carry [Forall2]-structured typing evidence that standard
    [induction] cannot recurse into.  A future refactor could extract
    these as standalone lemmas parameterized by the progress IH. *)

Theorem progress :
  forall Se Sf Sc F mu e tau,
    fun_entry_ctx_ok Se Sf Sc F ->
    has_plain_type Se Sf Sc [] mu e tau ->
    value F Sc (Se:=Se) (Sf:=Sf) (mu:=mu) e \/
    exists e', step F Sc (Se:=Se) (Sf:=Sf) (mu:=mu) e e'.
Proof.
  intros Se Sf Sc F mu e tau Henv [kres Hty].
  assert (Hprog :
    forall mu0 e0 tau0 kres0,
      has_type Se Sf Sc [] mu0 e0 (tau0, kres0) ->
      value F Sc (Se:=Se) (Sf:=Sf) (mu:=mu0) e0 \/
      exists e', step F Sc (Se:=Se) (Sf:=Sf) (mu:=mu0) e0 e').
  {
    fix Hprog 5.
    intros mu0 e0 tau0 kres0 Hderiv.
    remember [] as Gamma eqn:Hnil in Hderiv.
    destruct Hderiv; inversion Hnil; subst.
    - inversion H.
    - left. constructor.
    - destruct (Hprog _ _ _ _ Hderiv) as [Hv | [e' Hstep]].
      + right. eexists. eapply ST_Ascribe_Value; eauto.
      + right. eexists. eapply ST_Ascribe; eauto.
    - destruct_progress_full_app_resolves Se Sf Sc F Henv.
      set (expected := extract_cases (signature_params sigma)).
      pose_canonical_args_from_alignment.
      destruct (list_eq_dec labeled_expr_eq_dec args canon) as [Heqargs|Hneqargs].
      + subst args.
        match goal with
        | Htyped_args : Forall2 _ args_aligned (signature_params sigma) |- _ =>
            assert (Hpayloads :
              value_payloads F Sc (Se:=Se) (Sf:=Sf) (mu:=mu0) args_aligned \/
              exists payloads', step_exprs F Sc (Se:=Se) (Sf:=Sf) (mu:=mu0) args_aligned payloads')
        end.
        {
          clear Hcanon.
          unfold value_payloads in *.
          assert (Hpayloads_gen :
            forall es (params : list signature_param),
              Forall2 (fun arg (param : signature_param) =>
                exists kres_i,
                  has_type Se Sf Sc [] mu0 arg
                    (apply_subst bound (fst param), kres_i))
                es params ->
              Forall (value F Sc (Se:=Se) (Sf:=Sf) (mu:=mu0)) es \/
              exists payloads', step_exprs F Sc (Se:=Se) (Sf:=Sf) (mu:=mu0) es payloads').
          {
            fix Hpayloads_gen 3.
            intros es params Hargs.
            destruct Hargs as [|arg param es' params' Hex Hrest].
            - left. constructor.
            - destruct Hex as [kres_i Harg].
              destruct (Hprog _ _ _ _ Harg) as [Hvarg | [arg' Hsteparg]].
              + destruct (Hpayloads_gen es' params' Hrest) as [Hvrest | [rest' Hsteprest]];
                  [left; constructor; eauto | right; eexists; eapply SE_There; eauto].
              + right. eexists. eapply SE_Here; eauto.
          }
          match goal with
          | Htyped_args : Forall2 _ args_aligned (signature_params sigma) |- _ =>
              exact (Hpayloads_gen args_aligned (signature_params sigma) Htyped_args)
          end.
        }
        destruct Hpayloads as [Hvargs | [payloads' Hsteppayloads]].
        * pose proof Hresolve as Hresolve_entry.
          destruct Hresolve_entry as [Hentry [_ _]].
          pose proof (fun_entry_ctx_entry_monomorphic _ _ _ _ _ _ Henv Hentry) as Hmono_entry.
          assert (Hmono_sigma : monomorphic_signature sigma).
          { rewrite <- Hsignature. exact Hmono_entry. }
          match goal with
          | Htyped_args : Forall2 _ args_aligned (signature_params sigma) |- _ =>
              pose proof (typed_args_plain Se Sf Sc [] mu0
                (combine (signature_tvars sigma) (List.map snd theta))
                args_aligned (signature_params sigma) Htyped_args) as Hargs_plain
          end.
          rewrite (monomorphic_bound_nil sigma theta Hmono_sigma) in Hargs_plain.
          pose proof (Forall2_plain_subst_nil Se Sf Sc [] mu0
            args_aligned (signature_params sigma) Hargs_plain) as Hargs_plain_mono.
          assert (Hsemantic_payloads :
            Forall2 (fun arg param =>
              semantic_value Se Sf Sc mu0 (fst param) arg)
              args_aligned (signature_params sigma)).
          {
            match goal with
            | Halign : align_cases (extract_cases (signature_params sigma)) _ args_aligned |- _ =>
                pose proof (value_payloads_combine Se Sf F Sc mu0 args_aligned expected
                  Hvargs (align_cases_length _ _ _ _ Halign)) as Hvcanon
            end.
            pose proof (value_labeled_args_payloads Se Sf F Sc mu0
              (combine args_aligned expected) Hvcanon) as Hpayload_values.
            clear Hvcanon.
            eapply plain_value_payloads_semantic; eauto.
          }
          match goal with
          | Halign : align_cases (extract_cases (signature_params sigma)) _ args_aligned |- _ =>
              pose proof (semantic_value_payloads_combine Se Sf Sc mu0
                args_aligned expected (signature_params sigma)
                Hsemantic_payloads (align_cases_length _ _ _ _ Halign)) as Hsemantic_args
          end.
          match goal with
          | Hmode : Se f = true -> mu0 = Eff |- _ =>
              pose proof (fun_entry_ctx_entry_exhaustive _ _ _ _ _ _ _ Henv Hentry Hmode)
                as Hexhaustive
          end.
          rewrite Hsignature in Hexhaustive.
          destruct (Hexhaustive (combine args_aligned expected)) as [cl [rho [Hincl Hmatchcl]]].
          -- solve_canonical_args.
          -- eapply Forall2_semantic_subst_nil. exact Hsemantic_args.
          -- right.
             exists (subst_env rho (clause_body cl)).
             assert (Hmatchcl_entry :
               clause_matches Sc (fun_entry_signature entry) cl canon rho).
             { rewrite Hsignature. exact Hmatchcl. }
             eapply ST_App_Beta with (entry := entry) (cl := cl) (rho := rho); eauto.
             ++ rewrite Hsignature. exact Hcanon.
             ++ solve_value_payloads.
        * right.
          rewrite <- Hsignature in Hcanon.
          exists (EApp f (combine payloads'
            (extract_cases (signature_params (fun_entry_signature entry))))).
          eapply ST_App_Arg with (entry := entry); eauto.
          unfold canon.
          rewrite map_fst_combine; [exact Hsteppayloads | solve_align_length].
      + right.
        exists (EApp f canon).
        eapply ST_App_Canon with (entry := entry); eauto.
      rewrite Hsignature. exact Hcanon.
    - destruct_progress_partial_app_resolves Se Sf Sc F Henv.
      match goal with
      | Htyped_args : Forall2 _ args indices |- _ =>
          assert (Hargs :
            value_labeled_args F Sc (Se:=Se) (Sf:=Sf) (mu:=mu0) args \/
            exists args', step_args F Sc (Se:=Se) (Sf:=Sf) (mu:=mu0) args args')
      end.
      {
        unfold value_labeled_args in *.
        assert (Hargs_gen :
          forall args0 idxs,
            Forall2 (fun arg idx =>
              exists param kres_i,
                nth_error (signature_params sigma) idx = Some param /\
                has_type Se Sf Sc [] mu0 (fst arg)
                  (apply_subst bound (fst param), kres_i))
              args0 idxs ->
            Forall (fun p => value F Sc (Se:=Se) (Sf:=Sf) (mu:=mu0) (fst p)) args0 \/
            exists args', step_args F Sc (Se:=Se) (Sf:=Sf) (mu:=mu0) args0 args').
        {
          fix Hargs_gen 3.
          intros args0 idxs Htyped_args.
          destruct Htyped_args as [|[arg c] idx args' idxs' Hhead Hrest].
          - left. constructor.
          - destruct Hhead as [param [kres_i [Hnth Harg]]].
            destruct (Hprog _ _ _ _ Harg) as [Hvarg | [arg' Hsteparg]].
            + destruct (Hargs_gen args' idxs' Hrest) as [Hvrest | [rest' Hsteprest]].
              * left. constructor; simpl; eauto.
              * right. eexists. eapply SA_There; eauto.
            + right. eexists. eapply SA_Here; eauto.
        }
        match goal with
        | Htyped_args : Forall2 _ args indices |- _ =>
            exact (Hargs_gen args indices Htyped_args)
        end.
      }
      destruct Hargs as [Hvargs | [args' Hstepargs]].
      + left. eapply V_PartialApp with (entry := entry) (indices := indices); eauto.
      + right. eexists. eapply ST_App_Partial_Arg with (entry := entry) (indices := indices); eauto.
    - set (expected := extract_cases (signature_params sigma)).
      pose_canonical_args_from_alignment.
      destruct (list_eq_dec labeled_expr_eq_dec args canon) as [Heqargs|Hneqargs].
      + subst args.
        match goal with
        | Htyped_args : Forall2 _ args_aligned (signature_params sigma) |- _ =>
            assert (Hpayloads :
              value_payloads F Sc (Se:=Se) (Sf:=Sf) (mu:=mu0) args_aligned \/
              exists payloads', step_exprs F Sc (Se:=Se) (Sf:=Sf) (mu:=mu0) args_aligned payloads')
        end.
        {
          clear Hcanon.
          unfold value_payloads in *.
          assert (Hpayloads_gen :
            forall es (params : list signature_param),
              Forall2 (fun arg (param : signature_param) =>
                exists kres_i,
                  has_type Se Sf Sc [] mu0 arg
                    (apply_subst bound (fst param), kres_i))
                es params ->
              Forall (value F Sc (Se:=Se) (Sf:=Sf) (mu:=mu0)) es \/
              exists payloads', step_exprs F Sc (Se:=Se) (Sf:=Sf) (mu:=mu0) es payloads').
          {
            fix Hpayloads_gen 3.
            intros es params Hargs.
            destruct Hargs as [|arg param es' params' Hex Hrest].
            - left. constructor.
            - destruct Hex as [kres_i Harg].
              destruct (Hprog _ _ _ _ Harg) as [Hvarg | [arg' Hsteparg]].
              + destruct (Hpayloads_gen es' params' Hrest) as [Hvrest | [rest' Hsteprest]];
                  [left; constructor; eauto | right; eexists; eapply SE_There; eauto].
              + right. eexists. eapply SE_Here; eauto.
          }
          match goal with
          | Htyped_args : Forall2 _ args_aligned (signature_params sigma) |- _ =>
              exact (Hpayloads_gen args_aligned (signature_params sigma) Htyped_args)
          end.
        }
      destruct Hpayloads as [Hvargs | [payloads' Hsteppayloads]].
        * left. eapply V_Ctor with (sigma := sigma).
          -- eauto.
          -- solve_canonical_args.
          -- solve_value_payloads.
        * right.
          exists (ECtor C (combine payloads' expected)).
          eapply ST_Ctor_Arg with (sigma := sigma).
          -- eauto.
          -- solve_canonical_args.
          -- unfold canon.
             rewrite map_fst_combine.
             ++ eauto.
             ++ solve_align_length.
      + right.
        exists (ECtor C canon).
        eapply ST_Ctor_Canon with (sigma := sigma); eauto.
    - destruct (Hprog _ _ _ _ Hderiv) as [Hv | [scrut' Hstep]].
      + pose proof (has_type_plain Se Sf Sc [] mu0 es tau_s kres_s Hderiv) as Hscrut_plain.
        pose proof (value_has_semantic_value Se Sf Sc F mu0 es tau_s
          Henv Hv Hscrut_plain) as Hsemantic_scrut.
        match goal with
        | Hexhaustive : branches_exhaustive Se Sf Sc mu0 tau_s branches |- _ =>
            destruct (Hexhaustive es Hsemantic_scrut) as [p [body [rho [Hin Hmatch]]]]
        end.
        right. eexists. eapply ST_Match_Branch; eauto.
      + right. eexists. eapply ST_Match_Scrut; eauto.
    - destruct (Hprog mu0 e1 tau1 kres1 Hderiv1) as [Hv1 | [e1' Hstep1]].
      + right. eexists. eapply ST_Let_Value; eauto.
      + right. eexists. eapply ST_Let_Left; eauto.
    - destruct (Hprog Eff e1 tau1 kres1 Hderiv1) as [Hv1 | [e1' Hstep1]].
      + right. eexists. eapply ST_Seq_Value; eauto.
      + right. eexists. eapply ST_Seq_Left; eauto.
    - destruct (Hprog Eff e1 tau1 kres1 Hderiv1) as [Hv1 | [e1' Hstep1]].
      + right. eexists. eapply ST_Bind_Value; eauto.
      + right. eexists. eapply ST_Bind_Left; eauto.
  }
  exact (Hprog mu e tau kres Hty).
Qed.

(** The sequence and bind elimination rules in preservation
    repeatedly need the same inversion fact for [EBind].  Isolating
    it here keeps the final theorem branch small and stable under
    proof refactors.  The proof is a single inversion. *)
Lemma bind_body_typed :
  forall Se Sf Sc Gamma x e1 e2 tau kres,
    has_type Se Sf Sc Gamma Eff (EBind x e1 e2) (tau, kres) ->
    exists tau1 kres1,
      has_type Se Sf Sc Gamma Eff e1 (tau1, kres1) /\
      has_type Se Sf Sc (ctx_extend Gamma x tau1) Eff e2 (tau, kres).
Proof.
  intros Se Sf Sc Gamma x e1 e2 tau kres Hty;
  inversion Hty; subst; eauto.
Qed.

(** Likewise for matches: preservation only needs the typed scrutinee
    and the branch typing package carried by [T_Match]. *)
Lemma match_branches_typed :
  forall Se Sf Sc Gamma mu es branches tau kres,
    has_type Se Sf Sc Gamma mu (EMatch es branches) (tau, kres) ->
    exists tau_s kres_s,
      has_type Se Sf Sc Gamma mu es (tau_s, kres_s) /\
      branches_exhaustive Se Sf Sc mu tau_s branches /\
      Forall (fun pb =>
        exists Gamma_p tau_j kres_j,
          pat_bind Sc (fst pb) tau_s Gamma_p /\
          has_type Se Sf Sc (ctx_concat Gamma_p Gamma) mu (snd pb) (tau_j, kres_j) /\
          tau_j = tau
      ) branches.
Proof.
  intros Se Sf Sc Gamma mu es branches tau kres Hty.
  inversion Hty; subst.
  exists tau_s, kres_s.
  repeat split; eauto.
Qed.

(** ** Mutual Preservation *)

(** The main proof is packaged as a mutual induction over the three
    step relations ([step_exprs], [step_args], [step]) using the
    combined scheme [step_mutind].  The statement is intentionally
    stronger than the final [preservation] theorem: it simultaneously
    proves that stepping a payload list preserves the
    [Forall2]-structured typing evidence used by function and constructor
    applications, and that stepping a full expression preserves its plain
    type. *)
Lemma step_mutual_preservation :
  forall Se Sf Sc F mu,
    ctor_ctx_regular Sc ->
    fun_entry_ctx_ok Se Sf Sc F ->
    (forall es es' (Hs : step_exprs F Sc (Se:=Se) (Sf:=Sf) (mu:=mu) es es'),
      forall bound params,
        Forall2 (fun arg (param : signature_param) =>
          exists kres_i,
            has_type Se Sf Sc [] mu arg
              (apply_subst bound (fst param), kres_i))
        es params ->
        Forall2 (fun arg (param : signature_param) =>
          exists kres_i,
            has_type Se Sf Sc [] mu arg
              (apply_subst bound (fst param), kres_i))
        es' params) /\
    (forall args args' (Hs : step_args F Sc (Se:=Se) (Sf:=Sf) (mu:=mu) args args'),
      forall bound sigma indices,
        Forall2 (fun (arg : expr * case_label) (idx : nat) =>
          exists param kres_i,
            nth_error (signature_params sigma) idx = Some param /\
            has_type Se Sf Sc [] mu (fst arg)
              (apply_subst bound (fst param), kres_i))
        args indices ->
        Forall2 (fun (arg : expr * case_label) (idx : nat) =>
          exists param kres_i,
            nth_error (signature_params sigma) idx = Some param /\
            has_type Se Sf Sc [] mu (fst arg)
              (apply_subst bound (fst param), kres_i))
        args' indices) /\
    (forall e e' (Hs : step F Sc (Se:=Se) (Sf:=Sf) (mu:=mu) e e'),
      forall tau,
        has_plain_type Se Sf Sc [] mu e tau ->
        has_plain_type Se Sf Sc [] mu e' tau).
Proof.
  intros Se Sf Sc F mu Hregular Henv.
  refine (step_mutind F Sc Se Sf mu
    (fun es es' _ =>
      forall bound params,
        Forall2 (fun arg (param : signature_param) =>
          exists kres_i,
            has_type Se Sf Sc [] mu arg
              (apply_subst bound (fst param), kres_i))
        es params ->
        Forall2 (fun arg (param : signature_param) =>
          exists kres_i,
            has_type Se Sf Sc [] mu arg
              (apply_subst bound (fst param), kres_i))
        es' params)
    (fun args args' _ =>
      forall bound sigma indices,
        Forall2 (fun (arg : expr * case_label) (idx : nat) =>
          exists param kres_i,
            nth_error (signature_params sigma) idx = Some param /\
            has_type Se Sf Sc [] mu (fst arg)
              (apply_subst bound (fst param), kres_i))
        args indices ->
        Forall2 (fun (arg : expr * case_label) (idx : nat) =>
          exists param kres_i,
            nth_error (signature_params sigma) idx = Some param /\
            has_type Se Sf Sc [] mu (fst arg)
              (apply_subst bound (fst param), kres_i))
        args' indices)
    (fun e e' _ =>
      forall tau,
        has_plain_type Se Sf Sc [] mu e tau ->
        has_plain_type Se Sf Sc [] mu e' tau)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  - (* SE_Here: head expression steps in payload list *)
    intros e e' rest Hstep IH bound params Htyped.
    inversion Htyped as [|arg_hd param_hd es0 params0 Hhead Htail]; subst.
    constructor.
    + destruct Hhead as [kres_i Harg].
      apply has_type_plain in Harg.
      destruct (IH (apply_subst bound (fst param_hd)) Harg) as [kres_i' Harg'].
      eexists; eauto.
    + eauto.
  - (* SE_There: head is a value, rest steps *)
    intros e rest rest' Hv Hsteps IH bound params Htyped.
    inversion Htyped as [|arg_hd param_hd es0 params0 Hhead Htail]; subst.
    constructor; eauto.
  - (* SA_Here: head labeled argument steps *)
    intros e e' c rest Hstep IH bound sigma indices Htyped.
    inversion Htyped as [|[arg_hd c_hd] idx_hd args0 idxs0 Hhead Htail]; subst.
    constructor.
    + destruct Hhead as [param [kres_i [Hnth Harg]]].
      apply has_type_plain in Harg.
      destruct (IH (apply_subst bound (fst param)) Harg) as [kres_i' Harg'].
      eexists _, _. split; eauto.
    + eauto.
  - (* SA_There: head labeled arg is a value, rest steps *)
    intros e c rest rest' Hv Hsteps IH bound sigma indices Htyped.
    inversion Htyped as [|[arg_hd c_hd] idx_hd args0 idxs0 Hhead Htail]; subst.
    constructor; eauto.
  - (* ST_Ascribe: sub-expression steps under ascription *)
    intros e e' t Hstep IH tau Hplain.
    destruct Hplain as [kres Hty].
    destruct (ascription_sub_typing Se Sf Sc [] mu e t tau kres Hty)
      as [tau' [kres' [Harg [Hcompat [-> ->]]]]].
    apply has_type_plain in Harg.
    destruct (IH tau' Harg) as [kres'' Harg'].
    exists kres''; eapply T_Ascribe; eauto.
  - (* ST_Ascribe_Value: ascription of a value drops the annotation *)
    intros v t Hv tau Hplain.
    destruct Hplain as [kres Hty].
    destruct (ascription_sub_typing Se Sf Sc [] mu v t tau kres Hty)
      as [tau' [kres' [Hvty [Hcompat [-> ->]]]]].
    unfold compat in Hcompat. subst tau'.
    eauto.
  - (* ST_App_Partial_Arg: partial app with an argument stepping *)
    intros f entry args args' indices Hresolve Hsteps IHargs tau Hplain.
    invert_plain_type Hplain.
    + destruct_typed_full_app_resolves Henv.
      unfold full_app_resolves in Hresolve_typed.
      destruct Hresolve_typed as [Hentry_full [Hfull Huniq_full]].
      rewrite Hifc in Hfull.
      exfalso. eapply full_candidate_not_partial_resolved; eauto.
    + unfold partial_app_resolves in Hresolve.
      eapply partial_app_args_preserved_has_plain_type; eauto using step_args_extract_cases.
  - (* ST_App_Canon: canonicalize argument order *)
    intros f entry args args' Hresolve Hcanon Hneq tau Hplain.
    invert_plain_type Hplain.
    + match goal with
      | Hsig : In sigma (Sf f) |- _ =>
          destruct (fun_entry_ctx_complete_entry _ _ _ _ _ _ Henv Hsig)
            as [entry_sigma [Hin_sigma Hiface_sigma]]
      end.
      pose proof (fun_entry_ctx_entry_monomorphic _ _ _ _ _ _ Henv Hin_sigma) as Hmono_entry.
      assert (Hmono_sigma : monomorphic_signature sigma).
      { rewrite <- Hiface_sigma. exact Hmono_entry. }
      assert (Hcand : full_app_candidate Se Sf Sc mu sigma args).
      { eapply typed_full_app_candidate_mono; eauto. }
      rewrite_fun_entry_signature Henv.
      rewrite Heq_signature in *.
      unfold bound in *.
      rewrite Heq_signature in *.
      lazymatch goal with
      | Hsig : In (fun_entry_signature entry) (Sf ?f),
        Hmode : Se f = true -> mu = Eff,
        Hlen_theta : length theta = length (signature_tvars (fun_entry_signature entry)),
        Halign : align_cases (extract_cases (signature_params (fun_entry_signature entry))) args ?args_aligned,
        Htyped_args : Forall2 ?R args_aligned (signature_params (fun_entry_signature entry)) |- _ =>
          pose proof (canonical_args_as_combine
            (extract_cases (signature_params (fun_entry_signature entry))) args args_aligned args'
            Halign Hcanon) as Hcanon_eq;
          exists (Some (signature_return_case (fun_entry_signature entry)));
          eapply T_App with
            (sigma := fun_entry_signature entry)
            (theta := theta)
            (args_aligned := args_aligned);
            [ exact Hsig
            | exact Hmode
            | exact Hlen_theta
            | rewrite Hcanon_eq; apply align_cases_combine;
                eapply align_cases_length; exact Halign
            | exact Htyped_args ]
      end.
    + destruct_typed_partial_app_resolves Henv.
      unfold partial_app_resolves in Hresolve_typed.
      destruct Hresolve_typed as [Hentry_partial_typed [Hpartial_typed [Hnofull Huniq_partial]]].
      rewrite Hifc in Hpartial_typed.
      exfalso. eapply partial_candidate_not_full_resolved; eauto.
  - (* ST_App_Arg: payload list steps after canonicalization *)
    intros f entry args payloads' Hentry Hcanon Hsteps IHpayloads tau Hplain.
    invert_plain_type Hplain.
    + match goal with
      | Hsig : In sigma (Sf f) |- _ =>
          destruct (fun_entry_ctx_complete_entry _ _ _ _ _ _ Henv Hsig)
            as [entry_sigma [Hin_sigma Hiface_sigma]]
      end.
      pose proof (fun_entry_ctx_entry_monomorphic _ _ _ _ _ _ Henv Hin_sigma) as Hmono_entry.
      assert (Hmono_sigma : monomorphic_signature sigma).
      { rewrite <- Hiface_sigma. exact Hmono_entry. }
      assert (Hcand : full_app_candidate Se Sf Sc mu sigma args).
      { eapply typed_full_app_candidate_mono; eauto. }
      rewrite_fun_entry_signature Henv.
      rewrite Heq_signature in *.
      unfold bound in *.
      rewrite Heq_signature in *.
      lazymatch goal with
      | Halign : align_cases
          (extract_cases (signature_params (fun_entry_signature entry)))
          args ?args_aligned,
        Htyped_args : Forall2 _ args_aligned
          (signature_params (fun_entry_signature entry)) |- _ =>
          pose proof (canonical_args_payload_eq
            (extract_cases (signature_params (fun_entry_signature entry))) args args_aligned args
            Halign Hcanon) as Hargs_eq;
          rewrite Hargs_eq in IHpayloads;
          pose proof (IHpayloads
            (combine (signature_tvars (fun_entry_signature entry)) (List.map snd theta))
            (signature_params (fun_entry_signature entry)) Htyped_args) as Htyped_payloads;
          eapply app_payloads_typed_has_plain_type; eauto
      end.
    + destruct_typed_partial_app_resolves Henv.
      unfold partial_app_resolves in Hresolve_typed.
      destruct Hresolve_typed as [Hentry_partial_typed [Hpartial_typed [Hnofull Huniq_partial]]].
      rewrite Hifc in Hpartial_typed.
      exfalso. eapply partial_candidate_not_full_resolved; eauto.
  - (* ST_App_Beta: beta-reduction via a semantically matching clause *)
    intros f entry cl args rho Hentry Hcanon Hvargs Hincl Hmatch
      tau Hplain.
    invert_plain_type Hplain.
    + match goal with
      | Hsig : In sigma (Sf f) |- _ =>
          destruct (fun_entry_ctx_complete_entry _ _ _ _ _ _ Henv Hsig)
            as [entry_sigma [Hin_sigma Hiface_sigma]]
      end.
      pose proof (fun_entry_ctx_entry_monomorphic _ _ _ _ _ _ Henv Hin_sigma) as Hmono_entry.
      assert (Hmono_sigma : monomorphic_signature sigma).
      { rewrite <- Hiface_sigma. exact Hmono_entry. }
      assert (Hcand : full_app_candidate Se Sf Sc mu sigma args).
      { eapply typed_full_app_candidate_mono; eauto. }
      rewrite_fun_entry_signature Henv.
      rewrite Heq_signature in *.
      unfold bound in *.
      rewrite Heq_signature in *.
      unfold full_app_resolves in Hentry.
      destruct Hentry as [Hentry_inF [_ _]].
      pose proof (fun_entry_ctx_entry_monomorphic _ _ _ _ _ _ Henv Hentry_inF) as Hmono.
      pose proof (fun_entry_ctx_clause_core _ _ _ _ _ _ _ Henv Hentry_inF Hincl) as Hcore.
      rewrite (monomorphic_bound_nil (fun_entry_signature entry) theta Hmono).
      rewrite apply_subst_nil.
      eapply app_beta_has_plain_type; eauto.
    + destruct_typed_partial_app_resolves Henv.
      unfold partial_app_resolves in Hresolve_typed.
      destruct Hresolve_typed as [Hentry_partial_typed [Hpartial_typed [Hnofull Huniq_partial]]].
      rewrite Hifc in Hpartial_typed.
      exfalso. eapply partial_candidate_not_full_resolved; eauto.
  - (* ST_Ctor_Canon: canonicalize constructor argument order *)
    intros C sigma_step args args' Hsig_step Hcanon Hneq tau Hplain.
    invert_plain_type Hplain.
    rewrite_ctor_ctx.
    eapply canonical_ctor_has_plain_type; eauto.
  - (* ST_Ctor_Arg: constructor payload list steps *)
    intros C sigma_step args payloads' Hsig_step Hcanon Hsteps IHpayloads tau Hplain.
    invert_plain_type Hplain.
    rewrite_ctor_ctx.
    eapply ctor_payloads_preserved_has_plain_type; eauto.
  - (* ST_Match_Scrut: scrutinee steps *)
    intros scrut scrut' branches Hstep IH tau Hplain.
    destruct Hplain as [kres Hty].
    destruct (match_branches_typed Se Sf Sc [] mu scrut branches tau kres Hty)
      as [tau_s [kres_s [Hscrut [Hexhaustive Hbranches]]]].
    apply has_type_plain in Hscrut.
    destruct (IH tau_s Hscrut) as [kres_s' Hscrut'].
    exists None; eapply T_Match; eauto.
  - (* ST_Match_Branch: scrutinee is a value, reduce via a matching branch *)
    intros v branches p body rho Hv Hin Hmatch tau Hplain.
    destruct Hplain as [kres Hty].
    destruct (match_branches_typed Se Sf Sc [] mu v branches tau kres Hty)
      as [tau_s [kres_s [Hscrut [_ Hbranches]]]].
    eapply match_branch_has_plain_type; eauto.
  - (* ST_Let_Left: bound expression steps *)
    intros x e1 e1' e2 Hstep IH tau Hplain.
    invert_plain_type Hplain.
    lazymatch goal with
    | Hty1 : has_type Se Sf Sc [] mu e1 (?tau1, ?kres1),
      Hty2 : has_type Se Sf Sc (ctx_extend [] x tau1) mu e2 (tau, ?kres2) |- _ =>
        apply has_type_plain in Hty1;
        destruct (IH tau1 Hty1) as [kres1' Hty1'];
        exists kres2; eapply T_Let; eauto
    end.
  - (* ST_Let_Value: bound expression is a value, substitute into body. *)
    intros x v e2 Hv tau Hplain.
    invert_plain_type Hplain.
    lazymatch goal with
    | Hty1 : has_type Se Sf Sc [] mu v (?tau1, ?kres1),
      Hty2 : has_type Se Sf Sc (ctx_extend [] x tau1) mu e2 (tau, ?kres2) |- _ =>
        eapply subst_preserves_typing; eauto
    end.
  - (* ST_Seq_Left: left sub-expression of sequencing steps.
       We use [lazymatch] to find the typing hypotheses by their type
       structure rather than by their auto-generated names. *)
    intros e1 e1' e2 Hstep IH tau Hplain.
    invert_plain_type Hplain.
    lazymatch goal with
    | Hty1 : has_type Se Sf Sc [] Eff e1 (?tau1, ?kres1),
      Hty2 : has_type Se Sf Sc [] Eff e2 (tau, ?kres2) |- _ =>
        apply has_type_plain in Hty1;
        destruct (IH tau1 Hty1) as [kres1' Hty1'];
        exists kres2; eapply T_Seq; eauto
    end.
  - (* ST_Seq_Value: left sub-expression is a value, return right *)
    intros v e2 Hv tau Hplain.
    invert_plain_type Hplain.
    lazymatch goal with
    | Hty2 : has_type Se Sf Sc [] Eff e2 (tau, ?kres2) |- _ =>
        eauto
    end.
  - (* ST_Bind_Left: bound expression steps *)
    intros x e1 e1' e2 Hstep IH tau Hplain.
    invert_plain_type Hplain.
    lazymatch goal with
    | Hty1 : has_type Se Sf Sc [] Eff e1 (?tau1, ?kres1),
      Hty2 : has_type Se Sf Sc (ctx_extend [] x tau1) Eff e2 (tau, ?kres2) |- _ =>
        apply has_type_plain in Hty1;
        destruct (IH tau1 Hty1) as [kres1' Hty1'];
        exists kres2; eapply T_Bind; eauto
    end.
  - (* ST_Bind_Value: bound expression is a value, substitute into body.
       This is where the substitution lemma fires. *)
    intros x v e2 Hv tau Hplain.
    invert_plain_type Hplain.
    lazymatch goal with
    | Hty1 : has_type Se Sf Sc [] Eff v (?tau1, ?kres1),
      Hty2 : has_type Se Sf Sc (ctx_extend [] x tau1) Eff e2 (tau, ?kres2) |- _ =>
        eapply subst_preserves_typing; eauto
    end.
Qed.

(** *** Preservation *)

(** Standard preservation for closed expressions follows immediately
    from the expression component of [step_mutual_preservation].
    Together with [progress] above, this establishes type soundness:
    a well-typed closed expression never gets stuck. *)
Theorem preservation :
  forall Se Sf Sc F mu e e' tau,
    ctor_ctx_regular Sc ->
    fun_entry_ctx_ok Se Sf Sc F ->
    has_plain_type Se Sf Sc [] mu e tau ->
    step F Sc (Se:=Se) (Sf:=Sf) (mu:=mu) e e' ->
    has_plain_type Se Sf Sc [] mu e' tau.
Proof.
  intros Se Sf Sc F mu e e' tau Hregular Henv Hty Hstep.
  exact (proj2 (proj2 (step_mutual_preservation Se Sf Sc F mu Hregular Henv))
    e e' Hstep tau Hty).
Qed.
