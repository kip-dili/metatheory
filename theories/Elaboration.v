(** * Kip Elaboration Formalization *)
(** This file formalizes a small but precise fragment of Kip's elaboration
    algorithm: overload resolution for applications after subexpressions have
    already been elaborated to core expressions and assigned types.

    The goal is not to model the full parser or type checker.  Instead, this
    layer sits between surface morphology and the split core formalization in
    [KipCore.Syntax], [KipCore.Static], [KipCore.Dynamic], and their facts
    modules:

    - surface strings are analyzed by an abstract morphology oracle;
    - each argument already carries its elaborated core expression and the
      type inferred for that expression;
    - overload selection uses the core notions of case labels, types,
      expressions, signatures, exact case alignment, and partial-application
      matching;
    - ambiguity is explicit in the result type rather than being resolved by
      "pick the first match".

    There is an important modeling distinction to keep in mind.  The split
    core development still represents applications as ordinary unresolved
    [EApp] nodes, and its declarative operational semantics uses
    [full_app_resolves] / [partial_app_resolves] to state which overload a
    step may take.  Kip itself resolves overloading during type checking.
    Consequently, this file has two layers of results:

    - coherence theorems showing that the compile-time elaborator agrees with
      the existing overloaded core semantics;
    - a small "resolved call-head" layer, added at the end of the file,
      where the chosen entry is stored directly in the term and the
      head-step relation performs no overload search.

    The resolved layer is intentionally local to call heads.  This file does
    not yet formalize full-expression elaboration, so argument expressions and
    function bodies remain ordinary core [expr] terms.  What is verified here
    is therefore that compile-time elaboration can replace the overload search
    for the elaborated call head itself.

    This file is intentionally conservative.  It reuses the core syntax and
    matching machinery, but keeps the implementation-specific morphology layer
    abstract.  That makes it a good place to state and prove meta-properties
    about determinism, sound overload choice, uniqueness of unambiguous
    resolution, and stability under irrelevant environment growth. *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Sorting.Permutation.
From Stdlib Require Import Lia.
From KipCore Require Import Syntax.
From KipCore Require Import Static.
From KipCore Require Import StaticFacts.
From KipCore Require Import Dynamic.
From KipCore Require Import DynamicFacts.
Import ListNotations.
Open Scope string_scope.

(* ================================================================= *)
(** ** Morphological Analyses *)
(* ================================================================= *)

(** A morphological analysis contributes:

    - a candidate root name that may be looked up in the overload
      environment;
    - a primary grammatical case;
    - a flag recording whether a trailing possessive [P3s] suffix was also
      present.

    The trailing possessive is modeled separately because, in the
    implementation, [P3s] is not always the only case-like clue carried by a
    surface form. *)
Record morph_analysis := mk_morph_analysis {
  (** Candidate root name produced by morphology. *)
  morph_root : string;
  (** Primary case label contributed by the analysis. *)
  morph_case : case_label;
  (** Whether the analysis also carries a trailing possessive [P3s] marker. *)
  morph_has_trailing_p3s : bool;
}.

(** The elaboration algorithm is parameterized by an abstract morphology
    oracle.  The oracle takes a surface string and returns the analyses that
    remain possible at that point in elaboration. *)
Definition morph_oracle := string -> list morph_analysis.

(** One analysis can contribute more than one case label to overload
    resolution: the primary case always contributes, and a trailing possessive
    contributes [P3s] as an additional candidate label.  Duplicates are
    removed so later enumeration does not report the same choice twice. *)
Definition morph_analysis_labels (analysis : morph_analysis) : list case_label :=
  nodup case_label_eq_dec
    (morph_case analysis ::
      if morph_has_trailing_p3s analysis then [P3s] else []).

(** The function position uses morphology only to recover candidate root
    names.  Duplicate roots are removed so overload resolution is insensitive
    to repeated analyses of the same root. *)
Definition candidate_fun_names
  (analyze : morph_oracle) (surface_name : string) : list fun_name :=
  nodup string_dec (List.map morph_root (analyze surface_name)).

(* ================================================================= *)
(** ** Surface Calls with Elaborated Arguments *)
(* ================================================================= *)

(** An elaborated argument packages:

    - the original surface string, so morphology can still supply candidate
      case labels;
    - the elaborated core expression that will eventually appear in the core
      application;
    - the type inferred for that elaborated argument.

    This is the interface between parser/type-inference details and the
    overload-resolution layer formalized here. *)
Record elaborated_arg := mk_elaborated_arg {
  (** Original surface spelling used for morphology lookup. *)
  elaborated_arg_surface : string;
  (** Elaborated core expression for the argument. *)
  elaborated_arg_expr : expr;
  (** Inferred type of the elaborated argument. *)
  elaborated_arg_ty : ty;
}.

(** The possible case labels for one elaborated argument are the union of all
    labels contributed by its morphological analyses. *)
Definition candidate_arg_cases
  (analyze : morph_oracle) (arg : elaborated_arg) : list case_label :=
  nodup case_label_eq_dec
    (List.concat (List.map morph_analysis_labels (analyze (elaborated_arg_surface arg)))).

(** A surface call records the unresolved function head together with the
    elaborated arguments whose cases still need to participate in overload
    selection. *)
Record surface_call := mk_surface_call {
  (** Surface spelling of the call head. *)
  call_surface_head : string;
  (** Elaborated arguments supplied at the call site. *)
  call_surface_args : list elaborated_arg;
}.

(* ================================================================= *)
(** ** Elaboration Environments *)
(* ================================================================= *)

(** Decidable equality for return cases is needed locally for duplicate
    elimination on signatures. *)
Lemma return_case_eq_dec :
  forall (r1 r2 : return_case), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Defined.

(** Decidable equality for signatures lets the elaboration layer deduplicate
    overload lists before classifying the result. *)
Lemma signature_eq_dec :
  forall (sigma1 sigma2 : signature), {sigma1 = sigma2} + {sigma1 <> sigma2}.
Proof.
  intros [tvars1 params1 ret1 rc1] [tvars2 params2 ret2 rc2].
  decide equality.
  - apply return_case_eq_dec.
  - apply ty_eq_dec.
  - apply (list_eq_dec (pair_eq_dec ty case_label ty_eq_dec case_label_eq_dec)).
  - apply (list_eq_dec string_dec).
Defined.

(** The elaboration environment currently needs only function contexts to
    perform overload resolution.  Constructor contexts are included as a
    field anyway so that "irrelevant constructor growth" can be stated
    directly: the current algorithm ignores this field, and the corresponding
    stability theorem makes that explicit. *)
Record elaboration_env := mk_elaboration_env {
  (** Names that are currently in scope at the call site.  This mirrors the
      implementation-side scope filter that removes candidate base names not
      present in the typing context before overload resolution. *)
  elaboration_scope : list string;
  (** Overload environment for function names. *)
  elaboration_fun_ctx : fun_ctx;
  (** Constructor environment, currently ignored by this elaboration phase. *)
  elaboration_ctor_ctx : ctor_ctx;
}.

(** The call head is filtered through the current scope before overload
    enumeration.  This formalizes the implementation behavior where a surface
    form with several possible base names is first narrowed to the names that
    are actually in context. *)
Definition scoped_candidate_fun_names
  (analyze : morph_oracle) (env : elaboration_env) (surface_name : string)
  : list fun_name :=
  List.filter
    (fun f =>
      if in_dec string_dec f (elaboration_scope env) then true else false)
    (candidate_fun_names analyze surface_name).

(** Overload enumeration is performed on duplicate-free signature lists so the
    final classifier is not affected by repeated entries in the environment. *)
Definition callable_signatures
  (env : elaboration_env) (f : fun_name) : list signature :=
  nodup signature_eq_dec (elaboration_fun_ctx env f).

(* ================================================================= *)
(** ** Enumerating Argument Labelings *)
(* ================================================================= *)

(** A labeled elaborated argument keeps the elaborated payload together with
    one concrete case choice selected from morphology. *)
Definition labeled_elaborated_arg := (elaborated_arg * case_label)%type.

(** Forget the typing payload and project a labeled argument back to the core
    argument representation used by the main formalization. *)
Definition labeled_arg_to_core (arg : labeled_elaborated_arg) : expr * case_label :=
  (elaborated_arg_expr (fst arg), snd arg).

(** Project a whole labeling to the list of core arguments that a resolved
    application would use. *)
Definition labeled_args_to_core
  (args : list labeled_elaborated_arg) : list (expr * case_label) :=
  List.map labeled_arg_to_core args.

(** Enumerate all concrete case assignments for the arguments of a surface
    call.  Each recursive branch picks one candidate case label for the head
    argument and combines it with every labeling of the tail. *)
Fixpoint enumerate_labeled_args
  (analyze : morph_oracle) (args : list elaborated_arg)
  : list (list labeled_elaborated_arg) :=
  match args with
  | [] => [[]]
  | arg :: args' =>
      flat_map
        (fun case_choice =>
          List.map
            (fun rest => (arg, case_choice) :: rest)
            (enumerate_labeled_args analyze args'))
        (candidate_arg_cases analyze arg)
  end.

(* ================================================================= *)
(** ** Boolean Match Checkers *)
(* ================================================================= *)

(** Re-express [callable_signatures] using the standalone decider above. *)
Lemma callable_signatures_eq :
  forall env f,
    callable_signatures env f =
    nodup signature_eq_dec (elaboration_fun_ctx env f).
Proof. reflexivity. Qed.

(** Check whether a list of aligned elaborated arguments has exactly the
    parameter types declared by a signature. *)
Fixpoint arg_tys_match_paramsb
  (args : list elaborated_arg) (params : list signature_param) : bool :=
  match args, params with
  | [], [] => true
  | arg :: args', param :: params' =>
      if ty_eq_dec (elaborated_arg_ty arg) (fst param)
      then arg_tys_match_paramsb args' params'
      else false
  | _, _ => false
  end.

(** This specification turns the boolean exact-type checker above into the
    [Forall2]-based relational form used by the soundness statements. *)
Lemma arg_tys_match_paramsb_spec :
  forall args params,
    arg_tys_match_paramsb args params = true <->
    Forall2 (fun arg param => elaborated_arg_ty arg = fst param) args params.
Proof.
  induction args as [|arg args IH]; intro params.
  - destruct params as [|param params]; simpl; split; intro H.
    + constructor.
    + reflexivity.
    + discriminate.
    + inversion H.
  - destruct params as [|param params]; simpl.
    + split; intro H.
      * discriminate.
      * inversion H.
    + split; intro H.
      * destruct (ty_eq_dec (elaborated_arg_ty arg) (fst param)); try discriminate.
        constructor; [assumption | now apply IH].
      * inversion H as [|? ? ? ? Hhead Htail]; subst.
        destruct (ty_eq_dec (elaborated_arg_ty arg) (fst param)); [now apply IH | contradiction].
Qed.

(** Check whether each argument type matches the parameter type selected by a
    list of partial-application indices. *)
Fixpoint arg_tys_match_indicesb
  (args : list labeled_elaborated_arg)
  (params : list signature_param)
  (indices : list nat) : bool :=
  match args, indices with
  | [], [] => true
  | (arg, _) :: args', idx :: indices' =>
      match nth_error params idx with
      | Some param =>
          if ty_eq_dec (elaborated_arg_ty arg) (fst param)
          then arg_tys_match_indicesb args' params indices'
          else false
      | None => false
      end
  | _, _ => false
  end.

(** The relational form of the partial-type checker matches the shape of
    [partial_app_candidate] from the core formalization, except that it uses
    elaborated argument types rather than full typing derivations. *)
Lemma arg_tys_match_indicesb_spec :
  forall args params indices,
    arg_tys_match_indicesb args params indices = true <->
    Forall2
      (fun arg idx =>
        exists param,
          nth_error params idx = Some param /\
          elaborated_arg_ty (fst arg) = fst param)
      args indices.
Proof.
  induction args as [|[arg case_choice] args IH]; intros params indices.
  - destruct indices as [|idx indices]; simpl; split; intro H.
    + constructor.
    + reflexivity.
    + discriminate.
    + inversion H.
  - destruct indices as [|idx indices]; simpl.
    + split; intro H.
      * discriminate.
      * inversion H.
    + split; intro H.
      * destruct (nth_error params idx) as [param|] eqn:Hnth; try discriminate.
        destruct (ty_eq_dec (elaborated_arg_ty arg) (fst param)); try discriminate.
        constructor.
        -- exists param; split; assumption.
        -- now apply IH.
      * inversion H as [|? ? ? ? Hhead Htail]; subst.
        destruct Hhead as [param [Hnth Heq]].
        rewrite Hnth.
        destruct (ty_eq_dec (elaborated_arg_ty arg) (fst param)); [now apply IH | contradiction].
Qed.

(** Exact overload matching succeeds when the argument cases can be aligned to
    the signature parameters and the aligned argument types match the
    signature's parameter types exactly. *)
Definition exact_signature_matchesb
  (sigma : signature) (args : list labeled_elaborated_arg) : bool :=
  match align_cases_compute (extract_cases (signature_params sigma)) args with
  | Some aligned_args => arg_tys_match_paramsb aligned_args (signature_params sigma)
  | None => false
  end.

(** The propositional reading of [exact_signature_matchesb]. *)
Definition exact_signature_matches
  (sigma : signature) (args : list labeled_elaborated_arg) : Prop :=
  exists aligned_args,
    align_cases (extract_cases (signature_params sigma)) args aligned_args /\
    Forall2
      (fun arg param => elaborated_arg_ty arg = fst param)
      aligned_args (signature_params sigma).

(** The boolean exact matcher is sound and complete with respect to the
    relational exact-matching predicate. *)
Lemma exact_signature_matchesb_spec :
  forall sigma args,
    exact_signature_matchesb sigma args = true <->
    exact_signature_matches sigma args.
Proof.
  intros sigma args; unfold exact_signature_matchesb, exact_signature_matches.
  destruct (align_cases_compute (extract_cases (signature_params sigma)) args)
    as [aligned_args|] eqn:Halign; simpl.
  - rewrite arg_tys_match_paramsb_spec; split; intro H.
    + exists aligned_args; split; assumption.
    + destruct H as [aligned_args' [Halign' Htypes]].
      unfold align_cases in Halign'.
      rewrite Halign in Halign'; inversion Halign'; subst; exact Htypes.
  - split; intro H.
    + discriminate.
    + destruct H as [aligned_args [Halign' _]].
      unfold align_cases in Halign'; rewrite Halign in Halign'; discriminate.
Qed.

(** Partial overload matching succeeds when the call is under-saturated, the
    supplied argument cases can be matched to parameter positions, and the
    chosen parameter types agree with the elaborated argument types. *)
Definition partial_signature_matchesb
  (sigma : signature) (args : list labeled_elaborated_arg)
  : option (list nat) :=
  if Nat.ltb (length args) (length (signature_params sigma))
  then
    match match_partial_compute
      (extract_cases (signature_params sigma))
      (extract_cases args)
    with
    | Some indices =>
        if arg_tys_match_indicesb args (signature_params sigma) indices
        then Some indices
        else None
    | None => None
    end
  else None.

(** The propositional reading of [partial_signature_matchesb]. *)
Definition partial_signature_matches
  (sigma : signature) (args : list labeled_elaborated_arg)
  (indices : list nat) : Prop :=
  length args < length (signature_params sigma) /\
  match_partial
    (extract_cases (signature_params sigma))
    (extract_cases args)
    indices /\
  Forall2
    (fun arg idx =>
      exists param,
        nth_error (signature_params sigma) idx = Some param /\
        elaborated_arg_ty (fst arg) = fst param)
    args indices.

(** The boolean partial matcher is sound and complete with respect to the
    relational partial-matching predicate. *)
Lemma partial_signature_matchesb_spec :
  forall sigma args indices,
    partial_signature_matchesb sigma args = Some indices <->
    partial_signature_matches sigma args indices.
Proof.
  intros sigma args indices; unfold partial_signature_matchesb, partial_signature_matches.
  destruct (Nat.ltb (length args) (length (signature_params sigma))) eqn:Hlt; simpl.
  - destruct (match_partial_compute
      (extract_cases (signature_params sigma))
      (extract_cases args)) as [indices'|] eqn:Hmatch; simpl.
    + destruct (arg_tys_match_indicesb args (signature_params sigma) indices')
        eqn:Htypes; simpl.
      * split; intro H.
        -- inversion H; subst. split.
           ++ now apply Nat.ltb_lt.
           ++ split; [exact Hmatch | now apply arg_tys_match_indicesb_spec].
        -- destruct H as [_ [Hmatch' Htypes']].
           unfold match_partial in Hmatch'; rewrite Hmatch in Hmatch'; inversion Hmatch'; subst.
           reflexivity.
      * split; intro H.
        -- discriminate.
        -- destruct H as [_ [Hmatch' Htypes']].
           unfold match_partial in Hmatch'; rewrite Hmatch in Hmatch'; inversion Hmatch'; subst.
           assert (arg_tys_match_indicesb args (signature_params sigma) indices = true) as Htypesb.
           { now apply arg_tys_match_indicesb_spec. }
           rewrite Htypesb in Htypes; discriminate.
    + split; intro H.
      * discriminate.
      * destruct H as [_ [Hmatch' _]].
        unfold match_partial in Hmatch'; rewrite Hmatch in Hmatch'; discriminate.
  - split; intro H.
    + discriminate.
    + destruct H as [Hlt' _].
      apply Nat.ltb_ge in Hlt; lia.
Qed.

(* ================================================================= *)
(** ** Overload Choices and Elaboration Results *)
(* ================================================================= *)

(** An overload choice records the concrete overload selected by elaboration.
    Exact and partial applications are separated because the partial case also
    needs to remember which parameters were filled. *)
Inductive overload_choice : Type :=
  (** Exact application of a particular overload with a concrete case labeling
      for the elaborated arguments. *)
  | ExactChoice
      (resolved_name : fun_name)
      (resolved_signature : signature)
      (resolved_args : list (expr * case_label))
  (** Partial application of a particular overload, together with the indices
      of the parameters filled by the supplied arguments. *)
  | PartialChoice
      (resolved_name : fun_name)
      (resolved_signature : signature)
      (resolved_args : list (expr * case_label))
      (resolved_indices : list nat).

(** Elaborating a call either fails, succeeds uniquely, or reports ambiguity
    explicitly.  The ambiguous case intentionally carries no "winner", which
    prevents the algorithm from silently depending on list iteration order. *)
Inductive elaboration_result : Type :=
  (** No overload matched the elaborated argument cases and types. *)
  | ElabNoMatch
  (** Exactly one overload choice matched. *)
  | ElabUnique (choice : overload_choice)
  (** Two or more distinct overload choices matched. *)
  | ElabAmbiguous.

(** Exact choices for one fixed overload are produced by enumerating all
    argument labelings and retaining the ones that pass the exact matcher. *)
Definition exact_choices_for_signature
  (resolved_name : fun_name) (sigma : signature)
  (labeled_argss : list (list labeled_elaborated_arg))
  : list overload_choice :=
  flat_map
    (fun labeled_args =>
      if exact_signature_matchesb sigma labeled_args
      then [ExactChoice resolved_name sigma (labeled_args_to_core labeled_args)]
      else [])
    labeled_argss.

(** Partial choices for one fixed overload are produced similarly, except
    that the partial matcher also returns the chosen parameter indices. *)
Definition partial_choices_for_signature
  (resolved_name : fun_name) (sigma : signature)
  (labeled_argss : list (list labeled_elaborated_arg))
  : list overload_choice :=
  flat_map
    (fun labeled_args =>
      match partial_signature_matchesb sigma labeled_args with
      | Some indices =>
          [PartialChoice resolved_name sigma (labeled_args_to_core labeled_args) indices]
      | None => []
      end)
    labeled_argss.

(** All exact overload choices for a surface call.  This is the elaboration
    counterpart of the core full-application candidate search, but phrased in
    terms of morphology-derived name/case candidates and already elaborated
    argument types. *)
Definition exact_choices
  (analyze : morph_oracle) (env : elaboration_env) (call : surface_call)
  : list overload_choice :=
  let labeled_argss := enumerate_labeled_args analyze (call_surface_args call) in
  flat_map
    (fun resolved_name =>
      flat_map
        (fun sigma => exact_choices_for_signature resolved_name sigma labeled_argss)
        (callable_signatures env resolved_name))
    (scoped_candidate_fun_names analyze env (call_surface_head call)).

(** All partial overload choices for a surface call.  These are considered
    only when no exact choices exist. *)
Definition partial_choices
  (analyze : morph_oracle) (env : elaboration_env) (call : surface_call)
  : list overload_choice :=
  let labeled_argss := enumerate_labeled_args analyze (call_surface_args call) in
  flat_map
    (fun resolved_name =>
      flat_map
        (fun sigma => partial_choices_for_signature resolved_name sigma labeled_argss)
        (callable_signatures env resolved_name))
    (scoped_candidate_fun_names analyze env (call_surface_head call)).

(** Exact matches take precedence over partial matches, mirroring the
    implementation. *)
Definition prioritized_choices
  (analyze : morph_oracle) (env : elaboration_env) (call : surface_call)
  : list overload_choice :=
  match exact_choices analyze env call with
  | [] => partial_choices analyze env call
  | exacts => exacts
  end.

(** The classifier forgets list order except for the unique case, where the
    singleton witness is returned.  Ambiguous lists never select a first
    element. *)
Definition classify_choices (choices : list overload_choice) : elaboration_result :=
  match choices with
  | [] => ElabNoMatch
  | [choice] => ElabUnique choice
  | _ => ElabAmbiguous
  end.

(** The elaboration algorithm for one call site. *)
Definition elaborate_call
  (analyze : morph_oracle) (env : elaboration_env) (call : surface_call)
  : elaboration_result :=
  classify_choices (prioritized_choices analyze env call).

(* ================================================================= *)
(** ** Relational Reading of the Computed Choices *)
(* ================================================================= *)

(** An exact choice is semantically justified when it comes from:

    - a candidate head name from morphology;
    - a deduplicated overload in the environment;
    - a concrete argument labeling enumerated from morphology;
    - an exact signature match for that labeling. *)
Inductive exact_choice_matches
  (analyze : morph_oracle) (env : elaboration_env) (call : surface_call)
  : overload_choice -> Prop :=
  | ECM_Exact :
      forall resolved_name sigma labeled_args,
        In resolved_name (scoped_candidate_fun_names analyze env (call_surface_head call)) ->
        In sigma (callable_signatures env resolved_name) ->
        In labeled_args (enumerate_labeled_args analyze (call_surface_args call)) ->
        exact_signature_matches sigma labeled_args ->
        exact_choice_matches analyze env call
          (ExactChoice resolved_name sigma (labeled_args_to_core labeled_args)).

(** A partial choice is semantically justified when it comes from the same
    search process, but with the partial matcher and its chosen index list. *)
Inductive partial_choice_matches
  (analyze : morph_oracle) (env : elaboration_env) (call : surface_call)
  : overload_choice -> Prop :=
  | PCM_Partial :
      forall resolved_name sigma labeled_args indices,
        In resolved_name (scoped_candidate_fun_names analyze env (call_surface_head call)) ->
        In sigma (callable_signatures env resolved_name) ->
        In labeled_args (enumerate_labeled_args analyze (call_surface_args call)) ->
        partial_signature_matches sigma labeled_args indices ->
        partial_choice_matches analyze env call
          (PartialChoice resolved_name sigma (labeled_args_to_core labeled_args) indices).

(** Prioritized matching is the relational counterpart of [prioritized_choices]:
    exact matches always count, and partial matches count only when the exact
    search returned nothing. *)
Inductive prioritized_choice_matches
  (analyze : morph_oracle) (env : elaboration_env) (call : surface_call)
  : overload_choice -> Prop :=
  (** Exact matches survive prioritization unchanged. *)
  | Prio_Exact :
      forall choice,
        exact_choice_matches analyze env call choice ->
        prioritized_choice_matches analyze env call choice
  (** Partial matches are considered only when exact matching found nothing. *)
  | Prio_Partial :
      forall choice,
        exact_choices analyze env call = [] ->
        partial_choice_matches analyze env call choice ->
        prioritized_choice_matches analyze env call choice.

(* ================================================================= *)
(** ** Membership Specifications *)
(* ================================================================= *)

(** Membership in [exact_choices_for_signature] is exactly the existence of an
    enumerated labeling that passed the boolean exact matcher. *)
Lemma in_exact_choices_for_signature_iff :
  forall resolved_name sigma labeled_argss choice,
    In choice (exact_choices_for_signature resolved_name sigma labeled_argss) <->
    exists labeled_args,
      In labeled_args labeled_argss /\
      exact_signature_matchesb sigma labeled_args = true /\
      choice = ExactChoice resolved_name sigma (labeled_args_to_core labeled_args).
Proof.
  intros resolved_name sigma labeled_argss choice.
  unfold exact_choices_for_signature; rewrite in_flat_map; split.
  - intros [labeled_args [Hin Hchoice]].
    destruct (exact_signature_matchesb sigma labeled_args) eqn:Hmatch; simpl in Hchoice; try contradiction.
    destruct Hchoice as [Hchoice | []]; subst; eauto 10.
  - intros (labeled_args & Hin & Hmatch & ->).
    exists labeled_args; split; [exact Hin | rewrite Hmatch; simpl; auto].
Qed.

(** Membership in [partial_choices_for_signature] is exactly the existence of
    an enumerated labeling that passed the boolean partial matcher. *)
Lemma in_partial_choices_for_signature_iff :
  forall resolved_name sigma labeled_argss choice,
    In choice (partial_choices_for_signature resolved_name sigma labeled_argss) <->
    exists labeled_args indices,
      In labeled_args labeled_argss /\
      partial_signature_matchesb sigma labeled_args = Some indices /\
      choice = PartialChoice resolved_name sigma (labeled_args_to_core labeled_args) indices.
Proof.
  intros resolved_name sigma labeled_argss choice.
  unfold partial_choices_for_signature; rewrite in_flat_map; split.
  - intros [labeled_args [Hin Hchoice]].
    destruct (partial_signature_matchesb sigma labeled_args) as [indices|] eqn:Hmatch;
      simpl in Hchoice; try contradiction.
    destruct Hchoice as [Hchoice | []]; subst; eauto 10.
  - intros (labeled_args & indices & Hin & Hmatch & ->).
    exists labeled_args; split; [exact Hin | rewrite Hmatch; simpl; auto].
Qed.

(** Membership in the global exact-choice list expands into head-candidate,
    signature, and labeling witnesses. *)
Lemma in_exact_choices_iff :
  forall analyze env call choice,
    In choice (exact_choices analyze env call) <->
    exists resolved_name sigma labeled_args,
      In resolved_name (scoped_candidate_fun_names analyze env (call_surface_head call)) /\
      In sigma (callable_signatures env resolved_name) /\
      In labeled_args (enumerate_labeled_args analyze (call_surface_args call)) /\
      exact_signature_matchesb sigma labeled_args = true /\
      choice = ExactChoice resolved_name sigma (labeled_args_to_core labeled_args).
Proof.
  intros analyze env call choice.
  unfold exact_choices; rewrite in_flat_map; split.
  - intros [resolved_name [Hname Hin]].
    rewrite in_flat_map in Hin.
    destruct Hin as [sigma [Hsigma Hin]].
    apply in_exact_choices_for_signature_iff in Hin.
    destruct Hin as [labeled_args [Hargs [Hmatch Hchoice]]].
    eauto 10.
  - intros (resolved_name & sigma & labeled_args & Hname & Hsigma & Hargs & Hmatch & ->).
    exists resolved_name; split; [exact Hname |].
    rewrite in_flat_map; exists sigma; split; [exact Hsigma |].
    apply in_exact_choices_for_signature_iff.
    exists labeled_args; repeat split; assumption.
Qed.

(** Membership in the global partial-choice list expands analogously. *)
Lemma in_partial_choices_iff :
  forall analyze env call choice,
    In choice (partial_choices analyze env call) <->
    exists resolved_name sigma labeled_args indices,
      In resolved_name (scoped_candidate_fun_names analyze env (call_surface_head call)) /\
      In sigma (callable_signatures env resolved_name) /\
      In labeled_args (enumerate_labeled_args analyze (call_surface_args call)) /\
      partial_signature_matchesb sigma labeled_args = Some indices /\
      choice = PartialChoice resolved_name sigma (labeled_args_to_core labeled_args) indices.
Proof.
  intros analyze env call choice.
  unfold partial_choices; rewrite in_flat_map; split.
  - intros [resolved_name [Hname Hin]].
    rewrite in_flat_map in Hin.
    destruct Hin as [sigma [Hsigma Hin]].
    apply in_partial_choices_for_signature_iff in Hin.
    destruct Hin as [labeled_args [indices [Hargs [Hmatch Hchoice]]]].
    eauto 10.
  - intros (resolved_name & sigma & labeled_args & indices & Hname & Hsigma & Hargs & Hmatch & ->).
    exists resolved_name; split; [exact Hname |].
    rewrite in_flat_map; exists sigma; split; [exact Hsigma |].
    apply in_partial_choices_for_signature_iff.
    exists labeled_args, indices; repeat split; assumption.
Qed.

(* ================================================================= *)
(** ** Soundness and Completeness of the Computed Choice Lists *)
(* ================================================================= *)

(** Every exact choice computed by the algorithm really satisfies the exact
    relational matching specification. *)
Lemma exact_choices_sound :
  forall analyze env call choice,
    In choice (exact_choices analyze env call) ->
    exact_choice_matches analyze env call choice.
Proof.
  intros analyze env call choice Hin.
  apply in_exact_choices_iff in Hin.
  destruct Hin as (resolved_name & sigma & labeled_args & Hname & Hsigma & Hargs & Hmatch & ->).
  apply exact_signature_matchesb_spec in Hmatch.
  econstructor; eauto.
Qed.

(** Conversely, every relationally justified exact choice appears in the
    computed exact-choice list. *)
Lemma exact_choices_complete :
  forall analyze env call choice,
    exact_choice_matches analyze env call choice ->
    In choice (exact_choices analyze env call).
Proof.
  intros analyze env call choice Hmatch.
  inversion Hmatch as [resolved_name sigma labeled_args Hname Hsigma Hargs Hexact]; subst.
  apply in_exact_choices_iff.
  exists resolved_name, sigma, labeled_args; repeat split; try assumption.
  now apply exact_signature_matchesb_spec.
Qed.

(** Every partial choice computed by the algorithm really satisfies the
    partial relational matching specification. *)
Lemma partial_choices_sound :
  forall analyze env call choice,
    In choice (partial_choices analyze env call) ->
    partial_choice_matches analyze env call choice.
Proof.
  intros analyze env call choice Hin.
  apply in_partial_choices_iff in Hin.
  destruct Hin as (resolved_name & sigma & labeled_args & indices &
    Hname & Hsigma & Hargs & Hmatch & ->).
  apply partial_signature_matchesb_spec in Hmatch.
  econstructor; eauto.
Qed.

(** Conversely, every relationally justified partial choice appears in the
    computed partial-choice list. *)
Lemma partial_choices_complete :
  forall analyze env call choice,
    partial_choice_matches analyze env call choice ->
    In choice (partial_choices analyze env call).
Proof.
  intros analyze env call choice Hmatch.
  inversion Hmatch as [resolved_name sigma labeled_args indices Hname Hsigma Hargs Hpartial]; subst.
  apply in_partial_choices_iff.
  exists resolved_name, sigma, labeled_args, indices; repeat split; try assumption.
  now apply partial_signature_matchesb_spec.
Qed.

(** Membership in the prioritized choice list is sound with respect to the
    prioritized relational predicate. *)
Lemma prioritized_choices_sound :
  forall analyze env call choice,
    In choice (prioritized_choices analyze env call) ->
    prioritized_choice_matches analyze env call choice.
Proof.
  intros analyze env call choice Hin.
  unfold prioritized_choices in Hin.
  destruct (exact_choices analyze env call) as [|exact_choice exact_rest] eqn:Hexact.
  - simpl in Hin.
    apply Prio_Partial; [exact Hexact | now apply partial_choices_sound].
  - apply Prio_Exact.
    assert (In choice (exact_choices analyze env call)) as Hin_exact.
    { rewrite Hexact; exact Hin. }
    now apply exact_choices_sound in Hin_exact.
Qed.

(** The prioritized relational predicate is also complete for membership in
    the computed prioritized choice list. *)
Lemma prioritized_choices_complete :
  forall analyze env call choice,
    prioritized_choice_matches analyze env call choice ->
    In choice (prioritized_choices analyze env call).
Proof.
  intros analyze env call choice Hmatch.
  inversion Hmatch as [choice' Hexact | choice' Hexact Hpartial]; subst.
  - unfold prioritized_choices.
    destruct (exact_choices analyze env call) as [|exact_choice exact_rest] eqn:Hexact';
      [exfalso |].
    + pose proof (exact_choices_complete analyze env call choice Hexact) as Hin.
      rewrite Hexact' in Hin; contradiction.
    + pose proof (exact_choices_complete analyze env call choice Hexact) as Hin.
      rewrite Hexact' in Hin; exact Hin.
  - unfold prioritized_choices.
    destruct (exact_choices analyze env call) as [|exact_choice exact_rest] eqn:Hexact';
      [now apply partial_choices_complete |].
    rewrite Hexact in Hexact'; discriminate.
Qed.

(* ================================================================= *)
(** ** Classification Lemmas *)
(* ================================================================= *)

(** When the classifier reports a unique result, the underlying choice list
    really is a singleton. *)
Lemma classify_choices_unique :
  forall choice choices,
    classify_choices choices = ElabUnique choice ->
    choices = [choice].
Proof.
  intros choice [|choice0 [|choice1 choices]]; simpl; intro H;
    try discriminate; inversion H; reflexivity.
Qed.

(** This is the central "determinism or explicit ambiguity" theorem.  In a
    fixed environment, elaboration classifies the prioritized choice list into
    exactly one of the three intended cases: no match, one unique match, or
    multiple matches reported explicitly as ambiguity. *)
Theorem elaborate_call_deterministic_or_ambiguous :
  forall analyze env call,
    match elaborate_call analyze env call with
    | ElabNoMatch =>
        prioritized_choices analyze env call = []
    | ElabUnique choice =>
        prioritized_choices analyze env call = [choice]
    | ElabAmbiguous =>
        exists choice1 choice2 rest,
          prioritized_choices analyze env call = choice1 :: choice2 :: rest
    end.
Proof.
  intros analyze env call.
  unfold elaborate_call, classify_choices.
  destruct (prioritized_choices analyze env call) as [|choice1 [|choice2 rest]];
    simpl; eauto 10.
Qed.

(** If elaboration returns a unique result, that result is sound with respect
    to the prioritized matching relation. *)
Theorem elaborate_call_overload_sound :
  forall analyze env call choice,
    elaborate_call analyze env call = ElabUnique choice ->
    prioritized_choice_matches analyze env call choice.
Proof.
  intros analyze env call choice Hunique.
  pose proof (classify_choices_unique choice _ Hunique) as Hchoices.
  apply prioritized_choices_sound.
  unfold elaborate_call in Hunique.
  unfold classify_choices in Hunique.
  rewrite Hchoices; simpl; auto.
Qed.

(** If elaboration returns a unique result, no second distinct prioritized
    choice exists.  This is the implementation-side uniqueness property that
    corresponds to the core [full_app_resolves] / [partial_app_resolves]
    judgments. *)
Theorem elaborate_call_overload_unique :
  forall analyze env call choice choice',
    elaborate_call analyze env call = ElabUnique choice ->
    prioritized_choice_matches analyze env call choice' ->
    choice' = choice.
Proof.
  intros analyze env call choice choice' Hunique Hmatch.
  pose proof (classify_choices_unique choice _ Hunique) as Hchoices.
  pose proof (prioritized_choices_complete analyze env call choice' Hmatch) as Hin.
  rewrite Hchoices in Hin; simpl in Hin.
  destruct Hin as [-> | []]; reflexivity.
Qed.

(** A direct corollary packages the previous theorem in the form closer to the
    overload-resolution story: if elaboration reports a unique choice, there
    is no second distinct matching overload choice. *)
Corollary elaborate_call_no_second_distinct_choice :
  forall analyze env call choice choice',
    elaborate_call analyze env call = ElabUnique choice ->
    prioritized_choice_matches analyze env call choice' ->
    choice' <> choice ->
    False.
Proof.
  intros analyze env call choice choice' Hunique Hmatch Hneq.
  rewrite (elaborate_call_overload_unique analyze env call choice choice' Hunique Hmatch)
    in Hneq; contradiction.
Qed.

(* ================================================================= *)
(** ** Stability Under Irrelevant Growth *)
(* ================================================================= *)

(** Two elaboration environments agree on a call when every candidate function
    name for the head string has the same scope-filtered candidate list and
    the same deduplicated overload list in both environments.  No condition is
    imposed on constructors, because the current elaboration algorithm never
    inspects them. *)
Definition relevant_fun_ctxs_agree
  (analyze : morph_oracle)
  (env1 env2 : elaboration_env)
  (call : surface_call) : Prop :=
  scoped_candidate_fun_names analyze env1 (call_surface_head call) =
  scoped_candidate_fun_names analyze env2 (call_surface_head call) /\
  forall f,
    In f (scoped_candidate_fun_names analyze env1 (call_surface_head call)) ->
    callable_signatures env1 f = callable_signatures env2 f.

(** Exact-choice enumeration is stable under agreement on the relevant head
    candidates. *)
Lemma exact_choices_relevant_agree :
  forall analyze env1 env2 call,
    relevant_fun_ctxs_agree analyze env1 env2 call ->
    exact_choices analyze env1 call = exact_choices analyze env2 call.
Proof.
  intros analyze env1 env2 call [Hscope Hagree].
  unfold exact_choices.
  set (labeled_argss := enumerate_labeled_args analyze (call_surface_args call)).
  rewrite Hscope.
  assert (
    forall names : list fun_name,
      (forall f, In f names -> callable_signatures env1 f = callable_signatures env2 f) ->
      flat_map
        (fun resolved_name =>
          flat_map
            (fun sigma => exact_choices_for_signature resolved_name sigma labeled_argss)
            (callable_signatures env1 resolved_name))
        names =
      flat_map
        (fun resolved_name =>
          flat_map
            (fun sigma => exact_choices_for_signature resolved_name sigma labeled_argss)
            (callable_signatures env2 resolved_name))
        names) as Hnames.
  { induction names as [|resolved_name names IH]; simpl; intros Hagree_names; [reflexivity|].
    rewrite Hagree_names by (left; reflexivity); f_equal.
    apply IH; intros other Hother; apply Hagree_names; right; exact Hother. }
  apply Hnames; intros f Hf; apply Hagree.
  rewrite Hscope; exact Hf.
Qed.

(** Partial-choice enumeration is stable under the same agreement relation. *)
Lemma partial_choices_relevant_agree :
  forall analyze env1 env2 call,
    relevant_fun_ctxs_agree analyze env1 env2 call ->
    partial_choices analyze env1 call = partial_choices analyze env2 call.
Proof.
  intros analyze env1 env2 call [Hscope Hagree].
  unfold partial_choices.
  set (labeled_argss := enumerate_labeled_args analyze (call_surface_args call)).
  rewrite Hscope.
  assert (
    forall names : list fun_name,
      (forall f, In f names -> callable_signatures env1 f = callable_signatures env2 f) ->
      flat_map
        (fun resolved_name =>
          flat_map
            (fun sigma => partial_choices_for_signature resolved_name sigma labeled_argss)
            (callable_signatures env1 resolved_name))
        names =
      flat_map
        (fun resolved_name =>
          flat_map
            (fun sigma => partial_choices_for_signature resolved_name sigma labeled_argss)
            (callable_signatures env2 resolved_name))
        names) as Hnames.
  { induction names as [|resolved_name names IH]; simpl; intros Hagree_names; [reflexivity|].
    rewrite Hagree_names by (left; reflexivity); f_equal.
    apply IH; intros other Hother; apply Hagree_names; right; exact Hother. }
  apply Hnames; intros f Hf; apply Hagree.
  rewrite Hscope; exact Hf.
Qed.

(** Stability under irrelevant growth: adding unrelated names, unrelated
    overloads, or arbitrary constructor information does not change the
    elaboration of a call that only depends on the relevant head candidates. *)
Theorem elaborate_call_stable_under_irrelevant_context_growth :
  forall analyze env1 env2 call,
    relevant_fun_ctxs_agree analyze env1 env2 call ->
    elaborate_call analyze env1 call = elaborate_call analyze env2 call.
Proof.
  intros analyze env1 env2 call Hagree.
  unfold elaborate_call, prioritized_choices.
  rewrite (exact_choices_relevant_agree analyze env1 env2 call Hagree).
  destruct (exact_choices analyze env2 call) as [|choice choices].
  - now rewrite (partial_choices_relevant_agree analyze env1 env2 call Hagree).
  - reflexivity.
Qed.

(* ================================================================= *)
(** ** Bridges to the Core Formalization *)
(* ================================================================= *)

(** Theorems in this section should be read as compile-time correctness
    results for [elaborate_call] together with coherence results for the
    existing overloaded core semantics.  Because the split core development
    keeps unresolved [EApp] nodes in the core syntax, the bridge theorems
    below say that a compile-time unique choice agrees with the declarative
    static-semantics and dynamic-resolution relations of that overloaded
    core.  A
    separate resolved call-head semantics, added later in this file, packages
    the same compile-time choice into a term that no longer performs overload
    search at the elaborated head. *)

(** The elaboration layer stores a type next to every elaborated argument.
    To connect elaboration with the core static semantics, we record the
    intended consistency condition: the stored type is a plain type for the
    stored core expression in the empty context. *)
Definition elaborated_arg_well_typed
  (Se : effect_ctx) (Sf : fun_ctx) (Sc : ctor_ctx)
  (mu : eff_mode) (arg : elaborated_arg) : Prop :=
  has_plain_type Se Sf Sc [] mu
    (elaborated_arg_expr arg) (elaborated_arg_ty arg).

(** A whole surface call has well-typed elaborated arguments when each stored
    argument individually satisfies [elaborated_arg_well_typed]. *)
Definition surface_call_args_well_typed
  (Se : effect_ctx) (Sf : fun_ctx) (Sc : ctor_ctx)
  (mu : eff_mode) (call : surface_call) : Prop :=
  Forall (elaborated_arg_well_typed Se Sf Sc mu) (call_surface_args call).

(** [pick_case_payload] only removes one labeled payload from the list, so any
    payload property that held for the whole input list still holds for the
    selected payload and for the remaining list.  This is the key local fact
    used to transport typing assumptions through case-based reordering. *)
Lemma pick_case_payload_preserves_Forall_payload :
  forall (A : Type) (P : A -> Prop) c xs a rest,
    Forall (fun p => P (fst p)) xs ->
    pick_case_payload c xs = Some (a, rest) ->
    P a /\ Forall (fun p => P (fst p)) rest.
Proof.
  intros A P c xs.
  induction xs as [|[a' c'] xs IH]; intros a rest Hfor Hpick.
  - discriminate.
  - inversion Hfor as [|x xs' Hhead Htail]; subst.
    simpl in Hpick.
    destruct (case_label_eq_dec c c') as [Heq|Hneq].
    + inversion Hpick; subst. split; assumption.
    + destruct (pick_case_payload c xs) as [[a'' rest']|] eqn:Ep; try discriminate.
      inversion Hpick; subst.
      destruct (IH _ _ Htail eq_refl) as [Ha Hrest].
      split; [exact Ha | constructor; assumption].
Qed.

(** Case alignment preserves payload properties: if every labeled argument in
    the provided list satisfies a property [P], then every payload in the
    aligned list also satisfies [P]. *)
Lemma align_cases_preserves_Forall_payload :
  forall (A : Type) (P : A -> Prop) expected provided aligned,
    align_cases expected provided aligned ->
    Forall (fun p => P (fst p)) provided ->
    Forall P aligned.
Proof.
  intros A P expected; induction expected as [|c cs IH];
    intros provided aligned Halign Hfor.
  - unfold align_cases in Halign. simpl in Halign.
    destruct provided; inversion Halign; constructor.
  - unfold align_cases in Halign. simpl in Halign.
    destruct (pick_case_payload c provided) as [[a rest]|] eqn:Hpick; try discriminate.
    destruct (align_cases_compute cs rest) as [aligned'|] eqn:Hrest; try discriminate.
    inversion Halign; subst aligned.
    destruct (pick_case_payload_preserves_Forall_payload A P c provided a rest Hfor Hpick)
      as [Ha Hrest_for].
    constructor.
    + exact Ha.
    + eapply IH; eauto.
Qed.

(** Mapping only the payload component of labeled arguments commutes with
    [pick_case_payload].  Since case alignment depends only on case labels,
    this lets us reuse an alignment witness after projecting elaborated
    arguments to their core expressions. *)
Lemma pick_case_payload_map_payload :
  forall (A B : Type) (f : A -> B) c xs a rest,
    pick_case_payload c xs = Some (a, rest) ->
    pick_case_payload c (List.map (fun p => (f (fst p), snd p)) xs) =
      Some (f a, List.map (fun p => (f (fst p), snd p)) rest).
Proof.
  intros A B f c xs; induction xs as [|[a' c'] xs IH]; intros a rest Hpick.
  - discriminate.
  - simpl in Hpick.
    destruct (case_label_eq_dec c c') as [Heq|Hneq].
    + inversion Hpick; subst.
      simpl. destruct (case_label_eq_dec c' c'); [reflexivity|contradiction].
    + destruct (pick_case_payload c xs) as [[a'' rest']|] eqn:Ep; try discriminate.
      inversion Hpick; subst.
      simpl. destruct (case_label_eq_dec c c'); [contradiction|].
      now rewrite (IH _ _ eq_refl).
Qed.

(** Consequently, any case-alignment witness can be transported through a
    payload map.  We use this with [elaborated_arg_expr] to turn alignment of
    elaborated arguments into alignment of the core argument list actually
    passed to [EApp]. *)
Lemma align_cases_map_payload :
  forall (A B : Type) (f : A -> B) expected provided aligned,
    align_cases expected provided aligned ->
    align_cases expected
      (List.map (fun p => (f (fst p), snd p)) provided)
      (List.map f aligned).
Proof.
  intros A B f expected; induction expected as [|c cs IH];
    intros provided aligned Halign.
  - unfold align_cases in Halign. simpl in *.
    destruct provided; inversion Halign; reflexivity.
  - unfold align_cases in Halign. simpl in Halign.
    destruct (pick_case_payload c provided) as [[a rest]|] eqn:Hpick; try discriminate.
    destruct (align_cases_compute cs rest) as [aligned'|] eqn:Hrest; try discriminate.
    inversion Halign; subst aligned.
    unfold align_cases. simpl.
    rewrite (pick_case_payload_map_payload A B f c provided a rest Hpick).
    simpl. now rewrite (IH rest aligned' Hrest).
Qed.

(** Projecting elaborated arguments to core expressions leaves the case-label
    list unchanged.  Partial-application matching depends only on those case
    labels. *)
Lemma extract_cases_labeled_args_to_core :
  forall labeled_args,
    extract_cases (labeled_args_to_core labeled_args) = extract_cases labeled_args.
Proof.
  induction labeled_args as [|[arg c] labeled_args IH]; simpl; [reflexivity|].
  now rewrite IH.
Qed.

(** Every labeled argument enumeration reuses exactly the elaborated argument
    payloads from the source call.  Therefore any per-argument typing
    assumption on the source call lifts to the chosen labeling. *)
Lemma in_enumerate_labeled_args_well_typed :
  forall analyze args labeled_args Se Sf Sc mu,
    In labeled_args (enumerate_labeled_args analyze args) ->
    Forall (elaborated_arg_well_typed Se Sf Sc mu) args ->
    Forall (fun p => elaborated_arg_well_typed Se Sf Sc mu (fst p)) labeled_args.
Proof.
  intros analyze args; induction args as [|arg args IH];
    intros labeled_args Se Sf Sc mu Hin Htyped.
  - simpl in Hin. destruct Hin as [<-|[]]. constructor.
  - simpl in Hin.
    inversion Htyped as [|arg' args' Hhead Htail]; subst.
    apply in_flat_map in Hin.
    destruct Hin as [case_choice [Hcase Hin_map]].
    apply in_map_iff in Hin_map.
    destruct Hin_map as [rest [Hrest_eq Hin_rest]].
    inversion Hrest_eq; subst.
    constructor.
    + exact Hhead.
    + eapply IH; eauto.
Qed.

(** This helper turns equality-based exact matching into the [has_type]
    premises expected by the application typing rule. *)
Lemma exact_aligned_exprs_typed_params :
  forall Se Sf Sc mu (aligned_args : list elaborated_arg) (params : list signature_param),
    Forall (elaborated_arg_well_typed Se Sf Sc mu) aligned_args ->
    Forall2 (fun arg param => elaborated_arg_ty arg = fst param) aligned_args params ->
    Forall2
      (fun arg param =>
        exists kres_i,
          has_type Se Sf Sc [] mu arg (fst param, kres_i))
      (List.map elaborated_arg_expr aligned_args) params.
Proof.
  intros Se Sf Sc mu aligned_args params Htyped Heq.
  revert Htyped.
  induction Heq as [|arg param aligned_args params Heq_head Heq_tail IH];
    intros Htyped; simpl.
  - inversion Htyped; constructor.
  - inversion Htyped as [|arg' aligned_args' Hhead Htail]; subst.
    constructor.
    + destruct Hhead as [kres Hty].
      exists kres. now rewrite <- Heq_head.
    + apply IH. exact Htail.
Qed.

(** The same conversion, but forgetting the result-case witness to obtain the
    [has_plain_type] premises used by [full_app_candidate]. *)
Lemma exact_aligned_exprs_plain_params :
  forall Se Sf Sc mu (aligned_args : list elaborated_arg) (params : list signature_param),
    Forall (elaborated_arg_well_typed Se Sf Sc mu) aligned_args ->
    Forall2 (fun arg param => elaborated_arg_ty arg = fst param) aligned_args params ->
    Forall2
      (fun arg param =>
        has_plain_type Se Sf Sc [] mu arg (fst param))
      (List.map elaborated_arg_expr aligned_args) params.
Proof.
  intros Se Sf Sc mu aligned_args params Htyped Heq.
  revert Htyped.
  induction Heq as [|arg param aligned_args params Heq_head Heq_tail IH];
    intros Htyped; simpl.
  - inversion Htyped; constructor.
  - inversion Htyped as [|arg' aligned_args' Hhead Htail]; subst.
    constructor.
    + destruct Hhead as [kres Hty]. exists kres. now rewrite <- Heq_head.
    + apply IH. exact Htail.
Qed.

(** Partial matching similarly turns the stored elaborated-argument types into
    the [has_type] premises expected by [T_App_Partial]. *)
Lemma partial_labeled_core_args_typed_indices :
  forall Se Sf Sc mu (labeled_args : list labeled_elaborated_arg)
    (params : list signature_param) indices,
    Forall (fun p => elaborated_arg_well_typed Se Sf Sc mu (fst p)) labeled_args ->
    Forall2
      (fun arg idx =>
        exists param,
          nth_error params idx = Some param /\
          elaborated_arg_ty (fst arg) = fst param)
      labeled_args indices ->
    Forall2
      (fun arg idx =>
        exists param kres_i,
          nth_error params idx = Some param /\
          has_type Se Sf Sc [] mu (fst arg) (fst param, kres_i))
      (labeled_args_to_core labeled_args) indices.
Proof.
  intros Se Sf Sc mu labeled_args params indices Htyped Hmatch.
  revert Htyped.
  induction Hmatch as [|arg idx labeled_args indices Hhead Htail IH];
    intros Htyped; simpl.
  - inversion Htyped; constructor.
  - inversion Htyped as [|[earg case_choice] labeled_args' Htyped_head Htyped_tail]; subst.
    constructor.
    + destruct Hhead as [param [Hnth Heq]].
      destruct Htyped_head as [kres Hty].
      exists param, kres. split; [exact Hnth |].
      now rewrite <- Heq.
    + apply IH. exact Htyped_tail.
Qed.

(** Forgetting result-case witnesses yields the partial-candidate premises used
    by [partial_app_candidate]. *)
Lemma partial_labeled_core_args_plain_indices :
  forall Se Sf Sc mu (labeled_args : list labeled_elaborated_arg)
    (params : list signature_param) indices,
    Forall (fun p => elaborated_arg_well_typed Se Sf Sc mu (fst p)) labeled_args ->
    Forall2
      (fun arg idx =>
        exists param,
          nth_error params idx = Some param /\
          elaborated_arg_ty (fst arg) = fst param)
      labeled_args indices ->
    Forall2
      (fun arg idx =>
        exists param,
          nth_error params idx = Some param /\
          has_plain_type Se Sf Sc [] mu (fst arg) (fst param))
      (labeled_args_to_core labeled_args) indices.
Proof.
  intros Se Sf Sc mu labeled_args params indices Htyped Hmatch.
  revert Htyped.
  induction Hmatch as [|arg idx labeled_args indices Hhead Htail IH];
    intros Htyped; simpl.
  - inversion Htyped; constructor.
  - inversion Htyped as [|[earg case_choice] labeled_args' Htyped_head Htyped_tail]; subst.
    constructor.
    + destruct Hhead as [param [Hnth Heq]].
      destruct Htyped_head as [kres Hty].
      exists param. split; [exact Hnth |].
      exists kres. now rewrite <- Heq.
    + apply IH. exact Htyped_tail.
Qed.

(** When a signature is monomorphic, the empty type substitution used by the
    application typing rules leaves each parameter type unchanged. *)
Lemma typed_params_monomorphic_nil :
  forall Se Sf Sc mu sigma (args : list expr) (params : list signature_param),
    monomorphic_signature sigma ->
    Forall2
      (fun arg param =>
        exists kres_i,
          has_type Se Sf Sc [] mu arg (fst param, kres_i))
      args params ->
    Forall2
      (fun arg param =>
        exists kres_i,
          has_type Se Sf Sc [] mu arg
            (apply_subst
              (combine (signature_tvars sigma)
                (List.map snd ([] : list (tyvar_name * ty))))
              (fst param), kres_i))
      args params.
Proof.
  intros Se Sf Sc mu sigma args params Hmono Htyped.
  induction Htyped as [|arg param args params [kres Hty] Hrest IH]; constructor.
  - exists kres.
    rewrite (monomorphic_bound_nil sigma [] Hmono).
    simpl. rewrite apply_subst_nil. exact Hty.
  - exact IH.
Qed.

(** The same normalization is needed for the parameter-indexed premises of
    [T_App_Partial]. *)
Lemma typed_indices_monomorphic_nil :
  forall Se Sf Sc mu sigma (args : list (expr * case_label)) indices,
    monomorphic_signature sigma ->
    Forall2
      (fun arg idx =>
        exists param kres_i,
          nth_error (signature_params sigma) idx = Some param /\
          has_type Se Sf Sc [] mu (fst arg) (fst param, kres_i))
      args indices ->
    Forall2
      (fun arg idx =>
        exists param kres_i,
          nth_error (signature_params sigma) idx = Some param /\
          has_type Se Sf Sc [] mu (fst arg)
            (apply_subst
              (combine (signature_tvars sigma)
                (List.map snd ([] : list (tyvar_name * ty))))
              (fst param), kres_i))
      args indices.
Proof.
  intros Se Sf Sc mu sigma args indices Hmono Htyped.
  induction Htyped as [|arg idx args indices [param [kres [Hnth Hty]]] Hrest IH];
    constructor.
  - exists param, kres. split; [exact Hnth |].
    rewrite (monomorphic_bound_nil sigma [] Hmono).
    simpl. rewrite apply_subst_nil. exact Hty.
  - exact IH.
Qed.

(** Mapping the empty type substitution over a list of types leaves the list
    unchanged. *)
Lemma map_apply_subst_nil :
  forall ts,
    List.map (fun t => apply_subst [] t) ts = ts.
Proof.
  induction ts as [|t ts IH]; simpl; [reflexivity|].
  now rewrite apply_subst_nil, IH.
Qed.

(** The residual function type produced by [T_App_Partial] simplifies to the
    obvious arrow type when the chosen signature is monomorphic. *)
Lemma monomorphic_partial_result_type_nil :
  forall sigma indices,
    monomorphic_signature sigma ->
    List.fold_right TyArr
      (apply_subst
        (combine (signature_tvars sigma)
          (List.map snd ([] : list (tyvar_name * ty))))
        (signature_return_ty sigma))
      (List.map
        (fun t =>
          apply_subst
            (combine (signature_tvars sigma)
              (List.map snd ([] : list (tyvar_name * ty))))
            t)
        (collect_at_indices
          (remaining_indices 0 (length (signature_params sigma)) indices)
          (signature_params sigma))) =
    List.fold_right TyArr
      (signature_return_ty sigma)
      (collect_at_indices
        (remaining_indices 0 (length (signature_params sigma)) indices)
        (signature_params sigma)).
Proof.
  intros sigma indices Hmono.
  rewrite (monomorphic_bound_nil sigma [] Hmono).
  simpl. rewrite apply_subst_nil, map_apply_subst_nil. reflexivity.
Qed.

(** Prioritized matching of an exact choice must have come from the exact side
    of the priority split; a partial witness cannot construct an
    [ExactChoice]. *)
Lemma prioritized_exact_choice_matches :
  forall analyze env call f sigma args,
    prioritized_choice_matches analyze env call (ExactChoice f sigma args) ->
    exact_choice_matches analyze env call (ExactChoice f sigma args).
Proof.
  intros analyze env call f sigma args Hmatch.
  inversion Hmatch as [choice Hexact | choice Hexact Hpartial]; subst.
  - exact Hexact.
  - inversion Hpartial.
Qed.

(** Dually, prioritized matching of a partial choice must come from the
    partial side of the priority split. *)
Lemma prioritized_partial_choice_matches :
  forall analyze env call f sigma args indices,
    prioritized_choice_matches analyze env call (PartialChoice f sigma args indices) ->
    partial_choice_matches analyze env call (PartialChoice f sigma args indices).
Proof.
  intros analyze env call f sigma args indices Hmatch.
  inversion Hmatch as [choice Hexact | choice Hexact Hpartial]; subst.
  - inversion Hexact.
  - exact Hpartial.
Qed.

(** A semantically justified exact choice necessarily uses a signature that is
    present in the callable-signature environment for the chosen function
    name.  This projection is useful when relating elaboration choices to the
    completeness lemmas for executable entries in [fun_entry_ctx_ok]. *)
Lemma exact_choice_matches_in_callable_signatures :
  forall analyze env call f sigma args,
    exact_choice_matches analyze env call (ExactChoice f sigma args) ->
    In sigma (callable_signatures env f).
Proof.
  intros analyze env call f sigma args Hmatch.
  inversion Hmatch; subst; assumption.
Qed.

(** A signature listed in [callable_signatures] really comes from the
    underlying elaboration environment's function-signature map. *)
Lemma callable_signature_in_fun_ctx :
  forall env f sigma,
    In sigma (callable_signatures env f) ->
    In sigma (elaboration_fun_ctx env f).
Proof.
  intros env f sigma Hsigma.
  rewrite callable_signatures_eq in Hsigma.
  now apply (proj1 (nodup_In signature_eq_dec (elaboration_fun_ctx env f) sigma)).
Qed.

(** Exact semantic matching plus well-typed elaborated arguments yields a core
    [full_app_candidate].  This is the basic soundness bridge from elaboration
    to the declarative static semantics of applications. *)
Theorem exact_signature_matches_full_app_candidate :
  forall Se Sf Sc mu sigma labeled_args,
    exact_signature_matches sigma labeled_args ->
    Forall (fun p => elaborated_arg_well_typed Se Sf Sc mu (fst p)) labeled_args ->
    full_app_candidate Se Sf Sc mu sigma (labeled_args_to_core labeled_args).
Proof.
  intros Se Sf Sc mu sigma labeled_args [aligned_args [Halign Hmatch]] Htyped.
  exists (List.map elaborated_arg_expr aligned_args). split.
  - eapply align_cases_map_payload. exact Halign.
  - eapply exact_aligned_exprs_plain_params.
    + eapply align_cases_preserves_Forall_payload; eauto.
    + exact Hmatch.
Qed.

(** Partial semantic matching plus well-typed elaborated arguments yields a
    core [partial_app_candidate]. *)
Theorem partial_signature_matches_partial_app_candidate :
  forall Se Sf Sc mu sigma labeled_args indices,
    partial_signature_matches sigma labeled_args indices ->
    Forall (fun p => elaborated_arg_well_typed Se Sf Sc mu (fst p)) labeled_args ->
    partial_app_candidate Se Sf Sc mu sigma (labeled_args_to_core labeled_args) indices.
Proof.
  intros Se Sf Sc mu sigma labeled_args indices [Hlt [Hmatch Htyped_match]] Htyped.
  repeat split.
  - unfold labeled_args_to_core. rewrite length_map. exact Hlt.
  - rewrite extract_cases_labeled_args_to_core. exact Hmatch.
  - eapply partial_labeled_core_args_plain_indices; eauto.
Qed.

(** Lifting the previous theorem through the [exact_choice_matches] witness
    gives a bridge from an elaboration choice for a whole call site to the
    core [full_app_candidate] judgment. *)
Theorem exact_choice_matches_full_app_candidate :
  forall analyze env call Se Sf Sc mu f sigma args,
    exact_choice_matches analyze env call (ExactChoice f sigma args) ->
    surface_call_args_well_typed Se Sf Sc mu call ->
    full_app_candidate Se Sf Sc mu sigma args.
Proof.
  intros analyze env call Se Sf Sc mu f sigma args Hchoice Htyped_call.
  inversion Hchoice as
    [resolved_name sigma' labeled_args Hname Hsigma Hin Hexact]; subst.
  eapply exact_signature_matches_full_app_candidate.
  - exact Hexact.
  - eapply in_enumerate_labeled_args_well_typed; eauto.
Qed.

(** The analogous bridge for partial choices. *)
Theorem partial_choice_matches_partial_app_candidate :
  forall analyze env call Se Sf Sc mu f sigma args indices,
    partial_choice_matches analyze env call (PartialChoice f sigma args indices) ->
    surface_call_args_well_typed Se Sf Sc mu call ->
    partial_app_candidate Se Sf Sc mu sigma args indices.
Proof.
  intros analyze env call Se Sf Sc mu f sigma args indices Hchoice Htyped_call.
  inversion Hchoice as
    [resolved_name sigma' labeled_args indices' Hname Hsigma Hin Hpartial]; subst.
  eapply partial_signature_matches_partial_app_candidate.
  - exact Hpartial.
  - eapply in_enumerate_labeled_args_well_typed; eauto.
Qed.

(** If an exact elaboration choice uses a declared monomorphic signature, then
    the resulting core application is well typed at the signature's return
    type. *)
Theorem exact_choice_matches_application_has_plain_type :
  forall analyze env call Se Sf Sc mu f sigma args,
    exact_choice_matches analyze env call (ExactChoice f sigma args) ->
    surface_call_args_well_typed Se Sf Sc mu call ->
    In sigma (Sf f) ->
    mode_compatible Se f mu ->
    monomorphic_signature sigma ->
    has_plain_type Se Sf Sc [] mu (EApp f args) (signature_return_ty sigma).
Proof.
  intros analyze env call Se Sf Sc mu f sigma args Hchoice Htyped_call Hsig Hmode Hmono.
  inversion Hchoice as
    [resolved_name sigma' labeled_args Hname Hsigma Hin [aligned_args [Halign Hmatch]]];
    subst.
  pose proof (in_enumerate_labeled_args_well_typed analyze (call_surface_args call)
    labeled_args Se Sf Sc mu Hin Htyped_call) as Htyped_labeled.
  pose proof (align_cases_preserves_Forall_payload elaborated_arg
    (elaborated_arg_well_typed Se Sf Sc mu)
    (extract_cases (signature_params sigma)) labeled_args aligned_args
    Halign Htyped_labeled) as Htyped_aligned.
  pose proof (exact_aligned_exprs_typed_params Se Sf Sc mu
    aligned_args (signature_params sigma) Htyped_aligned Hmatch) as Htyped_params.
  replace (signature_return_ty sigma) with
    (apply_subst
      (combine (signature_tvars sigma)
        (List.map snd ([] : list (tyvar_name * ty))))
      (signature_return_ty sigma)).
  2:{
    rewrite (monomorphic_bound_nil sigma [] Hmono).
    simpl. now rewrite apply_subst_nil.
  }
  exists (Some (signature_return_case sigma)).
  eapply T_App with (sigma := sigma) (theta := []).
  - exact Hsig.
  - exact Hmode.
  - unfold monomorphic_signature in Hmono. rewrite Hmono. reflexivity.
  - eapply align_cases_map_payload. exact Halign.
  - eapply typed_params_monomorphic_nil; eauto.
Qed.

(** If a partial elaboration choice uses a declared monomorphic signature,
    then the resulting core application is well typed at the residual arrow
    type computed by the missing parameters. *)
Theorem partial_choice_matches_application_has_plain_type :
  forall analyze env call Se Sf Sc mu f sigma args indices,
    partial_choice_matches analyze env call (PartialChoice f sigma args indices) ->
    surface_call_args_well_typed Se Sf Sc mu call ->
    In sigma (Sf f) ->
    mode_compatible Se f mu ->
    monomorphic_signature sigma ->
    has_plain_type Se Sf Sc [] mu (EApp f args)
      (List.fold_right TyArr
        (signature_return_ty sigma)
        (collect_at_indices
          (remaining_indices 0 (length (signature_params sigma)) indices)
          (signature_params sigma))).
Proof.
  intros analyze env call Se Sf Sc mu f sigma args indices
    Hchoice Htyped_call Hsig Hmode Hmono.
  inversion Hchoice as
    [resolved_name sigma' labeled_args indices' Hname Hsigma Hin [Hlt [Hmatch Htyped_match]]];
    subst.
  pose proof (in_enumerate_labeled_args_well_typed analyze (call_surface_args call)
    labeled_args Se Sf Sc mu Hin Htyped_call) as Htyped_labeled.
  pose proof (partial_labeled_core_args_typed_indices Se Sf Sc mu
    labeled_args (signature_params sigma) indices Htyped_labeled Htyped_match)
    as Htyped_indices.
  rewrite <- (monomorphic_partial_result_type_nil sigma indices Hmono).
  eapply partial_app_args_typed_has_plain_type with (theta := []).
  - exact Hsig.
  - exact Hmode.
  - unfold monomorphic_signature in Hmono. rewrite Hmono. reflexivity.
  - unfold labeled_args_to_core. rewrite length_map. exact Hlt.
  - rewrite extract_cases_labeled_args_to_core. exact Hmatch.
  - eapply typed_indices_monomorphic_nil; eauto.
Qed.

(** A unique exact elaboration result is therefore enough to recover the
    declarative static-semantics judgment for the resulting core
    application. *)
Theorem elaborate_call_unique_exact_has_plain_type :
  forall analyze env call Se Sf Sc mu f sigma args,
    elaborate_call analyze env call = ElabUnique (ExactChoice f sigma args) ->
    surface_call_args_well_typed Se Sf Sc mu call ->
    In sigma (Sf f) ->
    mode_compatible Se f mu ->
    monomorphic_signature sigma ->
    has_plain_type Se Sf Sc [] mu (EApp f args) (signature_return_ty sigma).
Proof.
  intros analyze env call Se Sf Sc mu f sigma args
    Helab Htyped Hsig Hmode Hmono.
  apply exact_choice_matches_application_has_plain_type with (analyze := analyze) (env := env) (call := call); auto.
  apply prioritized_exact_choice_matches.
  now apply elaborate_call_overload_sound.
Qed.

(** Likewise for a unique partial elaboration result. *)
Theorem elaborate_call_unique_partial_has_plain_type :
  forall analyze env call Se Sf Sc mu f sigma args indices,
    elaborate_call analyze env call = ElabUnique (PartialChoice f sigma args indices) ->
    surface_call_args_well_typed Se Sf Sc mu call ->
    In sigma (Sf f) ->
    mode_compatible Se f mu ->
    monomorphic_signature sigma ->
    has_plain_type Se Sf Sc [] mu (EApp f args)
      (List.fold_right TyArr
        (signature_return_ty sigma)
        (collect_at_indices
          (remaining_indices 0 (length (signature_params sigma)) indices)
          (signature_params sigma))).
Proof.
  intros analyze env call Se Sf Sc mu f sigma args indices
    Helab Htyped Hsig Hmode Hmono.
  pose proof (prioritized_partial_choice_matches analyze env call f sigma args indices
    (elaborate_call_overload_sound analyze env call
      (PartialChoice f sigma args indices) Helab)) as Hpartial.
  eapply partial_choice_matches_application_has_plain_type; eauto.
Qed.

(** On the semantic side, a unique exact elaboration result also determines
    the overload selected by the core dynamic semantics, provided the
    executable environment satisfies [fun_entry_ctx_ok] and the elaboration
    signatures agree with the declarative signature environment. *)
Theorem elaborate_call_unique_exact_full_app_resolves :
  forall analyze env call Se Sf Sc F mu f sigma args,
    elaboration_fun_ctx env = Sf ->
    elaborate_call analyze env call = ElabUnique (ExactChoice f sigma args) ->
    surface_call_args_well_typed Se Sf Sc mu call ->
    fun_entry_ctx_ok Se Sf Sc F ->
    exists entry,
      full_app_resolves Se Sf Sc F mu f args entry /\
      fun_entry_signature entry = sigma.
Proof.
  intros analyze env call Se Sf Sc F mu f sigma args
    Henvsig Helab Htyped_call Hfunenv.
  pose proof (prioritized_exact_choice_matches analyze env call f sigma args
    (elaborate_call_overload_sound analyze env call
      (ExactChoice f sigma args) Helab)) as Hexact.
  pose proof (exact_choice_matches_full_app_candidate
    analyze env call Se Sf Sc mu f sigma args Hexact Htyped_call) as Hcand.
  pose proof (exact_choice_matches_in_callable_signatures
    analyze env call f sigma args Hexact) as Hsigma_callable.
  pose proof (callable_signature_in_fun_ctx env f sigma Hsigma_callable) as Hsigma_env.
  rewrite Henvsig in Hsigma_env.
  destruct (fun_entry_ctx_complete_entry Se Sf Sc F f sigma Hfunenv Hsigma_env)
    as [entry [Hentry Hentry_sig]].
  exists entry. split.
  - split.
    + exact Hentry.
    + split.
      * rewrite Hentry_sig. exact Hcand.
      * intros entry' Hentry' Hcand'.
        destruct Hfunenv as [_ [_ [Huniq_full _]]].
        eapply Huniq_full; eauto.
        rewrite Hentry_sig. exact Hcand.
  - exact Hentry_sig.
Qed.

(** Unique partial elaboration at least implies the corresponding core partial
    candidate judgment, even without any extra completeness assumption about
    exact matching. *)
Theorem elaborate_call_unique_partial_partial_app_candidate :
  forall analyze env call Se Sf Sc mu f sigma args indices,
    elaborate_call analyze env call = ElabUnique (PartialChoice f sigma args indices) ->
    surface_call_args_well_typed Se Sf Sc mu call ->
    partial_app_candidate Se Sf Sc mu sigma args indices.
Proof.
  intros analyze env call Se Sf Sc mu f sigma args indices Helab Htyped.
  pose proof (prioritized_partial_choice_matches analyze env call f sigma args indices
    (elaborate_call_overload_sound analyze env call
      (PartialChoice f sigma args indices) Helab)) as Hpartial.
  eapply partial_choice_matches_partial_app_candidate; eauto.
Qed.

(** This is the main exact-call correctness theorem for the current
    elaboration formalization.  When elaboration reports one unique exact
    overload, we get four facts at once:

    - the reported choice really is a prioritized semantic match;
    - no second prioritized choice exists;
    - the corresponding core application is well typed;
    - the core dynamic semantics resolves the call to a matching entry.

    Together, these summarize the implementation-side correctness story for
    exact overload elaboration. *)
Theorem elaborate_call_unique_exact_correct :
  forall analyze env call Se Sf Sc F mu f sigma args,
    elaboration_fun_ctx env = Sf ->
    elaborate_call analyze env call = ElabUnique (ExactChoice f sigma args) ->
    surface_call_args_well_typed Se Sf Sc mu call ->
    In sigma (Sf f) ->
    mode_compatible Se f mu ->
    monomorphic_signature sigma ->
    fun_entry_ctx_ok Se Sf Sc F ->
    prioritized_choice_matches analyze env call (ExactChoice f sigma args) /\
    (forall choice',
      prioritized_choice_matches analyze env call choice' ->
      choice' = ExactChoice f sigma args) /\
    has_plain_type Se Sf Sc [] mu (EApp f args) (signature_return_ty sigma) /\
    exists entry,
      full_app_resolves Se Sf Sc F mu f args entry /\
      fun_entry_signature entry = sigma.
Proof.
  intros analyze env call Se Sf Sc F mu f sigma args
    Henvsig Helab Htyped_call Hsig Hmode Hmono Hfunenv.
  repeat split.
  - now apply elaborate_call_overload_sound with (choice := ExactChoice f sigma args).
  - intros choice' Hmatch.
    exact (elaborate_call_overload_unique analyze env call
      (ExactChoice f sigma args) choice' Helab Hmatch).
  - eapply elaborate_call_unique_exact_has_plain_type; eauto.
  - eapply elaborate_call_unique_exact_full_app_resolves; eauto.
Qed.

(** The partial-call analogue packages the verified consequences of a unique
    partial elaboration result.  Since the current bridge to the core
    operational semantics is only proved for exact applications, the partial
    theorem stops at the declarative candidate and static-semantics
    judgments. *)
Theorem elaborate_call_unique_partial_correct :
  forall analyze env call Se Sf Sc mu f sigma args indices,
    elaborate_call analyze env call = ElabUnique (PartialChoice f sigma args indices) ->
    surface_call_args_well_typed Se Sf Sc mu call ->
    In sigma (Sf f) ->
    mode_compatible Se f mu ->
    monomorphic_signature sigma ->
    prioritized_choice_matches analyze env call (PartialChoice f sigma args indices) /\
    (forall choice',
      prioritized_choice_matches analyze env call choice' ->
      choice' = PartialChoice f sigma args indices) /\
    partial_app_candidate Se Sf Sc mu sigma args indices /\
    has_plain_type Se Sf Sc [] mu (EApp f args)
      (List.fold_right TyArr
        (signature_return_ty sigma)
        (collect_at_indices
          (remaining_indices 0 (length (signature_params sigma)) indices)
          (signature_params sigma))).
Proof.
  intros analyze env call Se Sf Sc mu f sigma args indices
    Helab Htyped_call Hsig Hmode Hmono.
  split.
  - now apply elaborate_call_overload_sound with
      (choice := PartialChoice f sigma args indices).
  - split.
    + intros choice' Hmatch.
      exact (elaborate_call_overload_unique analyze env call
        (PartialChoice f sigma args indices) choice' Helab Hmatch).
    + split.
      * eapply elaborate_call_unique_partial_partial_app_candidate; eauto.
      * eapply elaborate_call_unique_partial_has_plain_type; eauto.
Qed.

(* ================================================================= *)
(** ** Compile-Time Resolved Call Heads *)
(* ================================================================= *)

(** The bridge theorems above still target the overloaded core syntax of
    the split core development, where calls are represented by unresolved [EApp]
    nodes.  To capture the implementation intuition more directly, we also
    package compile-time overload choices into a small resolved call-head
    layer.  A resolved call head stores the chosen [fun_entry] explicitly, so
    its execution does not need to search the function environment again. *)

(** A resolved call-head state is either:

    - a fully resolved exact application;
    - a fully resolved partial application; or
    - an ordinary core expression reached after the call head has finished
      reducing, for example by beta-reducing to a clause body.

    The final [ResolvedExpr] form lets the head-local semantics hand control
    back to the ordinary core language once overload selection is no longer
    relevant. *)
Inductive resolved_call_state : Type :=
  | ResolvedExactCall
      (resolved_name : fun_name)
      (resolved_entry : fun_entry)
      (resolved_args : list (expr * case_label))
  | ResolvedPartialCall
      (resolved_name : fun_name)
      (resolved_entry : fun_entry)
      (resolved_args : list (expr * case_label))
      (resolved_indices : list nat)
  | ResolvedExpr
      (resolved_expr_payload : expr).

(** Erasing a resolved call-head state forgets the stored entry and produces
    the corresponding ordinary core expression.  This is the connection point
    to the core semantics in [KipCore.Dynamic]. *)
Definition erase_resolved_call_state
  (state : resolved_call_state) : expr :=
  match state with
  | ResolvedExactCall f _ args => EApp f args
  | ResolvedPartialCall f _ args _ => EApp f args
  | ResolvedExpr e => e
  end.

(** Well-formedness for resolved call heads records the static facts that the
    head-local semantics relies on:

    - the chosen entry really comes from the ambient function environment;
    - the stored arguments are a full or partial candidate for that entry's
      signature.

    Unlike [full_app_resolves] and [partial_app_resolves], this predicate does
    not perform overload selection.  It merely records that selection has
    already happened and that the stored entry is compatible with the call
    head. *)
Inductive resolved_call_state_ok
  (F : fun_entry_ctx) (Se : effect_ctx) (Sf : fun_ctx)
  (Sc : ctor_ctx) (mu : eff_mode)
  : resolved_call_state -> Prop :=
  | RCS_OK_Exact :
      forall f entry args,
        In entry (F f) ->
        full_app_candidate Se Sf Sc mu (fun_entry_signature entry) args ->
        resolved_call_state_ok F Se Sf Sc mu
          (ResolvedExactCall f entry args)
  | RCS_OK_Partial :
      forall f entry args indices,
        In entry (F f) ->
        partial_app_candidate Se Sf Sc mu (fun_entry_signature entry) args indices ->
        resolved_call_state_ok F Se Sf Sc mu
          (ResolvedPartialCall f entry args indices).

(** Typing for resolved call heads is stated by erasing back to the ordinary
    core expression and reusing [has_plain_type].  This keeps the resolved
    layer lightweight while still giving a direct theorem that compile-time
    resolved calls are well typed. *)
Definition resolved_call_state_has_plain_type
  (Se : effect_ctx) (Sf : fun_ctx) (Sc : ctor_ctx)
  (mu : eff_mode) (state : resolved_call_state) (tau : ty) : Prop :=
  has_plain_type Se Sf Sc [] mu (erase_resolved_call_state state) tau.

(** The head-local execution relation for resolved call heads reuses the core
    argument-stepping and clause-matching machinery, but it never consults
    [full_app_resolves] or [partial_app_resolves].  The chosen [fun_entry] is
    already stored in the term, so no overload search occurs during these
    steps. *)
Inductive resolved_call_head_step
  (F : fun_entry_ctx) (Sc : ctor_ctx)
  (Se : effect_ctx) (Sf : fun_ctx) (mu : eff_mode)
  : resolved_call_state -> resolved_call_state -> Prop :=
  | RCHS_Partial_Arg :
      forall f entry args args' indices,
        step_args F Sc (Se:=Se) (Sf:=Sf) (mu:=mu) args args' ->
        resolved_call_head_step F Sc Se Sf mu
          (ResolvedPartialCall f entry args indices)
          (ResolvedPartialCall f entry args' indices)
  | RCHS_Exact_Canon :
      forall f entry args args',
        canonical_args
          (extract_cases (signature_params (fun_entry_signature entry)))
          args = Some args' ->
        args <> args' ->
        resolved_call_head_step F Sc Se Sf mu
          (ResolvedExactCall f entry args)
          (ResolvedExactCall f entry args')
  | RCHS_Exact_Arg :
      forall f entry args payloads',
        canonical_args
          (extract_cases (signature_params (fun_entry_signature entry)))
          args = Some args ->
        step_exprs F Sc (Se:=Se) (Sf:=Sf) (mu:=mu)
          (List.map fst args) payloads' ->
        resolved_call_head_step F Sc Se Sf mu
          (ResolvedExactCall f entry args)
          (ResolvedExactCall f entry
            (combine payloads'
              (extract_cases (signature_params (fun_entry_signature entry)))))
  | RCHS_Exact_Beta :
      forall f entry cl args rho,
        canonical_args
          (extract_cases (signature_params (fun_entry_signature entry)))
          args = Some args ->
        value_labeled_args F Sc (Se:=Se) (Sf:=Sf) (mu:=mu) args ->
        In cl (fun_entry_clauses entry) ->
        clause_matches Sc (fun_entry_signature entry) cl args rho ->
        resolved_call_head_step F Sc Se Sf mu
          (ResolvedExactCall f entry args)
          (ResolvedExpr (subst_env rho (clause_body cl))).

(** A well-formed resolved exact call determines the corresponding
    declarative [full_app_resolves] proof.  This is the link used to show
    that resolved head steps are sound with respect to the original core
    semantics. *)
Lemma resolved_call_state_ok_exact_resolves :
  forall F Se Sf Sc mu f entry args,
    fun_entry_ctx_ok Se Sf Sc F ->
    resolved_call_state_ok F Se Sf Sc mu (ResolvedExactCall f entry args) ->
    full_app_resolves Se Sf Sc F mu f args entry.
Proof.
  intros F Se Sf Sc mu f entry args Hfunenv Hok.
  inversion Hok as [f' entry' args' Hentry Hcand |]; subst.
  split; [exact Hentry |].
  split; [exact Hcand |].
  intros entry' Hentry' Hcand'.
  destruct Hfunenv as [_ [_ [Huniq_full _]]].
  eapply Huniq_full; eauto.
Qed.

(** The partial analogue packages a stored entry and partial candidate into
    the declarative [partial_app_resolves] judgment. *)
Lemma resolved_call_state_ok_partial_resolves :
  forall F Se Sf Sc mu f entry args indices,
    fun_entry_ctx_ok Se Sf Sc F ->
    resolved_call_state_ok F Se Sf Sc mu
      (ResolvedPartialCall f entry args indices) ->
    partial_app_resolves Se Sf Sc F mu f args entry indices.
Proof.
  intros F Se Sf Sc mu f entry args indices Hfunenv Hok.
  inversion Hok as [|f' entry' args' indices' Hentry Hcand]; subst.
  split; [exact Hentry |].
  split; [exact Hcand |].
  split.
  - intros entry' Hentry' Hfull'.
    destruct Hfunenv as [_ [_ [_ [_ Hno_overlap]]]].
    eapply (Hno_overlap mu f entry' entry args indices); eauto.
  - intros entry' indices' Hentry' Hcand'.
    destruct Hfunenv as [_ [_ [_ [Huniq_partial _]]]].
    eapply (Huniq_partial mu f entry' entry args indices' indices); eauto.
Qed.

(** Every resolved head step is sound with respect to the original core
    [step] relation after erasure.  This is the central statement saying that
    once elaboration has chosen an entry, the call head can execute without
    re-running overload resolution. *)
Lemma resolved_call_head_step_erases_to_core_step :
  forall F Se Sf Sc mu state state',
    fun_entry_ctx_ok Se Sf Sc F ->
    resolved_call_state_ok F Se Sf Sc mu state ->
    resolved_call_head_step F Sc Se Sf mu state state' ->
    step F Sc (Se:=Se) (Sf:=Sf) (mu:=mu)
      (erase_resolved_call_state state)
      (erase_resolved_call_state state').
Proof.
  intros F Se Sf Sc mu state state' Hfunenv Hstate_ok Hstep.
  inversion Hstep; subst; simpl.
  - pose proof (resolved_call_state_ok_partial_resolves
      F Se Sf Sc mu f entry args indices Hfunenv Hstate_ok) as Hresolve.
    eapply ST_App_Partial_Arg; eauto.
  - pose proof (resolved_call_state_ok_exact_resolves
      F Se Sf Sc mu f entry args Hfunenv Hstate_ok) as Hresolve.
    eapply ST_App_Canon; eauto.
  - pose proof (resolved_call_state_ok_exact_resolves
      F Se Sf Sc mu f entry args Hfunenv Hstate_ok) as Hresolve.
    eapply ST_App_Arg; eauto.
  - pose proof (resolved_call_state_ok_exact_resolves
      F Se Sf Sc mu f entry args Hfunenv Hstate_ok) as Hresolve.
    eapply ST_App_Beta; eauto.
Qed.

(** Unique exact elaboration therefore produces a resolved exact call head
    that is:

    - backed by the chosen entry;
    - well typed;
    - executable via [resolved_call_head_step], whose rules never search the
      overload environment. *)
Theorem elaborate_call_unique_exact_produces_resolved_call :
  forall analyze env call Se Sf Sc F mu f sigma args,
    elaboration_fun_ctx env = Sf ->
    elaborate_call analyze env call = ElabUnique (ExactChoice f sigma args) ->
    surface_call_args_well_typed Se Sf Sc mu call ->
    In sigma (Sf f) ->
    mode_compatible Se f mu ->
    monomorphic_signature sigma ->
    fun_entry_ctx_ok Se Sf Sc F ->
    exists entry,
      fun_entry_signature entry = sigma /\
      resolved_call_state_ok F Se Sf Sc mu
        (ResolvedExactCall f entry args) /\
      resolved_call_state_has_plain_type Se Sf Sc mu
        (ResolvedExactCall f entry args) (signature_return_ty sigma) /\
      (forall state',
        resolved_call_head_step F Sc Se Sf mu
          (ResolvedExactCall f entry args) state' ->
        step F Sc (Se:=Se) (Sf:=Sf) (mu:=mu)
          (EApp f args) (erase_resolved_call_state state')).
Proof.
  intros analyze env call Se Sf Sc F mu f sigma args
    Henvsig Helab Htyped_call Hsig Hmode Hmono Hfunenv.
  destruct (elaborate_call_unique_exact_full_app_resolves
    analyze env call Se Sf Sc F mu f sigma args
    Henvsig Helab Htyped_call Hfunenv) as [entry [Hresolve Hentry_sig]].
  exists entry. repeat split.
  - exact Hentry_sig.
  - destruct Hresolve as [Hentry [Hcand _]].
    constructor; assumption.
  - unfold resolved_call_state_has_plain_type.
    eapply elaborate_call_unique_exact_has_plain_type; eauto.
  - intros state' Hhead_step.
    eapply (resolved_call_head_step_erases_to_core_step
      F Se Sf Sc mu (ResolvedExactCall f entry args) state'); eauto.
    destruct Hresolve as [Hentry [Hcand _]].
    constructor; assumption.
Qed.

(** Unique partial elaboration likewise produces a resolved partial call
    head.  Since partial applications are not yet beta-redexes, this theorem
    packages the chosen entry, the residual static-semantics judgment, and
    the same head-local execution guarantee for argument evaluation. *)
Theorem elaborate_call_unique_partial_produces_resolved_call :
  forall analyze env call Se Sf Sc F mu f sigma args indices,
    elaboration_fun_ctx env = Sf ->
    elaborate_call analyze env call = ElabUnique (PartialChoice f sigma args indices) ->
    surface_call_args_well_typed Se Sf Sc mu call ->
    In sigma (Sf f) ->
    mode_compatible Se f mu ->
    monomorphic_signature sigma ->
    fun_entry_ctx_ok Se Sf Sc F ->
    exists entry,
      fun_entry_signature entry = sigma /\
      resolved_call_state_ok F Se Sf Sc mu
        (ResolvedPartialCall f entry args indices) /\
      resolved_call_state_has_plain_type Se Sf Sc mu
        (ResolvedPartialCall f entry args indices)
        (List.fold_right TyArr
          (signature_return_ty sigma)
          (collect_at_indices
            (remaining_indices 0 (length (signature_params sigma)) indices)
            (signature_params sigma))) /\
      (forall state',
        resolved_call_head_step F Sc Se Sf mu
          (ResolvedPartialCall f entry args indices) state' ->
        step F Sc (Se:=Se) (Sf:=Sf) (mu:=mu)
          (EApp f args) (erase_resolved_call_state state')).
Proof.
  intros analyze env call Se Sf Sc F mu f sigma args indices
    Henvsig Helab Htyped_call Hsig Hmode Hmono Hfunenv.
  destruct (fun_entry_ctx_complete_entry Se Sf Sc F f sigma Hfunenv Hsig)
    as [entry [Hentry Hentry_sig]].
  exists entry. repeat split.
  - exact Hentry_sig.
  - constructor.
    + exact Hentry.
    + rewrite Hentry_sig.
      eapply elaborate_call_unique_partial_partial_app_candidate; eauto.
  - unfold resolved_call_state_has_plain_type.
    eapply elaborate_call_unique_partial_has_plain_type; eauto.
  - intros state' Hhead_step.
    eapply (resolved_call_head_step_erases_to_core_step
      F Se Sf Sc mu (ResolvedPartialCall f entry args indices) state'); eauto.
    constructor.
    + exact Hentry.
    + rewrite Hentry_sig.
      eapply elaborate_call_unique_partial_partial_app_candidate; eauto.
Qed.
