(** * Kip Dynamic Semantics *)
(** Dynamic environments, values, and small-step evaluation. *)

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
Import ListNotations.
Open Scope string_scope.

(* ================================================================= *)
(** ** Core Dynamic Semantics *)
(* ================================================================= *)

(** This section defines:
    - [has_plain_type]: the "erased" static-semantics judgment that forgets
      the result-case annotation (used by preservation, which only
      needs to track the ordinary type);
    - values, substitution, and the small-step [step] relation;
    - the [fun_entry_ctx_ok] invariant connecting the dynamic function
      environment with the declarative static semantics. *)

(** The parameters [Se], [Sf], and [Sc] are the global environments. The
    indices are a typing context [Gamma], an effect mode [mu], an expression
    [e], and an ordinary type [tau]; [has_plain_type Se Sf Sc Gamma mu e
    tau] means that [e] has type [tau] for some result-case annotation in
    the static semantics. *)
Definition has_plain_type
  (Se : effect_ctx) (Sf : fun_ctx) (Sc : ctor_ctx)
  (Gamma : val_ctx) (mu : eff_mode) (e : expr) (tau : ty) : Prop :=
  exists kres, has_type Se Sf Sc Gamma mu e (tau, kres).

(** This is the forgetful map from [has_type] to [has_plain_type]: we keep
    the type and drop the result-case witness. *)
Lemma has_type_plain :
  forall Se Sf Sc Gamma mu e tau kres,
    has_type Se Sf Sc Gamma mu e (tau, kres) ->
    has_plain_type Se Sf Sc Gamma mu e tau.
Proof. unfold has_plain_type; eauto. Qed.

#[export] Hint Resolve has_type_plain : core.

(** Convenience: extract the effect mode for a function name. *)
Definition fun_mode (Se : effect_ctx) (f : fun_name) : eff_mode :=
  if Se f then Eff else Pure.

(** [mode_compatible Se f mu] is the side condition saying that calling [f]
    in mode [mu] is allowed: effectful functions force [mu = Eff]. *)
Definition mode_compatible (Se : effect_ctx) (f : fun_name) (mu : eff_mode) : Prop :=
  Se f = true -> mu = Eff.

(** Executable function environments store one entry per overload of a
    function name.  Each entry packages a monomorphic signature together
    with the clauses used when that overload is selected in the dynamic
    semantics. *)
Record fun_entry := mk_fun_entry {
  fun_entry_signature : signature;
  fun_entry_clauses   : fun_def;
}.

(** Dynamic function environments map a function name to its executable
    overload entries. *)
Definition fun_entry_ctx := fun_name -> list fun_entry.

(** [monomorphic_signature sigma] says that [sigma] quantifies over no type
    variables and is therefore already fully instantiated. *)
Definition monomorphic_signature (sigma : signature) : Prop :=
  signature_tvars sigma = nil.

(** [pat_bound_vars] lists the variables bound by a pattern. *)
Fixpoint pat_bound_vars (p : pat) : list var_name :=
  match p with
  | PWild => nil
  | PVarPat x => [x]
  | PLit _ => nil
  | PCtorPat _ args =>
    List.concat (List.map (fun pc => pat_bound_vars (fst pc)) args)
  end.

(** Capture-avoiding substitution for the first-order core language.
    Match branches and binders stop substitution beneath variables that
    would be captured. *)
Fixpoint subst (x : var_name) (v : expr) (e : expr) : expr :=
  match e with
  | EVar y =>
    if String.eqb x y then v else EVar y
  | ELit c => ELit c
  | EAscribe e1 t =>
    EAscribe (subst x v e1) t
  | EApp f args =>
    EApp f (List.map (fun p => (subst x v (fst p), snd p)) args)
  | ECtor C args =>
    ECtor C (List.map (fun p => (subst x v (fst p), snd p)) args)
  | EMatch scrut branches =>
    EMatch (subst x v scrut)
      (List.map (fun pb =>
        if in_dec String.string_dec x (pat_bound_vars (fst pb))
        then pb
        else (fst pb, subst x v (snd pb))
      ) branches)
  | ELet y e1 e2 =>
    ELet y (subst x v e1)
      (if String.eqb x y then e2 else subst x v e2)
  | ESeq e1 e2 =>
    ESeq (subst x v e1) (subst x v e2)
  | EBind y e1 e2 =>
    EBind y (subst x v e1)
      (if String.eqb x y then e2 else subst x v e2)
  end.

(** Apply a whole substitution environment from left to right. *)
Fixpoint subst_env (rho : list (var_name * expr)) (e : expr) : expr :=
  match rho with
  | nil => e
  | (x, v) :: rho' => subst_env rho' (subst x v e)
  end.

(** Lookup in a substitution environment, used by environment-typing lemmas to
    recover the expression assigned to a bound variable. *)
Fixpoint expr_lookup (rho : list (var_name * expr)) (x : var_name) : option expr :=
  match rho with
  | nil => None
  | (y, v) :: rho' =>
    if String.eqb x y then Some v else expr_lookup rho' x
  end.

(** [full_app_candidate Se Sf Sc mu sigma args] says that the application
    [EApp f args] matches the full parameter list of [sigma] in mode [mu].
    The call-site order may differ from the signature order: payloads are
    judged after case alignment. *)
Definition full_app_candidate
  (Se : effect_ctx) (Sf : fun_ctx) (Sc : ctor_ctx)
  (mu : eff_mode) (sigma : signature) (args : list (expr * case_label)) : Prop :=
  exists args_aligned,
    align_cases (extract_cases (signature_params sigma)) args args_aligned /\
    Forall2 (fun arg param =>
      has_plain_type Se Sf Sc [] mu arg (fst param)
    ) args_aligned (signature_params sigma).

(** [partial_app_candidate Se Sf Sc mu sigma args indices] says that the
    call [EApp f args] is a well-typed under-saturated application of [sigma].
    The list [indices] records which signature parameters the provided
    arguments fill. *)
Definition partial_app_candidate
  (Se : effect_ctx) (Sf : fun_ctx) (Sc : ctor_ctx)
  (mu : eff_mode) (sigma : signature) (args : list (expr * case_label))
  (indices : list nat) : Prop :=
  length args < length (signature_params sigma) /\
  match_partial
    (extract_cases (signature_params sigma))
    (extract_cases args)
    indices /\
  Forall2 (fun arg idx =>
    exists param,
      nth_error (signature_params sigma) idx = Some param /\
      has_plain_type Se Sf Sc [] mu (fst arg) (fst param)
  ) args indices.

(** [full_app_resolves Se Sf Sc F mu f args entry] says that [entry] is the
    unique overload selected for the full application [EApp f args] in the
    dynamic semantics at mode [mu]. *)
Definition full_app_resolves
  (Se : effect_ctx) (Sf : fun_ctx) (Sc : ctor_ctx)
  (F : fun_entry_ctx) (mu : eff_mode) (f : fun_name)
  (args : list (expr * case_label)) (entry : fun_entry) : Prop :=
  In entry (F f) /\
  full_app_candidate Se Sf Sc mu (fun_entry_signature entry) args /\
  (forall entry',
    In entry' (F f) ->
    full_app_candidate Se Sf Sc mu (fun_entry_signature entry') args ->
    fun_entry_signature entry' = fun_entry_signature entry).

(** [partial_app_resolves Se Sf Sc F mu f args entry indices] says that
    [entry] is the unique overload selected for the partial application
    [EApp f args] in the dynamic semantics at mode [mu].  Exact matches take
    precedence: partial resolution is only allowed when no full application
    candidate exists. *)
Definition partial_app_resolves
  (Se : effect_ctx) (Sf : fun_ctx) (Sc : ctor_ctx)
  (F : fun_entry_ctx) (mu : eff_mode) (f : fun_name)
  (args : list (expr * case_label)) (entry : fun_entry) (indices : list nat)
  : Prop :=
  In entry (F f) /\
  partial_app_candidate Se Sf Sc mu (fun_entry_signature entry) args indices /\
  (forall entry',
    In entry' (F f) ->
    full_app_candidate Se Sf Sc mu (fun_entry_signature entry') args ->
    False) /\
  (forall entry' indices',
    In entry' (F f) ->
    partial_app_candidate Se Sf Sc mu (fun_entry_signature entry') args indices' ->
    fun_entry_signature entry' = fun_entry_signature entry).

(** The parameters [F], [Sc], [Se], [Sf], and [mu] are the ambient dynamic
    and static environments. The single index is an expression [e];
    [value F Sc e] says that [e] is a finished value for the dynamic
    semantics at those ambient parameters. *)
Inductive value
  (F : fun_entry_ctx) (Sc : ctor_ctx)
  (Se : effect_ctx) (Sf : fun_ctx) (mu : eff_mode) : expr -> Prop :=
  (** Literals are finished values. *)
  | V_Lit : forall c,
      value F Sc Se Sf mu (ELit c)
  (** Canonical constructor applications with value payloads are finished
      data values. *)
  | V_Ctor : forall C sigma args,
      Sc C = Some sigma ->
      canonical_args (extract_cases (signature_params sigma)) args = Some args ->
      Forall (fun p => value F Sc Se Sf mu (fst p)) args ->
      value F Sc Se Sf mu (ECtor C args)
  (** There is no separate expression form for bare function values in this
      core language: named functions live in the executable [fun_entry_ctx], and the
      only expression form for them is [EApp f args].  Consequently, a
      function value is represented exactly by an application that has not yet
      received enough arguments to fire.  In particular, for a positive-arity
      function, the "bare function" case is [EApp f []]. Fully-saturated
      applications are not values because they can still canonicalize, step
      arguments, or beta-reduce. *)
  | V_PartialApp : forall f entry args indices,
      partial_app_resolves Se Sf Sc F mu f args entry indices ->
      Forall (fun p => value F Sc Se Sf mu (fst p)) args ->
      value F Sc Se Sf mu (EApp f args).

(** [value_labeled_args F Sc args] is the pointwise statement that every
    payload in the labeled argument list [args] is already a value. *)
Definition value_labeled_args
  (F : fun_entry_ctx) (Sc : ctor_ctx)
  (Se : effect_ctx) (Sf : fun_ctx) (mu : eff_mode)
  (args : list (expr * case_label)) : Prop :=
  Forall (fun p => value F Sc Se Sf mu (fst p)) args.

(** [value_payloads F Sc args] is the unlabeled analogue of
    [value_labeled_args]: every payload expression in [args] is a value. *)
Definition value_payloads
  (F : fun_entry_ctx) (Sc : ctor_ctx)
  (Se : effect_ctx) (Sf : fun_ctx) (mu : eff_mode)
  (args : list expr) : Prop :=
  Forall (value F Sc Se Sf mu) args.

(** [clause_core_ok Se Sf Sc f sigma cl] packages the local static facts
    about the clause [cl] that beta-reduction of a call to [f] at signature
    [sigma] needs. *)
Definition clause_core_ok
  (Se : effect_ctx) (Sf : fun_ctx) (Sc : ctor_ctx)
  (f : fun_name) (sigma : signature) (cl : fun_clause) : Prop :=
  clause_name cl = f /\
  monomorphic_signature sigma /\
  exists pats_aligned Gammas,
    align_cases (extract_cases (signature_params sigma)) (clause_pats cl) pats_aligned /\
    NoDup (List.concat (List.map pat_bound_vars pats_aligned)) /\
    length Gammas = length pats_aligned /\
    Forall2 (fun (pg : pat * val_ctx) (tp : signature_param) =>
      pat_bind Sc (fst pg) (fst tp) (snd pg)
    ) (combine pats_aligned Gammas) (signature_params sigma) /\
    forall mu,
      mode_compatible Se f mu ->
      has_plain_type Se Sf Sc (List.concat Gammas) mu
        (clause_body cl) (signature_return_ty sigma).

(** [fun_entry_ctx_ok Se Sf Sc F] is the global invariant saying that the
    executable environment [F] agrees with the declarative signatures,
    clause typing facts, semantic exhaustiveness, and overload-resolution
    discipline.  Overload resolution in the dynamic semantics is still
    static/type-directed: for a fixed function name and typed argument list
    there is at most one matching full overload, at most one matching partial
    overload, and the full match wins whenever both would otherwise apply. *)
Definition fun_entry_ctx_ok
  (Se : effect_ctx) (Sf : fun_ctx) (Sc : ctor_ctx) (F : fun_entry_ctx) : Prop :=
  (forall f entry,
    In entry (F f) ->
    In (fun_entry_signature entry) (Sf f) /\
    monomorphic_signature (fun_entry_signature entry) /\
    Forall (clause_core_ok Se Sf Sc f (fun_entry_signature entry)) (fun_entry_clauses entry) /\
    forall mu,
      mode_compatible Se f mu ->
      clauses_exhaustive Se Sf Sc mu
        (fun_entry_signature entry) (fun_entry_clauses entry)) /\
  (forall f sigma,
    In sigma (Sf f) ->
    exists entry, In entry (F f) /\ fun_entry_signature entry = sigma) /\
  (forall mu f entry1 entry2 args,
    In entry1 (F f) ->
    In entry2 (F f) ->
    full_app_candidate Se Sf Sc mu (fun_entry_signature entry1) args ->
    full_app_candidate Se Sf Sc mu (fun_entry_signature entry2) args ->
    fun_entry_signature entry1 = fun_entry_signature entry2) /\
  (forall mu f entry1 entry2 args indices1 indices2,
    In entry1 (F f) ->
    In entry2 (F f) ->
    partial_app_candidate Se Sf Sc mu (fun_entry_signature entry1) args indices1 ->
    partial_app_candidate Se Sf Sc mu (fun_entry_signature entry2) args indices2 ->
    fun_entry_signature entry1 = fun_entry_signature entry2) /\
  (forall mu f entry_full entry_partial args indices,
    In entry_full (F f) ->
    In entry_partial (F f) ->
    full_app_candidate Se Sf Sc mu (fun_entry_signature entry_full) args ->
    partial_app_candidate Se Sf Sc mu (fun_entry_signature entry_partial) args indices ->
    False).

(** The parameters [Se], [Sf], [Sc], and [mu] are the ambient typing
    relations used to check substituted expressions. The indices are a
    substitution environment [rho] and a typing context [Gamma];
    [subst_env_typed Se Sf Sc mu rho Gamma] says that [rho] provides closed
    expressions of exactly the types listed in [Gamma]. *)
Inductive subst_env_typed
  (Se : effect_ctx) (Sf : fun_ctx) (Sc : ctor_ctx) (mu : eff_mode)
  : list (var_name * expr) -> val_ctx -> Prop :=
  (** The empty substitution environment realizes the empty typing context. *)
  | SET_nil :
      subst_env_typed Se Sf Sc mu [] []
  (** Extending a typed substitution environment with a closed typed value
      realizes the correspondingly extended context. *)
  | SET_cons : forall x v rho tau Gamma kres,
      has_type Se Sf Sc [] mu v (tau, kres) ->
      subst_env_typed Se Sf Sc mu rho Gamma ->
      subst_env_typed Se Sf Sc mu ((x, v) :: rho) ((x, tau) :: Gamma).

(** The parameters [F], [Sc], [Se], [Sf], and [mu] are the ambient dynamic
    and static environments used during evaluation. This mutual block has
    indices [es es' ] for [step_exprs], [args args' ] for [step_args], and
    [e e' ] for [step]; each judgment says the left index takes one small
    evaluation step to the right. *)
Inductive step_exprs
  (F : fun_entry_ctx) (Sc : ctor_ctx)
  (Se : effect_ctx) (Sf : fun_ctx) (mu : eff_mode)
  : list expr -> list expr -> Prop :=
  (** Step the head expression of a payload list. *)
  | SE_Here : forall e e' rest,
      step F Sc Se Sf mu e e' ->
      step_exprs F Sc Se Sf mu (e :: rest) (e' :: rest)
  (** Once the head is already a value, step somewhere in the tail. *)
  | SE_There : forall e rest rest',
      value F Sc Se Sf mu e ->
      step_exprs F Sc Se Sf mu rest rest' ->
      step_exprs F Sc Se Sf mu (e :: rest) (e :: rest')

  (** The parameters [Se], [Sf], [F], [Sc], and [mu] are the ambient static
      and dynamic environments. The indices are labeled argument lists [args]
      and [args']; [step_args Se Sf F Sc mu args args'] says that one payload
      inside [args] takes a single evaluation step, preserving the
      surrounding case labels. *)
with step_args
  (F : fun_entry_ctx) (Sc : ctor_ctx)
  (Se : effect_ctx) (Sf : fun_ctx) (mu : eff_mode)
  : list (expr * case_label) -> list (expr * case_label) -> Prop :=
  (** Step the payload of the first labeled argument. *)
  | SA_Here : forall e e' c rest,
      step F Sc Se Sf mu e e' ->
      step_args F Sc Se Sf mu ((e, c) :: rest) ((e', c) :: rest)
  (** Preserve a value prefix and step a later labeled argument. *)
  | SA_There : forall e c rest rest',
      value F Sc Se Sf mu e ->
      step_args F Sc Se Sf mu rest rest' ->
      step_args F Sc Se Sf mu ((e, c) :: rest) ((e, c) :: rest')

  (** The parameters [Se], [Sf], [F], [Sc], and [mu] are the ambient static
      and dynamic environments. The indices are expressions [e] and [e'];
      [step Se Sf F Sc mu e e'] is the one-step small-step evaluation
      relation for expressions. *)
with step
  (F : fun_entry_ctx) (Sc : ctor_ctx)
  (Se : effect_ctx) (Sf : fun_ctx) (mu : eff_mode)
  : expr -> expr -> Prop :=
  (** Propagate a step under an ascription. *)
  | ST_Ascribe : forall e e' t,
      step F Sc Se Sf mu e e' ->
      step F Sc Se Sf mu (EAscribe e t) (EAscribe e' t)
  (** Remove an ascription once its payload is a value. *)
  | ST_Ascribe_Value : forall v t,
      value F Sc Se Sf mu v ->
      step F Sc Se Sf mu (EAscribe v t) v
  (** Partial applications step one labeled argument at a time. *)
  | ST_App_Partial_Arg : forall f entry args args' indices,
      partial_app_resolves Se Sf Sc F mu f args entry indices ->
      step_args F Sc Se Sf mu args args' ->
      step F Sc Se Sf mu (EApp f args) (EApp f args')
  (** Fully saturated applications first canonicalize their argument order. *)
  | ST_App_Canon : forall f entry args args',
      full_app_resolves Se Sf Sc F mu f args entry ->
      canonical_args (extract_cases (signature_params (fun_entry_signature entry))) args = Some args' ->
      args <> args' ->
      step F Sc Se Sf mu (EApp f args) (EApp f args')
  (** Once an application is canonical, evaluation steps inside its payload
      list. *)
  | ST_App_Arg : forall f entry args payloads',
      full_app_resolves Se Sf Sc F mu f args entry ->
      canonical_args (extract_cases (signature_params (fun_entry_signature entry))) args = Some args ->
      step_exprs F Sc Se Sf mu (List.map fst args) payloads' ->
      step F Sc Se Sf mu (EApp f args)
        (EApp f (combine payloads' (extract_cases (signature_params (fun_entry_signature entry)))))
  (** A fully matched application beta-reduces by selecting an exhaustive
      clause and applying its substitution environment. *)
  | ST_App_Beta : forall f entry cl args rho,
      full_app_resolves Se Sf Sc F mu f args entry ->
      canonical_args (extract_cases (signature_params (fun_entry_signature entry))) args = Some args ->
      value_labeled_args F Sc Se Sf mu args ->
      In cl (fun_entry_clauses entry) ->
      clause_matches Sc (fun_entry_signature entry) cl args rho ->
      step F Sc Se Sf mu (EApp f args)
        (subst_env rho (clause_body cl))
  (** Constructors canonicalize their argument order before evaluating
      payloads. *)
  | ST_Ctor_Canon : forall C sigma args args',
      Sc C = Some sigma ->
      canonical_args (extract_cases (signature_params sigma)) args = Some args' ->
      args <> args' ->
      step F Sc Se Sf mu (ECtor C args) (ECtor C args')
  (** Canonical constructor applications step inside their payload list. *)
  | ST_Ctor_Arg : forall C sigma args payloads',
      Sc C = Some sigma ->
      canonical_args (extract_cases (signature_params sigma)) args = Some args ->
      step_exprs F Sc Se Sf mu (List.map fst args) payloads' ->
      step F Sc Se Sf mu (ECtor C args)
        (ECtor C (combine payloads' (extract_cases (signature_params sigma))))
  (** Matches step their scrutinee until it becomes a value. *)
  | ST_Match_Scrut : forall scrut scrut' branches,
      step F Sc Se Sf mu scrut scrut' ->
      step F Sc Se Sf mu (EMatch scrut branches) (EMatch scrut' branches)
  (** Once the scrutinee is a value, the first matching branch can fire. *)
  | ST_Match_Branch : forall v branches p body rho,
      value F Sc Se Sf mu v ->
      In (p, body) branches ->
      pat_match Sc p v rho ->
      step F Sc Se Sf mu (EMatch v branches)
        (subst_env rho body)
  (** A [let] expression steps its bound subexpression first. *)
  | ST_Let_Left : forall x e1 e1' e2,
      step F Sc Se Sf mu e1 e1' ->
      step F Sc Se Sf mu (ELet x e1 e2) (ELet x e1' e2)
  (** A [let] with a value substitutes that value into the body. *)
  | ST_Let_Value : forall x v e2,
      value F Sc Se Sf mu v ->
      step F Sc Se Sf mu (ELet x v e2) (subst x v e2)
  (** Sequences evaluate their left subexpression first. *)
  | ST_Seq_Left : forall e1 e1' e2,
      step F Sc Se Sf mu e1 e1' ->
      step F Sc Se Sf mu (ESeq e1 e2) (ESeq e1' e2)
  (** Once the left side of a sequence is finished, evaluation continues with
      the right side. *)
  | ST_Seq_Value : forall v e2,
      value F Sc Se Sf mu v ->
      step F Sc Se Sf mu (ESeq v e2) e2
  (** Binds evaluate their left subexpression first. *)
  | ST_Bind_Left : forall x e1 e1' e2,
      step F Sc Se Sf mu e1 e1' ->
      step F Sc Se Sf mu (EBind x e1 e2) (EBind x e1' e2)
  (** Once the bound expression is a value, a bind substitutes it into the
      continuation. *)
  | ST_Bind_Value : forall x v e2,
      value F Sc Se Sf mu v ->
      step F Sc Se Sf mu (EBind x v e2) (subst x v e2).

(** Generate a combined induction scheme for the three mutually-
    defined step relations.  This is used by [step_mutual_preservation]. *)
Scheme step_exprs_ind' := Induction for step_exprs Sort Prop
with step_args_ind' := Induction for step_args Sort Prop
with step_ind' := Induction for step Sort Prop.
(** Mutual induction principle for stepping expression lists, labeled
    arguments, and expressions. *)
Combined Scheme step_mutind from step_exprs_ind', step_args_ind', step_ind'.

Arguments value F Sc {Se Sf mu} _.
Arguments value_labeled_args F Sc {Se Sf mu} _.
Arguments value_payloads F Sc {Se Sf mu} _.
Arguments step_exprs F Sc {Se Sf mu} _ _.
Arguments step_args F Sc {Se Sf mu} _ _.
Arguments step F Sc {Se Sf mu} _ _.
