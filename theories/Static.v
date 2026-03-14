(** * Kip Static Semantics *)
(** Declarative static semantics: well-formedness, matching, and typing judgments. *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Ascii.
From Stdlib Require Import Floats.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Lia.
From KipCore Require Import Syntax.
Import ListNotations.
Open Scope string_scope.

(* ================================================================= *)
(** ** Type Well-Formedness *)
(* ================================================================= *)

(** The parameters are an ADT context [Sd] and a type-variable context
    [Delta]. The index is a type [t]; [ty_ok Sd Delta t] means that [t] is
    well formed relative to those declarations. For [TyData], the
    case-labeled type arguments are checked by aligning them with the
    declaration's parameter cases, so distinct labels can be written in any
    order. *)
Inductive ty_ok (Sd : adt_ctx) (Delta : ty_ctx) : ty -> Prop :=
  (** Type variables are well formed exactly when they are in scope. *)
  | OK_TVar : forall a, In a Delta -> ty_ok Sd Delta (TyVar a)
  (** Integers are primitive well-formed types. *)
  | OK_Int : ty_ok Sd Delta TyInt
  (** Floats are primitive well-formed types. *)
  | OK_Float : ty_ok Sd Delta TyFloat
  (** Strings are primitive well-formed types. *)
  | OK_String : ty_ok Sd Delta TyString
  (** Characters are primitive well-formed types. *)
  | OK_Char : ty_ok Sd Delta TyChar
  (** Data types are well formed when their case-labeled arguments align to
      the declaration and each aligned argument is well formed. *)
  | OK_DataTy : forall D decl args args_aligned,
    Sd D = Some decl ->
    align_cases
      (extract_cases (List.map (fun p => (TyVar (fst p), snd p)) (adt_params decl)))
      args
      args_aligned ->
    Forall (ty_ok Sd Delta) args_aligned ->
    ty_ok Sd Delta (TyData D args)
  (** Arrow types are well formed componentwise. *)
  | OK_Arrow : forall t1 t2,
    ty_ok Sd Delta t1 -> ty_ok Sd Delta t2 ->
    ty_ok Sd Delta (TyArr t1 t2)
  .

(* ================================================================= *)
(** ** Signature Well-Formedness *)
(* ================================================================= *)

(** The parameters are the data signature [Sd] and ambient type-variable
    context [Delta]. The index is a signature [sigma]; [signature_ok Sd
    Delta sigma] means that every parameter and the return type of [sigma]
    are well formed. *)
Inductive signature_ok (Sd : adt_ctx) (Delta : ty_ctx) : signature -> Prop :=
  (** A signature is well formed when all of its parameters and its return
      type are well formed under the signature's quantified variables. *)
  | OK_Signature : forall tvars params ret_ty ret_case,
    let Delta' := List.app tvars Delta in
    Forall (fun p => ty_ok Sd Delta' (fst p)) params ->
    ty_ok Sd Delta' ret_ty ->
    signature_ok Sd Delta (mk_signature tvars params ret_ty ret_case)
  .

(* ================================================================= *)
(** ** ADT Declaration Well-Formedness *)
(* ================================================================= *)

(** The parameter [Sd] is the ambient data signature used to check
    referenced types. The index is an ADT declaration [decl]; [adt_ok Sd
    decl] means that the declaration's constructors and return types are
    well formed and mutually consistent. Constructor return types may write
    the ADT's case-labeled type arguments in any order, provided they align
    with the declared cases. *)
Inductive adt_ok (Sd : adt_ctx) : adt_decl -> Prop :=
  (** A data declaration is well formed when constructor names are unique,
      constructor signatures share the declaration's type parameters, return
      the declared head type, and use only admissible return cases. *)
  | OK_Data : forall D_name params ctors,
    let Delta := List.map fst params in
    let decl := mk_adt D_name params ctors in
    NoDup (List.map fst ctors) ->
    Forall (fun cs => signature_tvars (snd cs) = List.map fst params) ctors ->
    NoDup (extract_cases
      (List.map (fun p => (TyVar (fst p), snd p)) params)) ->
    Forall (fun cs => signature_ok Sd Delta (snd cs)) ctors ->
    Forall (fun cs =>
      exists ret_args,
        signature_return_ty (snd cs) = TyData D_name ret_args /\
        align_cases
          (extract_cases (List.map (fun p => (TyVar (fst p), snd p)) params))
          ret_args
          (List.map (fun p => TyVar (fst p)) params)
    ) ctors ->
    Forall (fun cs =>
      signature_return_case (snd cs) = RNom \/ signature_return_case (snd cs) = RP3s
    ) ctors ->
    adt_ok Sd decl
  .

(* ================================================================= *)
(** ** MatchPartial *)
(* ================================================================= *)

(** Search for the first occurrence of case [c] in [cs], returning its index
    relative to the current offset [i].  This is the worker used by
    [match_partial_compute]. *)
Fixpoint find_case_index (cs : list case_label) (c : case_label) (i : nat)
  : option nat :=
  match cs with
  | nil => None
  | c' :: cs' =>
    if case_label_eq_dec c c' then Some i
    else find_case_index cs' c (S i)
  end.

(** Compute the parameter indices filled by an under-saturated application.
    Failure means that some provided case label does not exist or is repeated. *)
Fixpoint match_partial_compute
  (expected : list case_label) (provided : list case_label)
  : option (list nat) :=
  match provided with
  | nil => Some nil
  | c :: cs =>
    match find_case_index expected c 0 with
    | None => None
    | Some idx =>
      match match_partial_compute expected cs with
      | None => None
      | Some rest =>
        if List.existsb (Nat.eqb idx) rest then None
        else Some (idx :: rest)
      end
    end
  end.

(** This is the propositional wrapper around [match_partial_compute]:
    [match_partial expected provided indices] says that the provided cases
    pick out exactly the parameter positions listed in [indices]. *)
Definition match_partial
  (expected provided : list case_label) (indices : list nat) : Prop :=
  match_partial_compute expected provided = Some indices.

(** [align_cases] is deterministic: the underlying computation is
    a function, so equal inputs yield equal outputs.  [congruence]
    handles the [Some]-injection automatically. *)
Theorem align_cases_deterministic :
  forall (A : Type) expected provided aligned1 aligned2,
    @align_cases A expected provided aligned1 ->
    @align_cases A expected provided aligned2 ->
    aligned1 = aligned2.
Proof. unfold align_cases; intros; congruence. Qed.

(* ================================================================= *)
(** ** Compatibility and Join *)
(* ================================================================= *)

(** [compat t1 t2] is the proposition that the type [t1] can be used where
    [t2] is expected. In this formalization that intuition is implemented by
    plain equality. *)
Definition compat (t1 t2 : ty) : Prop := t1 = t2.

(** There are no separate parameters. The indices are a list of types [ts]
    and a type [t]; [join ts t] says that [ts] is nonempty and every element
    of [ts] agrees with the common type [t]. *)
Inductive join : list ty -> ty -> Prop :=
  (** A singleton list joins to its unique element. *)
  | Join_single : forall t, join [t] t
  (** Prepending another copy of the join type preserves the join. *)
  | Join_cons : forall t ts, join ts t -> join (t :: ts) t
  .

(* ================================================================= *)
(** ** EffectExpr *)
(* ================================================================= *)

(** The parameter [Se] records which function names are effectful. The index
    is an expression [e]; [effect_expr Se e] says that [e] is syntactically
    effectful under that context. *)
Inductive effect_expr (Se : effect_ctx) : expr -> Prop :=
  (** Sequences are always syntactically effectful. *)
  | EE_Seq  : forall e1 e2, effect_expr Se (ESeq e1 e2)
  (** Binds are always syntactically effectful. *)
  | EE_Bind : forall x e1 e2, effect_expr Se (EBind x e1 e2)
  (** A function call is effectful exactly when the effect context marks the
      callee as effectful. *)
  | EE_EffApp : forall f args,
      Se f = true ->
      effect_expr Se (EApp f args)
  .

(* ================================================================= *)
(** ** Remaining Parameters for Partial Application *)
(* ================================================================= *)

(** Enumerate the parameter positions in the range [[n, n + total))] that do
    not already appear in [filled].  The result drives the return type of a
    partial application. *)
Fixpoint remaining_indices (n : nat) (total : nat) (filled : list nat) : list nat :=
  match total with
  | 0 => nil
  | S total' =>
    if List.existsb (Nat.eqb n) filled
    then remaining_indices (S n) total' filled
    else n :: remaining_indices (S n) total' filled
  end.

(** Project the parameter types at the requested indices.  Partial
    application uses this to rebuild the arrow type of the remaining
    arguments. *)
Fixpoint collect_at_indices (indices : list nat) (params : list signature_param) : list ty :=
  match indices with
  | nil => nil
  | i :: is' =>
    match nth_error params i with
    | Some (t, _) => t :: collect_at_indices is' params
    | None => collect_at_indices is' params
    end
  end.

(* ================================================================= *)
(** ** Pattern Binding *)
(* ================================================================= *)

(** The parameter [Sc] provides the constructor context. The indices are a
    pattern [p], a scrutinee type [tau], and an output context [Gamma];
    [pat_bind Sc p tau Gamma] says that matching [p] against a value of type
    [tau] binds exactly the variables in [Gamma]. Constructor sub-patterns
    are aligned against constructor parameters by case label, so distinct
    labels can be written in any order. *)
Inductive pat_bind (Sc : ctor_ctx) : pat -> ty -> val_ctx -> Prop :=
  (** Wildcards never bind variables. *)
  | PB_Wild : forall tau,
    pat_bind Sc PWild tau nil
  (** Variable patterns bind the scrutinee under their variable name. *)
  | PB_Var : forall x tau,
    pat_bind Sc (PVarPat x) tau [(x, tau)]
  (** Literal patterns bind nothing and require the scrutinee type to be the
      corresponding literal type. *)
  | PB_Lit : forall c tau,
    tau = literal_ty c ->
    pat_bind Sc (PLit c) tau nil
  (** Constructor patterns align their subpatterns to the constructor
      signature, bind each subpattern against the corresponding payload type,
      and concatenate the resulting contexts. *)
  | PB_Ctor : forall C sigma (theta : list (tyvar_name * ty))
      (pats : list (pat * case_label)) (pats_aligned : list pat)
      tau Gammas,
    Sc C = Some sigma ->
    length theta = length (signature_tvars sigma) ->
    let bound := combine (signature_tvars sigma) (List.map (@snd tyvar_name ty) theta) in
    apply_subst bound (signature_return_ty sigma) = tau ->
    align_cases (extract_cases (signature_params sigma)) pats pats_aligned ->
    length Gammas = length pats_aligned ->
    Forall2 (fun (pg : pat * val_ctx) (tp : signature_param) =>
      pat_bind Sc (fst pg) (apply_subst bound (fst tp)) (snd pg)
    ) (combine pats_aligned Gammas) (signature_params sigma) ->
    pat_bind Sc (PCtorPat C pats) tau (List.concat Gammas)
  .

(* ================================================================= *)
(** ** Pattern Matching and Semantic Values *)
(* ================================================================= *)

(** [pat_match Sc p v rho] is the pattern-matching relation used by the
    dynamic semantics.
    Successful matches return the substitution environment [rho] generated by
    the pattern.  Constructor patterns align their sub-patterns to the
    constructor signature by case label, matching the static [pat_bind]
    judgment. *)
Inductive pat_match (Sc : ctor_ctx) : pat -> expr -> list (var_name * expr) -> Prop :=
  (** Wildcards always match and produce no bindings. *)
  | PM_Wild : forall v,
      pat_match Sc PWild v []
  (** Variable patterns always match and bind the whole value. *)
  | PM_Var : forall x v,
      pat_match Sc (PVarPat x) v [(x, v)]
  (** Literal patterns only match the same literal. *)
  | PM_Lit : forall c,
      pat_match Sc (PLit c) (ELit c) []
  (** Constructor patterns match canonical constructor values, align their
      subpatterns to the constructor signature, and recursively match the
      payload list. *)
  | PM_Ctor : forall C sigma pats pats_aligned args rho,
      Sc C = Some sigma ->
      canonical_args (extract_cases (signature_params sigma)) args = Some args ->
      align_cases (extract_cases (signature_params sigma)) pats pats_aligned ->
      pats_match Sc pats_aligned (List.map fst args) rho ->
      pat_match Sc (PCtorPat C pats) (ECtor C args) rho

(** The list-level analogue of [pat_match], used for matching the aligned
    pattern list of a function clause against the canonical payload list of a
    full application. *)
with pats_match (Sc : ctor_ctx)
  : list pat -> list expr -> list (var_name * expr) -> Prop :=
  (** Empty pattern lists match empty value lists with no bindings. *)
  | PMs_nil :
      pats_match Sc [] [] []
  (** Nonempty lists match pointwise, concatenating the bindings produced by
      the head match and the tail match. *)
  | PMs_cons : forall p v ps vs rho_p rho_ps,
      pat_match Sc p v rho_p ->
      pats_match Sc ps vs rho_ps ->
      pats_match Sc (p :: ps) (v :: vs) (rho_p ++ rho_ps).

(** [semantic_value Se Sf Sc mu tau v] is the closed-value semantics used by
    exhaustiveness.  Unlike [has_type], it talks only about canonical values,
    not arbitrary expressions. *)
Inductive semantic_value
  (Se : effect_ctx) (Sf : fun_ctx) (Sc : ctor_ctx) (mu : eff_mode)
  : ty -> expr -> Prop :=
  (** Literals inhabit the semantic-value relation at their primitive type. *)
  | SV_Lit : forall c,
      semantic_value Se Sf Sc mu (literal_ty c) (ELit c)
  (** Canonical constructor values are semantic values when each aligned
      payload is a semantic value at the corresponding instantiated parameter
      type. *)
  | SV_Ctor : forall C sigma (theta : list (tyvar_name * ty))
      args args_aligned,
      Sc C = Some sigma ->
      length theta = length (signature_tvars sigma) ->
      let bound := combine (signature_tvars sigma) (List.map snd theta) in
      align_cases (extract_cases (signature_params sigma)) args args_aligned ->
      Forall2 (fun arg param =>
        semantic_value Se Sf Sc mu (apply_subst bound (fst param)) arg
      ) args_aligned (signature_params sigma) ->
      semantic_value Se Sf Sc mu
        (apply_subst bound (signature_return_ty sigma))
        (ECtor C (combine args_aligned (extract_cases (signature_params sigma))))
  (** Under-saturated applications are semantic values at the residual arrow
      type determined by the unfilled parameter positions. *)
  | SV_PartialApp : forall f sigma (theta : list (tyvar_name * ty))
      args indices,
      In sigma (Sf f) ->
      (Se f = true -> mu = Eff) ->
      length theta = length (signature_tvars sigma) ->
      let bound := combine (signature_tvars sigma) (List.map snd theta) in
      length args < length (signature_params sigma) ->
      match_partial
        (extract_cases (signature_params sigma))
        (extract_cases args)
        indices ->
      Forall2 (fun arg idx =>
        exists param,
          nth_error (signature_params sigma) idx = Some param /\
          semantic_value Se Sf Sc mu (apply_subst bound (fst param)) (fst arg)
      ) args indices ->
      semantic_value Se Sf Sc mu
        (let rem_idxs := remaining_indices 0 (length (signature_params sigma)) indices in
         let rem_tys := List.map (fun t => apply_subst bound t)
                          (collect_at_indices rem_idxs (signature_params sigma)) in
         List.fold_right TyArr (apply_subst bound (signature_return_ty sigma)) rem_tys)
        (EApp f args).

(** A function clause matches a canonical argument list when its labeled
    patterns align to the signature and then match the payload list
    pointwise. *)
Definition clause_matches
  (Sc : ctor_ctx) (sigma : signature) (cl : fun_clause)
  (args : list (expr * case_label)) (rho : list (var_name * expr)) : Prop :=
  exists pats_aligned,
    align_cases (extract_cases (signature_params sigma)) (clause_pats cl) pats_aligned /\
    pats_match Sc pats_aligned (List.map fst args) rho.

(** Semantic exhaustiveness for [match]: every canonical closed value of the
    scrutinee type matches some branch. *)
Definition branches_exhaustive
  (Se : effect_ctx) (Sf : fun_ctx) (Sc : ctor_ctx)
  (mu : eff_mode) (tau : ty) (branches : list (pat * expr)) : Prop :=
  forall v,
    semantic_value Se Sf Sc mu tau v ->
    exists p body rho,
      In (p, body) branches /\
      pat_match Sc p v rho.

(** Semantic exhaustiveness for function clauses: every canonical value tuple
    inhabiting the instantiated signature parameters matches some clause.
    The extra substitution [bound] lets the same notion serve both the
    monomorphic dynamic environment and the polymorphic function-definition
    checker. *)
Definition clauses_exhaustive_under
  (Se : effect_ctx) (Sf : fun_ctx) (Sc : ctor_ctx)
  (mu : eff_mode) (bound : ty_subst) (sigma : signature) (clauses : fun_def) : Prop :=
  forall args,
    canonical_args (extract_cases (signature_params sigma)) args = Some args ->
    Forall2 (fun arg param =>
      semantic_value Se Sf Sc mu (apply_subst bound (fst param)) (fst arg)
    ) args (signature_params sigma) ->
    exists cl rho,
      In cl clauses /\
      clause_matches Sc sigma cl args rho.

(** The monomorphic dynamic semantics uses the special case with no
    additional type substitution. *)
Definition clauses_exhaustive
  (Se : effect_ctx) (Sf : fun_ctx) (Sc : ctor_ctx)
  (mu : eff_mode) (sigma : signature) (clauses : fun_def) : Prop :=
  clauses_exhaustive_under Se Sf Sc mu [] sigma clauses.

(** Elimination principle for single-pattern pattern matching. *)
Scheme pat_match_ind' := Induction for pat_match Sort Prop
with pats_match_ind' := Induction for pats_match Sort Prop.
(** Mutual elimination principle for pattern matching on a single pattern and
    on aligned pattern lists.  The static-semantics lemmas for matching use
    this instead of rebuilding mutual induction manually. *)
Combined Scheme pat_match_mutind from pat_match_ind', pats_match_ind'.

(* ================================================================= *)
(** ** Core Typing Judgment *)
(* ================================================================= *)

(** The parameters [Se], [Sf], and [Sc] provide the effect, function, and
    constructor contexts. The indices are a typing context [Gamma], an
    effect mode [mu], an expression [e], and a result type [upsilon = (tau,
    kres)]; [has_type Se Sf Sc Gamma mu e upsilon] is the core typing
    judgment. *)
Inductive has_type (Se : effect_ctx) (Sf : fun_ctx) (Sc : ctor_ctx)
  : val_ctx -> eff_mode -> expr -> result_ty -> Prop :=

  (** Variables are typed by looking them up in the ambient value context.
      Variables never carry a result-case annotation of their own. *)
  | T_Var : forall Gamma mu x tau,
    ctx_lookup Gamma x = Some tau ->
    has_type Se Sf Sc Gamma mu (EVar x) (tau, None)

  (** Literals synthesize their primitive type immediately and likewise have
      no result-case annotation. *)
  | T_Lit : forall Gamma mu c,
    has_type Se Sf Sc Gamma mu (ELit c) (literal_ty c, None)

  (** Ascription checks compatibility with the user-written annotation while
      preserving the underlying result case. *)
  | T_Ascribe : forall Gamma mu e tau kres tau_ann,
    has_type Se Sf Sc Gamma mu e (tau, kres) ->
    compat tau tau_ann ->
    has_type Se Sf Sc Gamma mu (EAscribe e tau_ann) (tau_ann, kres)

  (** T-App: fully-saturated case-labeled function application.
      If [f] is effectful (an infinitive), the mode must be [Eff].
      Arguments are matched to parameters via [align_cases], which
      picks provided arguments by case label.  When case labels are
      distinct the call-site order is irrelevant; when labels repeat
      the written order determines matching. *)
  | T_App : forall Gamma mu f sigma (theta : list (tyvar_name * ty))
      (args : list (expr * case_label)) (args_aligned : list expr),
    In sigma (Sf f) ->
    (Se f = true -> mu = Eff) ->
    length theta = length (signature_tvars sigma) ->
    let bound := combine (signature_tvars sigma) (List.map (@snd tyvar_name ty) theta) in
    align_cases (extract_cases (signature_params sigma)) args args_aligned ->
    Forall2 (fun arg param =>
      exists kres_i,
        has_type Se Sf Sc Gamma mu arg
          (apply_subst bound (fst param), kres_i)
    ) args_aligned (signature_params sigma) ->
    has_type Se Sf Sc Gamma mu
      (EApp f args)
      (apply_subst bound (signature_return_ty sigma), Some (signature_return_case sigma))

  (** Partial applications are typed by recording which parameters were
      supplied and returning an arrow over the remaining parameter types.
      The same effectfulness side condition as in [T_App] applies. *)
  | T_App_Partial : forall Gamma mu f sigma (theta : list (tyvar_name * ty))
      (args : list (expr * case_label)) indices,
    In sigma (Sf f) ->
    (Se f = true -> mu = Eff) ->
    length theta = length (signature_tvars sigma) ->
    let bound := combine (signature_tvars sigma) (List.map (@snd tyvar_name ty) theta) in
    length args < length (signature_params sigma) ->
    match_partial
      (extract_cases (signature_params sigma))
      (extract_cases args)
      indices ->
    Forall2 (fun arg idx =>
      exists param kres_i,
        nth_error (signature_params sigma) idx = Some param /\
        has_type Se Sf Sc Gamma mu (fst arg)
          (apply_subst bound (fst param), kres_i)
    ) args indices ->
    let rem_idxs := remaining_indices 0 (length (signature_params sigma)) indices in
    let rem_tys := List.map (fun t => apply_subst bound t)
                     (collect_at_indices rem_idxs (signature_params sigma)) in
    has_type Se Sf Sc Gamma mu
      (EApp f args)
      (List.fold_right TyArr (apply_subst bound (signature_return_ty sigma)) rem_tys,
       None)

  (** Constructor applications use the same case-alignment machinery as
      function calls, but their result case is fixed by the constructor
      signature rather than overload resolution. *)
  | T_Ctor : forall Gamma mu C sigma (theta : list (tyvar_name * ty))
      (args : list (expr * case_label)) (args_aligned : list expr),
    Sc C = Some sigma ->
    length theta = length (signature_tvars sigma) ->
    let bound := combine (signature_tvars sigma) (List.map (@snd tyvar_name ty) theta) in
    align_cases (extract_cases (signature_params sigma)) args args_aligned ->
    Forall2 (fun arg param =>
      exists kres_i,
        has_type Se Sf Sc Gamma mu arg
          (apply_subst bound (fst param), kres_i)
    ) args_aligned (signature_params sigma) ->
    has_type Se Sf Sc Gamma mu
      (ECtor C args)
      (apply_subst bound (signature_return_ty sigma), Some (signature_return_case sigma))

  (** A match expression is well typed when the scrutinee is typed, the
      branches are semantically exhaustive for the scrutinee type, and each
      branch body is typed at a common result type under the bindings induced
      by its pattern. *)
  | T_Match : forall Gamma mu es tau_s kres_s branches tau,
    has_type Se Sf Sc Gamma mu es (tau_s, kres_s) ->
    branches_exhaustive Se Sf Sc mu tau_s branches ->
    Forall (fun pb =>
      exists Gamma_p tau_j kres_j,
        pat_bind Sc (fst pb) tau_s Gamma_p /\
        has_type Se Sf Sc (ctx_concat Gamma_p Gamma) mu (snd pb) (tau_j, kres_j) /\
        tau_j = tau
    ) branches ->
    has_type Se Sf Sc Gamma mu
      (EMatch es branches)
      (tau, None)

  (** T-Let: pure local binding via substitution.  The bound expression
      is checked first, then the body is checked in the extended
      context. *)
  | T_Let : forall Gamma mu x e1 e2 tau1 kres1 tau2 kres2,
    has_type Se Sf Sc Gamma mu e1 (tau1, kres1) ->
    has_type Se Sf Sc (ctx_extend Gamma x tau1) mu e2 (tau2, kres2) ->
    has_type Se Sf Sc Gamma mu (ELet x e1 e2) (tau2, kres2)

  (** Sequencing is only available in [Eff] mode: it evaluates [e1] for its
      effects and then continues with [e2]. *)
  | T_Seq : forall Gamma e1 e2 tau1 kres1 tau2 kres2,
    has_type Se Sf Sc Gamma Eff e1 (tau1, kres1) ->
    has_type Se Sf Sc Gamma Eff e2 (tau2, kres2) ->
    has_type Se Sf Sc Gamma Eff (ESeq e1 e2) (tau2, kres2)

  (** Bind sequencing is also restricted to [Eff] mode and extends the
      continuation context with the value produced by the left-hand side. *)
  | T_Bind : forall Gamma x e1 e2 tau1 kres1 tau2 kres2,
    has_type Se Sf Sc Gamma Eff e1 (tau1, kres1) ->
    has_type Se Sf Sc (ctx_extend Gamma x tau1) Eff e2 (tau2, kres2) ->
    has_type Se Sf Sc Gamma Eff (EBind x e1 e2) (tau2, kres2)
  .

(* ================================================================= *)
(** ** Static Rejection *)
(* ================================================================= *)

(** An expression is effect-rejected when it is syntactically effectful and
    therefore admits no typing derivation in [Pure] mode. *)
Definition effect_rejected (Se : effect_ctx) (Sf : fun_ctx) (Sc : ctor_ctx)
  (Gamma : val_ctx) (e : expr) : Prop :=
  effect_expr Se e /\ forall upsilon, ~ has_type Se Sf Sc Gamma Pure e upsilon.

(** An application is ambiguous when there are two distinct candidate
    interfaces for the same function name and the call is typable under at
    least one of them. *)
Definition app_ambiguous (Se : effect_ctx) (Sf : fun_ctx) (Sc : ctor_ctx)
  (Gamma : val_ctx) (mu : eff_mode) (f : fun_name)
  (args : list (expr * case_label)) : Prop :=
  exists sigma1 sigma2,
    In sigma1 (Sf f) /\ In sigma2 (Sf f) /\ sigma1 <> sigma2 /\
    (exists upsilon1, has_type Se Sf Sc Gamma mu (EApp f args) upsilon1).

(** An application has no match when no result type yields a typing
    derivation for that call site. *)
Definition app_no_match (Se : effect_ctx) (Sf : fun_ctx) (Sc : ctor_ctx)
  (Gamma : val_ctx) (mu : eff_mode) (f : fun_name)
  (args : list (expr * case_label)) : Prop :=
  forall upsilon, ~ has_type Se Sf Sc Gamma mu (EApp f args) upsilon.

(* ================================================================= *)
(** ** Function Definition Well-Formedness *)
(* ================================================================= *)

(** The parameters [Se], [Sf], [Sc], and [mu] are the global contexts and
    the effect mode in which the definition family is checked. The index
    [phi] is a function-definition family; [fun_def_ok Se Sf Sc mu phi]
    means that every clause in [phi] is well typed against a common
    signature and that the clause list is semantically exhaustive for that
    signature. Clause patterns are aligned to the signature by case label,
    so distinct labeled arguments can be written in any order. *)
Inductive fun_def_ok (Se : effect_ctx) (Sf : fun_ctx) (Sc : ctor_ctx) (mu : eff_mode)
  : fun_def -> Prop :=

  (** A clause family is well formed when it shares a common signature, each
      clause body is typed under the bindings induced by its aligned
      patterns, and the family is semantically exhaustive for that
      signature. *)
  | T_FunDef : forall f sigma (theta : list (tyvar_name * ty)) clauses,
    In sigma (Sf f) ->
    length theta = length (signature_tvars sigma) ->
    let bound := combine (signature_tvars sigma) (List.map (@snd tyvar_name ty) theta) in
    Forall (fun cl => clause_name cl = f) clauses ->
    Forall (fun cl =>
      exists pats_aligned Gamma_cl kres_cl,
        align_cases (extract_cases (signature_params sigma))
          (clause_pats cl) pats_aligned /\
        (forall i pi_param,
          nth_error (combine pats_aligned (signature_params sigma)) i =
            Some pi_param ->
          exists Gamma_i,
            pat_bind Sc (fst pi_param)
              (apply_subst bound (fst (snd pi_param))) Gamma_i) /\
        has_type Se Sf Sc Gamma_cl mu (clause_body cl)
          (apply_subst bound (signature_return_ty sigma), kres_cl)
    ) clauses ->
    clauses_exhaustive_under Se Sf Sc mu bound sigma clauses ->
    fun_def_ok Se Sf Sc mu clauses
  .

(* ================================================================= *)
(** ** Program Well-Formedness *)
(* ================================================================= *)

(** The parameters [Sd], [Se], [Sf], and [Sc] are the global contexts. The
    index is a whole program [prog]; [program_ok Sd Se Sf Sc prog] says that
    its ADTs, function definitions, and top-level expression are all well
    formed. *)
Inductive program_ok (Sd : adt_ctx) (Se : effect_ctx) (Sf : fun_ctx) (Sc : ctor_ctx)
  : program -> Prop :=

  (** A whole program is well formed when every ADT declaration is valid,
      every function family is valid in some mode, and the top-level
      expression is a pure well-typed term. *)
  | T_Program : forall adts funs e tau kres,
    Forall (adt_ok Sd) adts ->
    Forall (fun phi => exists mu, fun_def_ok Se Sf Sc mu phi) funs ->
    has_type Se Sf Sc nil Pure e (tau, kres) ->
    program_ok Sd Se Sf Sc (mk_program adts funs e)
  .
