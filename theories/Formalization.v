(** * Kip Core Static Formalization *)
(** This file formalizes the typed static core of Kip with explicit
    case-labeled interfaces.  It models:

    - The type system (typing judgments, well-formedness of types,
      interfaces, and ADT declarations);
    - The operational semantics (small-step reduction with
      case-label alignment);
    - Key metatheoretic properties (effect safety, substitution,
      progress, and preservation / type soundness).

    It does _not_ model parsing or elaboration.

    ** Proof engineering notes **

    Proofs are written defensively against Rocq's automatic naming:
    hypotheses are either named explicitly in [intros], matched by
    type with [match goal with], or consumed immediately by [eauto].
    This makes the proofs robust against reorderings of constructor
    arguments and additions of new typing rules.

    Custom [Ltac] tactics are collected in the "Proof Automation"
    section so that every downstream proof can use them. *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Ascii.
From Stdlib Require Import Floats.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Lia.
Import ListNotations.
Open Scope string_scope.

(* ================================================================= *)
(** ** Case Labels *)
(* ================================================================= *)

(** Grammatical case labels used by the surface syntax of Kip.
    These correspond to Turkish grammatical cases. *)
Inductive case_label : Type :=
  (** [Nom] is the nominative case, used for default argument and return
      positions. *)
  | Nom
  (** [Acc] is the accusative case. *)
  | Acc
  (** [Dat] is the dative case. *)
  | Dat
  (** [Loc] is the locative case. *)
  | Loc
  (** [Abl] is the ablative case. *)
  | Abl
  (** [Gen] is the genitive case. *)
  | Gen
  (** [Ins] is the instrumental/comitative case. *)
  | Ins
  (** [Cond] is the conditional case label. *)
  | Cond
  (** [P3s] is the third-person possessive case label. *)
  | P3s
  .

(** Decidable equality for case labels.  Rocq's [decide equality]
    discharges the proof automatically because [case_label] is a
    simple enumeration type.  The rest of the file uses this directly
    instead of maintaining a parallel boolean equality API. *)
Lemma case_label_eq_dec : forall (c1 c2 : case_label), {c1 = c2} + {c1 <> c2}.
Proof. decide equality. Defined.

(** Return-case labels: only nominative and possessive are
    valid for function/constructor return positions. *)
Inductive return_case : Type :=
  (** [RNom] is the ordinary nominative return case. *)
  | RNom
  (** [RP3s] is the possessive return case. *)
  | RP3s
  .

(** Embed return cases into the full case-label vocabulary.  This keeps result
    annotations compatible with the rest of the case-label machinery. *)
Definition return_case_to_case (rc : return_case) : case_label :=
  match rc with RNom => Nom | RP3s => P3s end.

(** Expressions either carry no result case or a concrete return case.
    This is just an optional [return_case]; using [option] keeps the
    formalization closer to the intended data model. *)
Definition result_case : Type := option return_case.

(* ================================================================= *)
(** ** Effect Modes *)
(* ================================================================= *)

(** Kip distinguishes pure and effectful computations.
    In Kip, pure definitions are noun phrases and effectful definitions
    are imperative verbs (infinitives). These are fundamentally different
    syntactic categories: a pure function call looks like a noun phrase,
    while an effectful function call looks like a verb. *)
Inductive eff_mode : Type :=
  (** [Pure] forbids effectful applications. *)
  | Pure
  (** [Eff] allows effectful applications and sequencing forms. *)
  | Eff
  .

(** Like [case_label_eq_dec], this just records that [eff_mode] is a finite
    datatype with decidable equality. *)
Lemma eff_mode_eq_dec : forall (m1 m2 : eff_mode), {m1 = m2} + {m1 <> m2}.
Proof. decide equality. Defined.

(* ================================================================= *)
(** ** Names *)
(* ================================================================= *)

(** All name sorts are represented as [string].  Separate type aliases
    improve readability of signatures without introducing the overhead
    of distinct wrapper types.  At this level of formalization the
    lack of strong name-sorting is harmless. *)
(** Variables are represented by strings. *)
Definition var_name := string.
(** Functions are represented by strings. *)
Definition fun_name := string.
(** Constructors are represented by strings. *)
Definition ctor_name := string.
(** Type variables are represented by strings. *)
Definition tyvar_name := string.
(** Data-type names are represented by strings. *)
Definition data_name := string.

(* ================================================================= *)
(** ** Literals *)
(* ================================================================= *)

(** The formalization supports integer, floating-point, string, and
    character literals.  Integers are modeled as [nat] for simplicity;
    the actual language uses arbitrary-precision integers, while
    floating-point literals use Rocq's standard [float] type. *)
Inductive literal : Type :=
  (** Integer literals. *)
  | CInt     (n : nat)
  (** Floating-point literals. *)
  | CFloat   (f : float)
  (** String literals. *)
  | CString  (s : string)
  (** Character literals. *)
  | CChar    (c : ascii)
  .

(** Rocq floats expose a boolean Leibniz equality.  Turning it into a
    [sumbool] lets the rest of the development stay constructive. *)
Lemma float_eq_dec : forall (f1 f2 : float), {f1 = f2} + {f1 <> f2}.
Proof.
  intros f1 f2; destruct (Leibniz.eqb f1 f2) eqn:Heq; [left | right].
  - now apply Leibniz.eqb_spec.
  - intro Heq'; subst f2.
    rewrite (proj2 (Leibniz.eqb_spec f1 f1) eq_refl) in Heq; discriminate.
Defined.

(** Decidable equality for literals follows from the primitive deciders for
    their payloads. *)
Lemma literal_eq_dec : forall (c1 c2 : literal), {c1 = c2} + {c1 <> c2}.
Proof.
  decide equality;
    try solve [apply Nat.eq_dec | apply float_eq_dec | apply string_dec | apply ascii_dec].
Defined.

(* ================================================================= *)
(** ** Types *)
(* ================================================================= *)

(** The type language includes:
    - [TyVar]: type variables (universally quantified in interfaces);
    - Primitive types: [TyInt], [TyFloat], [TyString], [TyChar];
    - [TyData]: algebraic data types, parameterized by case-labeled
      type arguments (reflecting Kip's case-labeled syntax and matched
      by case label rather than raw position);
    - [TyArr]: function (arrow) types, used for partial applications
      and higher-order values.

    Note that [TyData] carries its arguments as [(ty * case_label)]
    pairs, mirroring how Kip's surface syntax labels each type
    argument with a grammatical case. *)
Inductive ty : Type :=
  (** A type variable. *)
  | TyVar    (a : tyvar_name)
  (** Integer type. *)
  | TyInt
  (** Floating-point type. *)
  | TyFloat
  (** String type. *)
  | TyString
  (** Character type. *)
  | TyChar
  (** Algebraic data type application with case-labeled arguments. *)
  | TyData   (D : data_name) (args : list (ty * case_label))
  (** Function type. *)
  | TyArr    (dom : ty) (cod : ty)
  .

(** A generic constructive equality decider for pairs. *)
Lemma pair_eq_dec :
  forall (A B : Type)
    (eqA : forall x y : A, {x = y} + {x <> y})
    (eqB : forall x y : B, {x = y} + {x <> y})
    (p1 p2 : A * B),
    {p1 = p2} + {p1 <> p2}.
Proof.
  intros A B eqA eqB [a1 b1] [a2 b2]; decide equality.
Defined.

(** Type equality is decidable.  The only nontrivial recursive case is the
    case-labeled argument list of [TyData]. *)
Lemma ty_eq_dec : forall (t1 t2 : ty), {t1 = t2} + {t1 <> t2}.
Proof.
  fix IH 1.
  intros t1 t2; decide equality; try solve [apply string_dec].
  apply (list_eq_dec (pair_eq_dec ty case_label IH case_label_eq_dec)).
Defined.

(** Compute the primitive type of a literal.  The literal typing rules and
    literal-pattern rules both factor through this definition. *)
Definition literal_ty (c : literal) : ty :=
  match c with
  | CInt _    => TyInt
  | CFloat _  => TyFloat
  | CString _ => TyString
  | CChar _   => TyChar
  end.

(** A typing judgment returns both the ordinary type and the optional
    return-case annotation produced by the expression. *)
Definition result_ty := (ty * result_case)%type.

(* ================================================================= *)
(** ** Interfaces *)
(* ================================================================= *)

(** [signature_param] pairs a parameter type with the case label that
    must appear at call sites. *)
Definition signature_param := (ty * case_label)%type.

(** Signatures are the shared contract format for constructors and
    functions.  They package quantified type variables, case-labeled
    parameters, and the return information used by typing, overload
    resolution, and runtime matching. *)
Record signature := mk_signature {
  (** Universally quantified type variables. *)
  signature_tvars        : list tyvar_name;
  (** Parameter list expected at call sites. *)
  signature_params       : list signature_param;
  (** Ordinary return type. *)
  signature_return_ty    : ty;
  (** Morphological case of the result. *)
  signature_return_case  : return_case;
}.

(* ================================================================= *)
(** ** Patterns *)
(* ================================================================= *)

(** Patterns include wildcards, variable bindings, literal matching
    (including floating-point literals via [PLit (CFloat ...)]), and
    constructor patterns with case-labeled sub-patterns that are
    matched by case label rather than by position. *)
Inductive pat : Type :=
  (** Wildcard patterns inspect a value but bind nothing. *)
  | PWild
  (** Variable patterns bind the whole matched value. *)
  | PVarPat  (x : var_name)
  (** Literal patterns match an exact literal. *)
  | PLit   (c : literal)
  (** Constructor patterns recursively match case-labeled subpatterns. *)
  | PCtorPat (C : ctor_name) (args : list (pat * case_label))
  .

(** Pattern equality is decidable because every payload type already has a
    decidable equality test. *)
Lemma pat_eq_dec : forall (p1 p2 : pat), {p1 = p2} + {p1 <> p2}.
Proof.
  fix IH 1.
  intros p1 p2; decide equality;
    try solve [apply literal_eq_dec | apply string_dec].
  apply (list_eq_dec (pair_eq_dec pat case_label IH case_label_eq_dec)).
Defined.

(* ================================================================= *)
(** ** Expressions *)
(* ================================================================= *)

(** The expression language includes:
    - Variables and literals;
    - Type ascriptions;
    - Function application and constructor application, both with
      case-labeled argument lists;
    - Pattern matching;
    - Pure let-binding ([ELet]);
    - Effectful sequencing ([ESeq]) and monadic bind ([EBind]).

    Note that [EApp] and [ECtor] carry their arguments as
    [(expr * case_label)] pairs.  This is the core of Kip's
    case-labeled calling convention: arguments are matched to
    parameters by case label, not by position. *)
Inductive expr : Type :=
  (** Variables. *)
  | EVar     (x : var_name)
  (** Literal expressions. *)
  | ELit  (c : literal)
  (** Type ascriptions. *)
  | EAscribe (e : expr) (t : ty)
  (** Function application with case-labeled arguments. *)
  | EApp     (f : fun_name) (args : list (expr * case_label))
  (** Constructor application with case-labeled arguments. *)
  | ECtor    (C : ctor_name) (args : list (expr * case_label))
  (** Pattern matching. *)
  | EMatch   (scrut : expr) (branches : list (pat * expr))
  (** Pure let-binding. *)
  | ELet     (x : var_name) (e1 : expr) (e2 : expr)
  (** Effectful sequencing. *)
  | ESeq     (e1 : expr) (e2 : expr)
  (** Effectful bind sequencing. *)
  | EBind    (x : var_name) (e1 : expr) (e2 : expr)
  .

(** A simple structural size measure on expressions.  Applications and
    constructors count the sizes of all payload expressions; matches count
    the scrutinee and all branch bodies.  We use this measure to recurse
    through value payloads in [value_has_semantic_value]. *)
Fixpoint expr_size (e : expr) : nat :=
  match e with
  | EVar _ => 1
  | ELit _ => 1
  | EAscribe e _ => S (expr_size e)
  | EApp _ args =>
      S (fold_right plus 0 (List.map (fun p => expr_size (fst p)) args))
  | ECtor _ args =>
      S (fold_right plus 0 (List.map (fun p => expr_size (fst p)) args))
  | EMatch scrut branches =>
      S (expr_size scrut +
         fold_right plus 0 (List.map (fun branch => expr_size (snd branch)) branches))
  | ELet _ e1 e2 => S (expr_size e1 + expr_size e2)
  | ESeq e1 e2 => S (expr_size e1 + expr_size e2)
  | EBind _ e1 e2 => S (expr_size e1 + expr_size e2)
  end.

(** Any element's contribution is bounded by the sum over the whole list. *)
Lemma in_sum_map_le :
  forall (A : Type) (f : A -> nat) xs x,
    In x xs ->
    f x <= fold_right plus 0 (List.map f xs).
Proof.
  intros A f xs.
  induction xs as [|y ys IH]; intros x Hin; simpl in *.
  - contradiction.
  - destruct Hin as [->|Hin].
    + lia.
    + pose proof (IH _ Hin). lia.
Qed.

(** Expression equality is also decidable.  The progress proof uses this to
    split constructively on whether a call is already in canonical argument
    order. *)
Lemma expr_eq_dec : forall (e1 e2 : expr), {e1 = e2} + {e1 <> e2}.
Proof.
  fix IH 1.
  intros e1 e2; decide equality;
    try solve [apply pat_eq_dec | apply literal_eq_dec | apply ty_eq_dec | apply string_dec].
  - apply (list_eq_dec (pair_eq_dec expr case_label IH case_label_eq_dec)).
  - apply (list_eq_dec (pair_eq_dec expr case_label IH case_label_eq_dec)).
  - apply (list_eq_dec (pair_eq_dec pat expr pat_eq_dec IH)).
Defined.

(** Equality for labeled expressions is the pairwise combination of
    [expr_eq_dec] and [case_label_eq_dec]. *)
Lemma labeled_expr_eq_dec :
  forall (p1 p2 : expr * case_label), {p1 = p2} + {p1 <> p2}.
Proof.
  apply (pair_eq_dec expr case_label expr_eq_dec case_label_eq_dec).
Defined.

(* ================================================================= *)
(** ** Function Clauses and Definitions *)
(* ================================================================= *)

(** [fun_clause] is the runtime/static representation of one function clause:
    a function name, its case-labeled patterns, and the body executed when the
    clause matches. *)
Record fun_clause := mk_clause {
  (** The function name this clause belongs to. *)
  clause_name : fun_name;
  (** The clause's case-labeled patterns. *)
  clause_pats : list (pat * case_label);
  (** The clause body. *)
  clause_body : expr;
}.

(** A function definition is represented as a list of clauses sharing a
    common name and signature. *)
Definition fun_def := list fun_clause.

(* ================================================================= *)
(** ** ADT Declarations *)
(* ================================================================= *)

(** An ADT declaration names the data type, lists its type parameters
    (each with a case label), and lists its constructors (each with
    a signature specifying parameter types and the return type). *)
Record adt_decl := mk_adt {
  adt_name   : data_name;
  adt_params : list (tyvar_name * case_label);
  adt_ctors  : list (ctor_name * signature);
}.

(* ================================================================= *)
(** ** Programs *)
(* ================================================================= *)

(** A program consists of ADT declarations, function definitions,
    and a top-level expression.  Well-formedness ([program_ok])
    requires that all ADTs and functions are well-typed, and that
    the top-level expression is well-typed in pure mode. *)
Record program := mk_program {
  prog_adts : list adt_decl;
  prog_funs : list fun_def;
  prog_expr : expr;
}.

(* ================================================================= *)
(** ** Other Contexts *)
(* ================================================================= *)

(** Function context maps a function name to all of its callable
    interfaces. Overloading is modeled by returning a list. *)
Definition fun_ctx := fun_name -> list signature.

(** Constructors are not overloaded, so a constructor context maps each
    constructor name to at most one signature. *)
Definition ctor_ctx := ctor_name -> option signature.

(** The ADT context exposes the declared algebraic data types. *)
Definition adt_ctx := data_name -> option adt_decl.

(** The effect context records whether a function name denotes an
    effectful verb or a pure noun phrase. *)
Definition effect_ctx := fun_name -> bool.

(* ================================================================= *)
(** ** Typing Contexts *)
(* ================================================================= *)

(** Type variable contexts ([ty_ctx]) and value contexts ([val_ctx])
    are association lists.  Using lists rather than finite maps keeps
    the formalization simple and avoids funext issues. *)
Definition ty_ctx := list tyvar_name.
(** Value contexts map term variables to their types. *)
Definition val_ctx := list (var_name * ty).

(** Extract just the variable names from a value context.  Disjointness and
    freshness lemmas phrase their side conditions through this projection. *)
Definition ctx_names (Gamma : val_ctx) : list var_name :=
  List.map fst Gamma.

(** Two contexts are disjoint when no variable name appears in both of their
    name lists. *)
Definition ctx_disjoint (G1 G2 : val_ctx) : Prop :=
  forall x, In x (ctx_names G1) -> ~ In x (ctx_names G2).

(** Context lookup is left-biased: the first binding shadows later ones. *)
Fixpoint ctx_lookup (G : val_ctx) (x : var_name) : option ty :=
  match G with
  | nil => None
  | (y, t) :: G' => if String.eqb x y then Some t else ctx_lookup G' x
  end.

(** Extend a context with a fresh left-biased binding. *)
Definition ctx_extend (G : val_ctx) (x : var_name) (t : ty) : val_ctx :=
  (x, t) :: G.

(** Concatenate contexts by putting the left context in front, so its bindings
    shadow the right context during lookup. *)
Definition ctx_concat (G1 G2 : val_ctx) : val_ctx := List.app G1 G2.

(* ================================================================= *)
(** ** Type Substitution *)
(* ================================================================= *)

(** Type substitutions are association lists from type variables to types. *)
Definition ty_subst := list (tyvar_name * ty).

(** [apply_subst theta t] substitutes type variables according to [theta].
    Only free occurrences of declared type variables are affected. *)
Fixpoint apply_subst (theta : ty_subst) (t : ty) : ty :=
  match t with
  | TyVar a =>
    match List.find (fun p => String.eqb (fst p) a) theta with
    | Some (_, t') => t'
    | None => TyVar a
    end
  | TyInt => TyInt
  | TyFloat => TyFloat
  | TyString => TyString
  | TyChar => TyChar
  | TyData D args =>
    TyData D (List.map (fun p => (apply_subst theta (fst p), snd p)) args)
  | TyArr t1 t2 =>
    TyArr (apply_subst theta t1) (apply_subst theta t2)
  end.

(* ================================================================= *)
(** ** Auxiliary Predicates: Case-Label Alignment *)
(* ================================================================= *)

(** The following definitions implement the core of Kip's
    case-labeled calling convention.  At every call site, arguments
    are tagged with case labels.  The callee declares which case
    labels its parameters expect.  [align_cases_compute] reorders
    the provided arguments to match the parameter order, picking
    each argument by its case label. *)

(** [extract_cases] forgets payloads and remembers only the case labels
    attached to a list of arguments or parameters. *)
Definition extract_cases {A : Type} (xs : list (A * case_label)) : list case_label :=
  List.map snd xs.

(** [pick_case_payload c xs] removes the first argument in [xs] carrying
    case [c], returning its payload together with the remaining arguments. *)
Fixpoint pick_case_payload {A : Type}
  (c : case_label) (xs : list (A * case_label))
  : option (A * list (A * case_label)) :=
  match xs with
  | nil => None
  | (a, c') :: xs' =>
    if case_label_eq_dec c c'
    then Some (a, xs')
    else
      match pick_case_payload c xs' with
      | Some (a', rest) => Some (a', (a, c') :: rest)
      | None => None
      end
  end.

(** [align_cases_compute expected provided] reorders [provided] into the
    parameter order described by [expected]. It fails when a required case
    is missing or when extra arguments remain after alignment. When case
    labels are distinct, the written order of [provided] is irrelevant; when
    labels repeat, matching proceeds left to right through the provided
    list. *)
Fixpoint align_cases_compute {A : Type}
  (expected : list case_label) (provided : list (A * case_label))
  : option (list A) :=
  match expected with
  | nil =>
    match provided with
    | nil => Some nil
    | _ => None
    end
  | c :: cs =>
    match pick_case_payload c provided with
    | None => None
    | Some (a, provided') =>
      match align_cases_compute cs provided' with
      | Some rest => Some (a :: rest)
      | None => None
      end
    end
  end.

(** This is the propositional wrapper around [align_cases_compute]:
    [align_cases expected provided aligned] says that the provided labeled
    arguments can be reordered to [aligned] according to [expected]. In
    particular, distinct labels make the judgment permutation-invariant,
    while repeated labels remain sensitive to the written order. *)
Definition align_cases {A : Type}
  (expected : list case_label)
  (provided : list (A * case_label))
  (aligned : list A) : Prop :=
  align_cases_compute expected provided = Some aligned.

(* ================================================================= *)
(** ** Constructor Regularity *)
(* ================================================================= *)

(** Constructor regularity is the explicit invariant that makes constructor
    pattern matching sound.  A regular constructor context says:

    - its quantified type variables are pairwise distinct;
    - its result type is an ADT headed by some [D];
    - the result's case-labeled arguments are exactly those quantified
      variables, one per result case, possibly written in a different order.

    This is the formalization's "no hidden existential payload types"
    requirement: once the result type is known, the constructor payload types
    are determined. *)
Definition regular_constructor_ctx (sigma : signature) : Prop :=
  exists D result_cases ret_args,
    NoDup (signature_tvars sigma) /\
    NoDup result_cases /\
    length result_cases = length (signature_tvars sigma) /\
    signature_return_ty sigma = TyData D ret_args /\
    align_cases result_cases ret_args
      (List.map TyVar (signature_tvars sigma)).

(** A constructor context is regular when every constructor signature is. *)
Definition ctor_ctx_regular (Sc : ctor_ctx) : Prop :=
  forall C sigma,
    Sc C = Some sigma ->
    regular_constructor_ctx sigma.

(** Canonical arguments are case-aligned arguments paired back up with
    the parameter-order case labels expected by the callee. *)
Definition canonical_args (expected : list case_label)
  (args : list (expr * case_label))
  : option (list (expr * case_label)) :=
  match align_cases_compute expected args with
  | Some aligned => Some (combine aligned expected)
  | None => None
  end.

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
(** ** Runtime Pattern Matching and Semantic Values *)
(* ================================================================= *)

(** [pat_match Sc p v rho] is the runtime pattern-matching relation.
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
    monomorphic runtime environment and the polymorphic function-definition
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

(** Monomorphic runtime entries use the special case with no additional type
    substitution. *)
Definition clauses_exhaustive
  (Se : effect_ctx) (Sf : fun_ctx) (Sc : ctor_ctx)
  (mu : eff_mode) (sigma : signature) (clauses : fun_def) : Prop :=
  clauses_exhaustive_under Se Sf Sc mu [] sigma clauses.

(** Elimination principle for single-pattern runtime matching. *)
Scheme pat_match_ind' := Induction for pat_match Sort Prop
with pats_match_ind' := Induction for pats_match Sort Prop.
(** Mutual elimination principle for runtime pattern matching on a single
    pattern and on aligned pattern lists.  The typing lemmas for matching use
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

(* ================================================================= *)
(** ** Proof Automation *)
(* ================================================================= *)

(** This section collects [Ltac] tactics used throughout the
    metatheory.  Centralising them here ensures that every downstream
    proof can use them, and that proof-engineering patterns are
    documented in a single place. *)

(** [option_inject] handles the common pattern where two [Some]
    equalities in context yield an equality of payloads. *)
Ltac option_inject :=
  match goal with
  | [ H1 : ?lhs = Some ?a, H2 : ?lhs = Some ?b |- _ ] =>
      rewrite H1 in H2; injection H2; intros; subst; auto
  end.

(** [invert_has_type] inverts a [has_type] hypothesis and performs
    [subst].  Useful as a one-shot tactic for simple inversion
    lemmas. *)
Ltac invert_has_type :=
  match goal with
  | [ H : has_type _ _ _ _ _ _ _ |- _ ] => inversion H; subst; clear H
  end.

(** [eauto_split] repeatedly introduces existential witnesses and
    conjunctions, then lets [eauto] discharge the easy leaves. *)
Ltac eauto_split :=
  repeat match goal with
  | |- exists _, _ => eexists
  | |- _ /\ _ => split
  end; eauto with kip_hints.

(** The remaining automation tactics ([invert_plain_type_tac],
    [rewrite_fun_entry_signature], [solve_signature_arity_contradiction],
    [rewrite_ctor_ctx]) are defined later in the file, after the
    lemmas they depend on (e.g. [fun_entry_ctx_full_resolves_signature]) have
    been proved.  See the "Local Automation" section. *)

(** Hint database for [eauto] in the metatheory.  Hints for lemmas
    that are defined later (e.g. [match_partial_nil]) are registered
    near the lemma definitions, not here. *)
Create HintDb kip_hints discriminated.

#[export] Hint Constructors join : kip_hints.

(* ================================================================= *)
(** ** Metatheoretic Properties *)
(* ================================================================= *)

(** *** Effect Safety *)

(** Sequencing and binding forms cannot be typed in pure mode.
    The proof destructs the expression and inverts the typing
    derivation; [ESeq] and [EBind] require [Eff] mode, so the
    inversion yields no subgoals. *)
Theorem effect_safety_seq_bind :
  forall Se Sf Sc Gamma e upsilon,
    has_type Se Sf Sc Gamma Pure e upsilon ->
    match e with
    | ESeq _ _ => False
    | EBind _ _ _ => False
    | _ => True
    end.
Proof.
  intros Se Sf Sc Gamma e upsilon Hty.
  destruct e; auto; inversion Hty.
Qed.

(** Effectful function calls cannot be typed in pure mode.
    We invert the typing derivation for [EApp] and use [match goal
    with] to find the effectfulness premise without depending on its
    automatically-assigned name. *)
Theorem effectful_app_rejected_in_pure :
  forall Se Sf Sc Gamma f args upsilon,
    Se f = true ->
    ~ has_type Se Sf Sc Gamma Pure (EApp f args) upsilon.
Proof.
  intros Se Sf Sc Gamma f args upsilon Heff Hty.
  inversion Hty; subst;
  match goal with
  | [ H : (Se _ = true -> _ = Eff) |- _ ] =>
    specialize (H Heff); discriminate
  end.
Qed.

(** Combined effect safety: effectful expressions are rejected in
    pure mode.  Case-splits on the [effect_expr] derivation; each
    constructor is dismissed by inverting the typing derivation or
    delegating to [effectful_app_rejected_in_pure]. *)
Theorem effect_safety :
  forall Se Sf Sc Gamma e upsilon,
    has_type Se Sf Sc Gamma Pure e upsilon ->
    ~ effect_expr Se e.
Proof.
  intros Se Sf Sc Gamma e upsilon Hty Heff.
  inversion Heff; subst.
  - (* ESeq *)  inversion Hty.
  - (* EBind *) inversion Hty.
  - (* EApp effectful *) eapply effectful_app_rejected_in_pure; eauto.
Qed.

(** Effect rejection is sound: any effectful expression is rejected
    in pure mode. *)
Theorem effect_rejection_sound :
  forall Se Sf Sc Gamma e,
    effect_expr Se e ->
    effect_rejected Se Sf Sc Gamma e.
Proof.
  intros Se Sf Sc Gamma e Heff.
  unfold effect_rejected; split; auto.
  intros upsilon Hty; eapply effect_safety; eauto.
Qed.

(** *** Context Lookup Properties *)

(** Lookup is deterministic: the same variable in the same context
    yields the same type.  [congruence] handles the [Some]-injection
    and equality chaining automatically. *)
Lemma ctx_lookup_deterministic :
  forall G x t1 t2,
    ctx_lookup G x = Some t1 ->
    ctx_lookup G x = Some t2 ->
    t1 = t2.
Proof. intros; congruence. Qed.

(** Extending a context with [(x, t)] and looking up [x] yields [t]. *)
Lemma ctx_lookup_extend_same :
  forall G x t,
    ctx_lookup (ctx_extend G x t) x = Some t.
Proof.
  intros; unfold ctx_extend; simpl.
  rewrite String.eqb_refl; reflexivity.
Qed.

(** Looking up a variable different from the extension key ignores
    the extension.  We destruct the boolean equality and discharge
    the impossible branch via [String.eqb_eq]. *)
Lemma ctx_lookup_extend_diff :
  forall G x y t,
    x <> y ->
    ctx_lookup (ctx_extend G y t) x = ctx_lookup G x.
Proof.
  intros G x y t Hneq; unfold ctx_extend; simpl.
  destruct (String.eqb x y) eqn:Heqb;
    [ apply String.eqb_eq in Heqb; contradiction
    | reflexivity ].
Qed.

(** *** Typing Determinism *)

(** Variable typing is deterministic: both derivations must use
    [T_Var], and the result follows from [ctx_lookup] being a
    function.  We use [match goal with] to find the two lookup
    hypotheses without naming them. *)
Lemma var_typing_deterministic :
  forall Se Sf Sc Gamma mu x t1 t2 k1 k2,
    has_type Se Sf Sc Gamma mu (EVar x) (t1, k1) ->
    has_type Se Sf Sc Gamma mu (EVar x) (t2, k2) ->
    t1 = t2 /\ k1 = k2.
Proof.
  intros Se Sf Sc Gamma mu x t1 t2 k1 k2 Hty1 Hty2.
  inversion Hty1; subst; inversion Hty2; subst.
  match goal with
  | [ H1 : ctx_lookup _ _ = Some _,
      H2 : ctx_lookup _ _ = Some _ |- _ ] =>
      rewrite H1 in H2; injection H2; intros; subst; auto
  end.
Qed.

(** Literal typing is deterministic: [T_Lit] fixes the type to
    [literal_ty c] and the result case to [None]. *)
Lemma literal_typing_deterministic :
  forall Se Sf Sc Gamma mu c t1 t2 k1 k2,
    has_type Se Sf Sc Gamma mu (ELit c) (t1, k1) ->
    has_type Se Sf Sc Gamma mu (ELit c) (t2, k2) ->
    t1 = t2 /\ k1 = k2.
Proof.
  intros Se Sf Sc Gamma mu c t1 t2 k1 k2 Hty1 Hty2.
  inversion Hty1; subst; inversion Hty2; subst; auto.
Qed.

(** *** Join Properties *)

(** [join] is deterministic because both constructors fix the
    result type to a single value.  Induction on one derivation
    and inversion of the other suffice. *)
Theorem join_deterministic :
  forall ts t1 t2,
    join ts t1 -> join ts t2 -> t1 = t2.
Proof.
  intros ts t1 t2 Hj1 Hj2.
  induction Hj1; inversion Hj2; subst; auto.
Qed.

(** Every element of a joined list equals the join result. *)
Theorem join_all_equal :
  forall ts t,
    join ts t -> Forall (fun t' => t' = t) ts.
Proof.
  intros ts t Hj; induction Hj; constructor; auto.
Qed.

(** A joined list is always nonempty. *)
Lemma join_nonempty :
  forall ts t, join ts t -> ts <> nil.
Proof. intros ts t Hj; inversion Hj; discriminate. Qed.

(** *** Substitution Properties *)

(** The empty substitution is the identity.  We use [fix IH 1]
    instead of standard [induction] because [ty] is nested inside
    [list] in the [TyData] constructor; standard [induction] does
    not recurse into the list elements. *)
Theorem apply_subst_nil :
  forall t, apply_subst nil t = t.
Proof.
  fix IH 1.
  intro t; destruct t; simpl; auto.
  - f_equal. induction args as [| [t' c'] rest IHrest]; simpl; auto.
    f_equal; [f_equal; apply IH | apply IHrest].
  - f_equal; apply IH.
Qed.

(** Substitution leaves primitive types unchanged. *)
Lemma apply_subst_prim :
  forall theta,
    apply_subst theta TyInt = TyInt /\
    apply_subst theta TyFloat = TyFloat /\
    apply_subst theta TyString = TyString /\
    apply_subst theta TyChar = TyChar.
Proof. intros; repeat split; reflexivity. Qed.

(** The type of a literal is always a primitive, hence closed under
    any substitution. *)
Lemma apply_subst_literal_ty :
  forall theta c,
    apply_subst theta (literal_ty c) = literal_ty c.
Proof. intros; destruct c; reflexivity. Qed.

(** Looking up the distinguished head variable in a freshly-extended
    substitution always returns the head payload. *)
Lemma apply_subst_tyvar_head :
  forall a t theta,
    apply_subst ((a, t) :: theta) (TyVar a) = t.
Proof.
  intros a t theta.
  simpl.
  rewrite String.eqb_refl.
  reflexivity.
Qed.

(** Applying a [combine]-generated substitution to the very type variables it
    was built from recovers the payload list. *)
Lemma map_apply_subst_combine_tyvars :
  forall tvars tys,
    NoDup tvars ->
    length tys = length tvars ->
    List.map (apply_subst (combine tvars tys)) (List.map TyVar tvars) = tys.
Proof.
  intros tvars.
  induction tvars as [|a tvars IH]; intros tys Hnodup Hlen.
  - destruct tys; simpl in *; [reflexivity|discriminate].
  - destruct tys as [|t tys]; [discriminate|].
    inversion Hnodup as [|? ? Hnotin Hnodup']; subst.
    inversion Hlen; subst.
    simpl.
    rewrite String.eqb_refl.
    f_equal.
    transitivity (List.map (apply_subst (combine tvars tys)) (List.map TyVar tvars)).
    2:{ apply IH; assumption. }
    apply map_ext_in.
    intros x Hin.
    apply in_map_iff in Hin.
    destruct Hin as [b [Hx Hin]].
    subst x.
    simpl.
    destruct (String.eqb a b) eqn:Heq; [|reflexivity].
    apply String.eqb_eq in Heq. subst b.
    exfalso.
    apply Hnotin.
    exact Hin.
Qed.

(** *** MatchPartial Properties *)

(** [match_partial] is deterministic because the underlying
    computation function is. *)
Theorem match_partial_deterministic :
  forall expected provided i1 i2,
    match_partial expected provided i1 ->
    match_partial expected provided i2 ->
    i1 = i2.
Proof. unfold match_partial; intros; congruence. Qed.

(** The empty provided list matches the empty index list. *)
Lemma match_partial_nil :
  forall expected, match_partial expected nil nil.
Proof. unfold match_partial; simpl; reflexivity. Qed.

(** *** Weakening (per expression form) *)

(** Weakening for variables: extending the context with a fresh
    variable does not invalidate existing variable lookups.
    The key step is showing that [ctx_lookup] in the extended context
    still returns the same type; the impossible branch (where [y = x])
    is dismissed because [x] is fresh (not in [Gamma]). *)
Lemma weakening_var :
  forall Se Sf Sc Gamma mu y t k x tau_fresh,
    ctx_lookup Gamma x = None ->
    has_type Se Sf Sc Gamma mu (EVar y) (t, k) ->
    has_type Se Sf Sc (ctx_extend Gamma x tau_fresh) mu (EVar y) (t, k).
Proof.
  intros Se Sf Sc Gamma mu y t k x tau_fresh Hfresh Hty.
  inversion Hty; subst.
  eapply T_Var.
  unfold ctx_extend; simpl.
  destruct (String.eqb y x) eqn:Heqb.
  - apply String.eqb_eq in Heqb; subst.
    match goal with
    | [ H1 : ctx_lookup ?G ?z = None,
        H2 : ctx_lookup ?G ?z = Some _ |- _ ] =>
        rewrite H1 in H2; discriminate
    end.
  - assumption.
Qed.

(** Weakening for literals is trivial: literals do not use the
    context at all. *)
Lemma weakening_literal :
  forall Se Sf Sc Gamma mu c t k x tau_fresh,
    has_type Se Sf Sc Gamma mu (ELit c) (t, k) ->
    has_type Se Sf Sc (ctx_extend Gamma x tau_fresh) mu (ELit c) (t, k).
Proof.
  intros; match goal with
  | [ H : has_type _ _ _ _ _ (ELit _) _ |- _ ] =>
      inversion H; subst
  end; apply T_Lit.
Qed.

(** This is the unproved full weakening theorem stated as a proposition:
    extending the context with a fresh variable should preserve any typing
    derivation. *)
Definition weakening_statement : Prop :=
  forall Se Sf Sc Gamma mu e upsilon x tau,
    ctx_lookup Gamma x = None ->
    has_type Se Sf Sc Gamma mu e upsilon ->
    has_type Se Sf Sc (ctx_extend Gamma x tau) mu e upsilon.

(** *** Constructor Context Determinism *)

(** Constructor contexts are functions, so equal inputs give equal
    outputs.  [congruence] discharges this in one step. *)
Lemma ctor_ctx_deterministic :
  forall (Sc : ctor_ctx) C sigma1 sigma2,
    Sc C = Some sigma1 ->
    Sc C = Some sigma2 ->
    sigma1 = sigma2.
Proof. intros; congruence. Qed.

(** *** Pattern Binding Properties *)

(** Each catch-all pattern form binds a predictable context:
    - [PWild] binds nothing;
    - [PVarPat x] binds exactly [(x, tau)];
    - [PLit c] binds nothing (literals carry no variables). *)

Lemma pat_bind_wild_nil :
  forall Sc tau Gamma,
    pat_bind Sc PWild tau Gamma -> Gamma = nil.
Proof. now inversion 1. Qed.

(** A variable pattern contributes exactly one binding: the matched variable
    gets the scrutinee's type. *)
Lemma pat_bind_var_singleton :
  forall Sc x tau Gamma,
    pat_bind Sc (PVarPat x) tau Gamma -> Gamma = [(x, tau)].
Proof. now inversion 1. Qed.

(** Literal patterns inspect the scrutinee but never extend the typing
    context with new variables. *)
Lemma pat_bind_literal_nil :
  forall Sc c tau Gamma,
    pat_bind Sc (PLit c) tau Gamma -> Gamma = nil.
Proof. now inversion 1. Qed.

(** *** Sub-Expression Typing *)

(** These "sub-expression" lemmas extract typing information about
    immediate sub-expressions from the typing derivation of a
    compound expression.  They are used extensively in the
    preservation proof. *)

(** An ascription derivation witnesses that the sub-expression has
    a compatible type. *)
Lemma ascription_sub_typing :
  forall Se Sf Sc Gamma mu e tau_ann tau kres,
    has_type Se Sf Sc Gamma mu (EAscribe e tau_ann) (tau, kres) ->
    exists tau' kres',
      has_type Se Sf Sc Gamma mu e (tau', kres') /\
      compat tau' tau_ann /\
      tau = tau_ann /\ kres = kres'.
Proof.
  intros Se Sf Sc Gamma mu e tau_ann tau kres Hty.
  inversion Hty; subst; unfold compat in *; subst.
  eexists; eexists; eauto.
Qed.

(** The scrutinee of a typed match is typed. *)
Lemma match_scrutinee_typed :
  forall Se Sf Sc Gamma mu es branches tau kres,
    has_type Se Sf Sc Gamma mu (EMatch es branches) (tau, kres) ->
    exists tau_s kres_s,
      has_type Se Sf Sc Gamma mu es (tau_s, kres_s).
Proof.
  intros Se Sf Sc Gamma mu es branches tau kres Hty.
  inversion Hty; subst; eauto.
Qed.

(** The first sub-expression of a typed bind is typed. *)
Lemma bind_sub_typing :
  forall Se Sf Sc Gamma x e1 e2 tau kres,
    has_type Se Sf Sc Gamma Eff (EBind x e1 e2) (tau, kres) ->
    exists tau1 kres1,
      has_type Se Sf Sc Gamma Eff e1 (tau1, kres1).
Proof.
  intros Se Sf Sc Gamma x e1 e2 tau kres Hty.
  inversion Hty; subst; eauto.
Qed.

(** Both sub-expressions of a typed sequencing are typed. *)
Lemma seq_sub_typing :
  forall Se Sf Sc Gamma e1 e2 tau kres,
    has_type Se Sf Sc Gamma Eff (ESeq e1 e2) (tau, kres) ->
    (exists tau1 kres1, has_type Se Sf Sc Gamma Eff e1 (tau1, kres1)) /\
    has_type Se Sf Sc Gamma Eff e2 (tau, kres).
Proof.
  intros Se Sf Sc Gamma e1 e2 tau kres Hty.
  inversion Hty; subst; eauto.
Qed.

(** *** Result-Case Marker Properties *)

(** Variables, literals, and matches always produce [kres = None].
    Constructor applications always produce [kres = Some rc].
    These follow immediately by inverting the typing derivation. *)

Lemma var_result_case_none :
  forall Se Sf Sc Gamma mu x tau kres,
    has_type Se Sf Sc Gamma mu (EVar x) (tau, kres) ->
    kres = None.
Proof. now inversion 1. Qed.

(** Literals are plain values, so their typing judgment carries no
    return-case annotation. *)
Lemma literal_result_case_none :
  forall Se Sf Sc Gamma mu c tau kres,
    has_type Se Sf Sc Gamma mu (ELit c) (tau, kres) ->
    kres = None.
Proof. now inversion 1. Qed.

(** The match rule always returns an ordinary type, so its result-case
    component is forced to [None]. *)
Lemma match_result_case_none :
  forall Se Sf Sc Gamma mu es branches tau kres,
    has_type Se Sf Sc Gamma mu (EMatch es branches) (tau, kres) ->
    kres = None.
Proof. now inversion 1. Qed.

(** Constructor applications always inherit a concrete return case from the
    constructor contexts. *)
Lemma ctor_result_case_some :
  forall Se Sf Sc Gamma mu C args tau kres,
    has_type Se Sf Sc Gamma mu (ECtor C args) (tau, kres) ->
    exists rc, kres = Some rc.
Proof.
  intros Se Sf Sc Gamma mu C args tau kres Hty.
  inversion Hty; subst; eauto.
Qed.

(** *** Pure Function Calls *)

(** A pure function head ([Se f = false]) adds no effectfulness
    constraint.  The mode premise [(Se f = true -> mu = Eff)] is
    vacuously satisfied because [Se f = false]. *)
Lemma pure_app_head_unconstrained :
  forall Se Sf Sc Gamma mu f sigma (theta : list (tyvar_name * ty))
    (args : list (expr * case_label)) (args_aligned : list expr),
    In sigma (Sf f) ->
    Se f = false ->
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
      (apply_subst bound (signature_return_ty sigma), Some (signature_return_case sigma)).
Proof.
  intros Se Sf Sc Gamma mu f sigma theta args args_aligned Hsig Hpure Htheta
    bound Halign Hargs.
  eapply T_App; eauto.
  (* The effectfulness premise is vacuously true: *)
  intros Htrue; rewrite Hpure in Htrue; discriminate.
Qed.

(* ================================================================= *)
(** ** Order Independence for Distinct Cases *)
(* ================================================================= *)

(** A key design feature of Kip is that function and constructor
    arguments are matched to parameters by _case label_, not by
    position.  This section proves that when the provided case labels
    are pairwise distinct, the result of [align_cases_compute] is
    invariant under permutations of the argument list.

    The proof strategy is:
    1. Prove adjacent-swap invariance ([align_cases_compute_swap]):
       swapping two adjacent arguments with different case labels
       does not change the alignment result.
    2. Lift to full [Permutation] invariance using the Stdlib
       [Permutation] inductive type and auxiliary lemmas about
       [pick_case_payload].

    The [Permutation] infrastructure from Stdlib is imported here. *)

(** When two adjacent provided arguments carry different case labels,
    swapping them does not change the result of [align_cases_compute].
    This requires NO hypothesis about the rest of the list -- it holds
    unconditionally because [pick_case_payload] finds by case label,
    so elements with non-matching cases are simply skipped past.

    Since any permutation of a list with pairwise-distinct labels
    can be decomposed into adjacent transpositions of elements
    with distinct labels, this lemma implies full order independence
    when provided case labels are distinct. *)

Lemma align_cases_compute_swap :
  forall (A : Type) expected (a1 a2 : A) c1 c2 rest,
    c1 <> c2 ->
    @align_cases_compute A expected ((a1,c1) :: (a2,c2) :: rest) =
    @align_cases_compute A expected ((a2,c2) :: (a1,c1) :: rest).
Proof.
  intros A expected.
  induction expected as [| c cs IH]; intros a1 a2 c1 c2 rest Hneq.
  - (* expected = [] : both sides are None since provided is nonempty *)
    reflexivity.
  - (* expected = c :: cs *)
    simpl.
    destruct (case_label_eq_dec c c1) as [Ec1|Ec1];
    destruct (case_label_eq_dec c c2) as [Ec2|Ec2].
    + (* c = c1 and c = c2 contradicts c1 <> c2 *)
      subst. exfalso. apply Hneq. reflexivity.
    + (* c = c1, c <> c2:
         LHS picks a1, rest = (a2,c2)::rest
         RHS skips (a2,c2), then picks a1, rest = (a2,c2)::rest *)
      reflexivity.
    + (* c <> c1, c = c2:
         LHS skips (a1,c1), picks a2, rest = (a1,c1)::rest
         RHS picks a2, rest = (a1,c1)::rest *)
      reflexivity.
    + (* c <> c1 and c <> c2:
         both skip to rest, find same element a';
         LHS recursion gets (a1,c1)::(a2,c2)::rest'
         RHS recursion gets (a2,c2)::(a1,c1)::rest'
         IH finishes *)
      destruct (pick_case_payload c rest) as [[a' rest']|] eqn:Epick.
      * (* pick found a' in rest *)
        rewrite IH; auto.
      * (* pick found nothing in rest *)
        reflexivity.
Qed.

(** *** Permutation infrastructure *)

(** We use the Stdlib [Permutation] inductive type to state and prove
    full order-independence for [align_cases_compute] when the
    provided case labels are pairwise distinct ([NoDup]).

    The key auxiliary lemmas are:
    - [pick_rest_In]: membership in [extract_cases] is preserved
      when an element is picked out.
    - [pick_rest_NoDup]: uniqueness of case labels is preserved.
    - [pick_none_iff]: [pick_case_payload] returns [None] iff the
      case is absent.
    - [pick_Permutation]: [pick_case_payload] commutes with
      [Permutation] (up to permuted remainders). *)

From Stdlib Require Import Sorting.Permutation.

(** [pick_case_payload] rest is a sub-list: membership is preserved. *)
Lemma pick_rest_In :
  forall (A : Type) c (xs : list (A * case_label)) a rest,
    pick_case_payload c xs = Some (a, rest) ->
    forall x, In x (extract_cases rest) -> In x (extract_cases xs).
Proof.
  intros A c xs. induction xs as [|[a' c'] xs' IH]; simpl; intros a rest H x Hin.
  - discriminate.
  - destruct (case_label_eq_dec c c').
    + inversion H; subst. right. exact Hin.
    + destruct (pick_case_payload c xs') as [[a'' rest']|] eqn:E; try discriminate.
      inversion H; subst. simpl in Hin. destruct Hin as [Heq|Hin'].
      * left. exact Heq.
      * right. eapply IH; eauto.
Qed.

(** [pick_case_payload] preserves uniqueness of the remaining case labels. *)
Lemma pick_rest_NoDup :
  forall (A : Type) c (xs : list (A * case_label)) a rest,
    NoDup (extract_cases xs) ->
    pick_case_payload c xs = Some (a, rest) ->
    NoDup (extract_cases rest).
Proof.
  intros A c xs. induction xs as [|[a' c'] xs' IH]; simpl; intros a rest Hd Hp.
  - discriminate.
  - apply NoDup_cons_iff in Hd as [Hnotin Hd'].
    destruct (case_label_eq_dec c c').
    + inversion Hp; subst. exact Hd'.
    + destruct (pick_case_payload c xs') as [[a'' rest']|] eqn:E; try discriminate.
      inversion Hp; subst.
      apply NoDup_cons.
      * intro Hin. apply Hnotin. eapply pick_rest_In; eauto.
      * eapply IH; eauto.
Qed.

(** [pick_case_payload] returns [None] iff the case is absent. *)
Lemma pick_none_iff :
  forall (A : Type) c (xs : list (A * case_label)),
    pick_case_payload c xs = None <-> ~ In c (extract_cases xs).
Proof.
  intros A c xs. induction xs as [|[a' c'] xs' IH]; simpl.
  - tauto.
  - destruct (case_label_eq_dec c c') as [->|Hneq].
    + split; [discriminate | tauto].
    + destruct IH as [IH1 IH2]. split.
      * intros H [Heq|Hin].
        -- subst. contradiction.
        -- destruct (pick_case_payload c xs') as [[av rv]|];
             [discriminate | exact (IH1 eq_refl Hin)].
      * intro H.
        assert (Hni : ~ In c (extract_cases xs'))
          by (intro Hin; apply H; right; exact Hin).
        rewrite (IH2 Hni). reflexivity.
Qed.

(** [pick_case_payload] respects [Permutation] when cases are distinct:
    same payload, permuted rests.  The proof goes by induction on the
    [Permutation] derivation. *)
Lemma pick_Permutation :
  forall (A : Type) c (p1 p2 : list (A * case_label)) a r1,
    NoDup (extract_cases p1) ->
    Permutation p1 p2 ->
    pick_case_payload c p1 = Some (a, r1) ->
    exists r2,
      pick_case_payload c p2 = Some (a, r2) /\
      Permutation r1 r2.
Proof.
  intros A c p1 p2 a r1 Hd Hp. revert a r1 Hd.
  induction Hp; intros a0 r1 Hd Hpick.
  - (* perm_nil *) simpl in Hpick. discriminate.
  - (* perm_skip x l l' *)
    destruct x as [a' c'].
    simpl pick_case_payload in Hpick. simpl extract_cases in Hd.
    apply NoDup_cons_iff in Hd as [Hni Hd'].
    destruct (case_label_eq_dec c c') as [->|Hneq].
    + inversion Hpick; subst.
      exists l'. split.
      * simpl. destruct (case_label_eq_dec c' c'); [reflexivity|contradiction].
      * apply Hp.
    + 
      destruct (pick_case_payload c l) as [[a'' rest']|] eqn:E; try discriminate.
      injection Hpick. intros Hr Ha. subst a0 r1.
      destruct (IHHp a'' rest' Hd' eq_refl) as [r2' [Hr2' Hpr]].
      exists ((a', c') :: r2'). split.
      * simpl. destruct (case_label_eq_dec c c'); [contradiction|].
        rewrite Hr2'. reflexivity.
      * apply perm_skip. exact Hpr.
  - (* perm_swap x y l *)
    destruct x as [a1 c1]. destruct y as [a2 c2].
    simpl pick_case_payload in Hpick.
    simpl extract_cases in Hd.
    apply NoDup_cons_iff in Hd as [Hni1 Hd].
    apply NoDup_cons_iff in Hd as [Hni2 Hd'].
    destruct (case_label_eq_dec c c1) as [Ec1|Ec1];
    destruct (case_label_eq_dec c c2) as [Ec2|Ec2].
    + (* c = c1 = c2 → contradiction *)
      subst. exfalso. apply Hni1. left. reflexivity.
    + (* c = c1, c <> c2 *)
      inversion Hpick; subst.
      exists ((a2, c2) :: l). split; [|apply Permutation_refl].
      simpl.
      destruct (case_label_eq_dec c1 c2); [contradiction|].
      destruct (case_label_eq_dec c1 c1); [reflexivity|contradiction].
    + (* c <> c1, c = c2 *)
      inversion Hpick; subst.
      exists ((a1, c1) :: l). split; [|apply Permutation_refl].
      simpl.
      destruct (case_label_eq_dec c2 c1); [contradiction|].
      destruct (case_label_eq_dec c2 c2); [reflexivity|contradiction].
    + (* c <> c1, c <> c2 *)
      destruct (pick_case_payload c l) as [[a'' rest']|] eqn:E; try discriminate.
      injection Hpick. intros Hr Ha. subst.
      exists ((a1, c1) :: (a2, c2) :: rest'). split.
      * simpl.
        destruct (case_label_eq_dec c c2); [contradiction|].
        destruct (case_label_eq_dec c c1); [contradiction|].
        rewrite E. reflexivity.
      * apply perm_swap.
  - (* perm_trans *)
    specialize (IHHp1 a0 r1 Hd Hpick).
    destruct IHHp1 as [r2 [Hr2 Hpr1]].
    assert (Hd2 : NoDup (extract_cases l')).
    { eapply Permutation_NoDup.
      - apply Permutation_map. exact Hp1.
      - exact Hd.
    }
    specialize (IHHp2 a0 r2 Hd2 Hr2).
    destruct IHHp2 as [r3 [Hr3 Hpr2]].
    exists r3. split; auto.
    eapply Permutation_trans; eauto.
Qed.

(** Dual: if [pick] returns [None] for one list, it returns [None]
    for any permutation. *)
Lemma pick_Permutation_none :
  forall (A : Type) c (p1 p2 : list (A * case_label)),
    Permutation p1 p2 ->
    pick_case_payload c p1 = None ->
    pick_case_payload c p2 = None.
Proof.
  intros A c p1 p2 Hp Hn.
  apply pick_none_iff.
  apply pick_none_iff in Hn.
  intro Hin. apply Hn.
  eapply Permutation_in; [apply Permutation_sym; apply Permutation_map; exact Hp | exact Hin].
Qed.

(** *** Main theorem: full Permutation invariance *)

(** When all provided case labels are distinct, [align_cases_compute]
    is invariant under any [Permutation] of the provided list. *)
Theorem align_cases_compute_Permutation :
  forall (A : Type) expected (p1 p2 : list (A * case_label)),
    NoDup (extract_cases p1) ->
    Permutation p1 p2 ->
    align_cases_compute expected p1 = align_cases_compute expected p2.
Proof.
  intros A expected.
  induction expected as [|c cs IH]; intros p1 p2 Hd Hp.
  - destruct p1 as [|x p1']; destruct p2 as [|y p2']; simpl in *; try reflexivity.
    + exfalso. apply Permutation_length in Hp. simpl in Hp. discriminate.
    + exfalso. apply Permutation_length in Hp. simpl in Hp. discriminate.
  - simpl.
    destruct (pick_case_payload c p1) as [[a r1]|] eqn:E1.
    + destruct (pick_Permutation A c p1 p2 a r1 Hd Hp E1) as [r2 [E2 Hpr]].
      rewrite E2.
      assert (Hdr1 : NoDup (extract_cases r1)).
      { eapply pick_rest_NoDup; eauto. }
      rewrite (IH r1 r2 Hdr1 Hpr). reflexivity.
    + rewrite (pick_Permutation_none A c p1 p2 Hp E1).
      reflexivity.
Qed.

(** For the [align_cases] wrapper: *)
Theorem align_cases_Permutation :
  forall (A : Type) expected (p1 p2 : list (A * case_label)) aligned,
    NoDup (extract_cases p1) ->
    Permutation p1 p2 ->
    @align_cases A expected p1 aligned ->
    @align_cases A expected p2 aligned.
Proof.
  unfold align_cases. intros.
  rewrite <- (align_cases_compute_Permutation A expected p1 p2); auto.
Qed.

(* ================================================================= *)
(** ** Core Dynamic Semantics *)
(* ================================================================= *)

(** This section defines:
    - [has_plain_type]: the "erased" typing judgment that forgets
      the result-case annotation (used by preservation, which only
      needs to track the ordinary type);
    - values, substitution, and the small-step [step] relation;
    - the [fun_entry_ctx_ok] invariant connecting the runtime function
      environment with the declarative typing environment. *)

(** The parameters [Se], [Sf], and [Sc] are the global environments. The
    indices are a typing context [Gamma], an effect mode [mu], an expression
    [e], and an ordinary type [tau]; [has_plain_type Se Sf Sc Gamma mu e
    tau] means that [e] has type [tau] for some result-case annotation. *)
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

(** Executable function environments store one runtime entry per overload of
    a function name.  Each entry packages a monomorphic signature together
    with the clauses used when that overload is selected. *)
Record fun_entry := mk_fun_entry {
  fun_entry_signature : signature;
  fun_entry_clauses   : fun_def;
}.

(** Runtime function environments map a function name to its executable
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
    unique runtime overload selected for the full application [EApp f args] in
    mode [mu]. *)
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
    [entry] is the unique runtime overload selected for the partial
    application [EApp f args] in mode [mu].  Exact matches take precedence:
    partial resolution is only allowed when no full application candidate
    exists. *)
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

(** The parameters [F], [Sc], [Se], [Sf], and [mu] are the ambient runtime
    and static environments. The single index is an expression [e];
    [value F Sc e] says that [e] is a finished runtime value at those
    ambient parameters. *)
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
      core language: named functions live in the runtime [fun_entry_ctx], and the
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
    discipline.  Runtime overload resolution is static/type-directed: for a
    fixed function name and typed argument list there is at most one matching
    full overload, at most one matching partial overload, and the full match
    wins whenever both would otherwise apply. *)
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

(** The parameters [F], [Sc], [Se], [Sf], and [mu] are the ambient runtime
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
      and runtime environments. The indices are labeled argument lists [args]
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
      and runtime environments. The indices are expressions [e] and [e'];
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

(* ================================================================= *)
(** ** Context Concatenation Properties *)
(* ================================================================= *)

(** The following lemmas establish how [ctx_lookup] interacts with
    [ctx_concat], [ctx_extend], and related operations.  They are
    the plumbing needed for the context invariance, weakening, and
    substitution proofs. *)

(** A binding found in the left context survives concatenation. *)
Lemma ctx_lookup_concat_some_left :
  forall G1 G2 x tau,
    ctx_lookup G1 x = Some tau ->
    ctx_lookup (ctx_concat G1 G2) x = Some tau.
Proof.
  induction G1 as [|[y ty] G1 IH]; intros G2 x tau H; simpl in *.
  - discriminate.
  - destruct (String.eqb x y) eqn:E; simpl.
    + inversion H. reflexivity.
    + apply IH. exact H.
Qed.

(** If the left context misses [x], looking up [x] in a concatenation simply
    falls through to the right context. *)
Lemma ctx_lookup_concat_none_left :
  forall G1 G2 x,
    ctx_lookup G1 x = None ->
    ctx_lookup (ctx_concat G1 G2) x = ctx_lookup G2 x.
Proof.
  induction G1 as [|[y ty] G1 IH]; intros G2 x H; simpl in *.
  - reflexivity.
  - destruct (String.eqb x y) eqn:E; try discriminate.
    apply IH. exact H.
Qed.

(** Two pointwise-equal contexts remain interchangeable after prefixing both
    with the same context fragment. *)
Lemma ctx_lookup_concat_invariant :
  forall Delta G1 G2 x,
    (forall y, ctx_lookup G1 y = ctx_lookup G2 y) ->
    ctx_lookup (ctx_concat Delta G1) x = ctx_lookup (ctx_concat Delta G2) x.
Proof.
  induction Delta as [|[y ty] Delta IH]; intros G1 G2 x Heq; simpl.
  - apply Heq.
  - destruct (String.eqb x y); reflexivity || apply IH; exact Heq.
Qed.

(** Rebinding the same variable immediately shadows the older binding, so
    lookup cannot observe the first extension. *)
Lemma ctx_lookup_extend_shadowed :
  forall Gamma x tau_old tau_new y,
    ctx_lookup (ctx_extend (ctx_extend Gamma x tau_old) x tau_new) y =
    ctx_lookup (ctx_extend Gamma x tau_new) y.
Proof.
  intros Gamma x tau_old tau_new y.
  unfold ctx_extend. simpl.
  destruct (String.eqb y x); reflexivity.
Qed.

(** Extensions on distinct variables commute observationally because lookup
    sees the same answer in either order. *)
Lemma ctx_lookup_extend_commute :
  forall Gamma x tx y ty z,
    x <> y ->
    ctx_lookup (ctx_extend (ctx_extend Gamma x tx) y ty) z =
    ctx_lookup (ctx_extend (ctx_extend Gamma y ty) x tx) z.
Proof.
  intros Gamma x tx y ty z Hneq.
  unfold ctx_extend. simpl.
  destruct (String.eqb z y) eqn:Ezy, (String.eqb z x) eqn:Ezx; try reflexivity.
  - apply String.eqb_eq in Ezy. apply String.eqb_eq in Ezx. subst. contradiction.
Qed.

(** A right-hand extension for [x] cannot affect lookup of a different
    variable once the left fragment is fixed. *)
Lemma ctx_lookup_concat_extend_irrelevant :
  forall Gamma_p Gamma x tau_x y,
    y <> x ->
    ctx_lookup (ctx_concat Gamma_p (ctx_extend Gamma x tau_x)) y =
    ctx_lookup (ctx_concat Gamma_p Gamma) y.
Proof.
  induction Gamma_p as [|[z tz] Gamma_p IH]; intros Gamma x tau_x y Hneq; simpl.
  - apply ctx_lookup_extend_diff. exact Hneq.
  - destruct (String.eqb y z); [reflexivity|].
    apply IH. exact Hneq.
Qed.

(** If the left fragment already binds [x], then a later right-hand binding
    for [x] is completely hidden. *)
Lemma ctx_lookup_concat_extend_shadowed :
  forall Gamma_p Gamma x tau_p tau_x y,
    ctx_lookup Gamma_p x = Some tau_p ->
    ctx_lookup (ctx_concat Gamma_p (ctx_extend Gamma x tau_x)) y =
    ctx_lookup (ctx_concat Gamma_p Gamma) y.
Proof.
  induction Gamma_p as [|[z tz] Gamma_p IH]; intros Gamma x tau_p tau_x y Hlook; simpl in *.
  - discriminate.
  - destruct (String.eqb x z) eqn:Exz.
    + inversion Hlook; subst.
      destruct (String.eqb y z) eqn:Eyz.
      * reflexivity.
      * apply String.eqb_neq in Eyz.
        apply String.eqb_eq in Exz. subst.
        eapply ctx_lookup_concat_extend_irrelevant. exact Eyz.
    + destruct (String.eqb y z); [reflexivity|].
      eapply IH. exact Hlook.
Qed.

(** If the left fragment does not bind [x], extending the right fragment is
    equivalent to extending the concatenated context. *)
Lemma ctx_lookup_concat_extend_fresh :
  forall Gamma_p Gamma x tau_x y,
    ctx_lookup Gamma_p x = None ->
    ctx_lookup (ctx_concat Gamma_p (ctx_extend Gamma x tau_x)) y =
    ctx_lookup (ctx_extend (ctx_concat Gamma_p Gamma) x tau_x) y.
Proof.
  induction Gamma_p as [|[z tz] Gamma_p IH]; intros Gamma x tau_x y Hnone; simpl in *.
  - reflexivity.
  - destruct (String.eqb x z) eqn:Exz; [discriminate|].
    destruct (String.eqb y z) eqn:Eyz.
    + apply String.eqb_eq in Eyz. subst. rewrite String.eqb_sym. rewrite Exz. reflexivity.
    + eapply IH. exact Hnone.
Qed.

(** ** Context Invariance *)

(** If two contexts agree on every variable lookup, then any typing
    derivation under one context transfers to the other.

    The proof uses [fix IH 10] instead of standard [induction]
    because the typing judgment contains [Forall2]-structured
    sub-derivations in the application and constructor rules.
    Standard [induction] would not recurse into those lists.
    The fixpoint destructs the typing derivation and reconstructs
    each rule, applying [IH] at every recursive position.  The
    match and bind branches additionally use
    [ctx_lookup_concat_invariant] to propagate the context
    agreement through pattern-binding contexts. *)
Lemma has_type_ctx_invariant :
  forall Se Sf Sc Gamma1 Gamma2 mu e tau kres,
    has_type Se Sf Sc Gamma1 mu e (tau, kres) ->
    (forall x, ctx_lookup Gamma1 x = ctx_lookup Gamma2 x) ->
    has_type Se Sf Sc Gamma2 mu e (tau, kres).
Proof.
  fix IH 10.
  intros Se Sf Sc Gamma1 Gamma2 mu e tau kres Hty Heq.
  destruct Hty.
  - eapply T_Var. rewrite <- Heq. eauto.
  - constructor.
  - eapply T_Ascribe; eauto.
  - eapply T_App with (sigma := sigma) (theta := theta) (args_aligned := args_aligned); eauto.
    clear H2.
    induction H3 as [|arg param args' params' Hex Hrest IHrest]; constructor; eauto.
    destruct Hex as [kres_i Harg]. eexists. eapply IH; eauto.
  - eapply T_App_Partial with (sigma := sigma) (theta := theta) (indices := indices); eauto.
    clear H2 H3.
    induction H4 as [|arg idx args' idxs' Hhead Hrest IHrest]; constructor; eauto.
    destruct Hhead as [param [kres_i [Hnth Harg]]].
    exists param, kres_i. split; [eauto | eapply IH; eauto].
  - eapply T_Ctor with (sigma := sigma) (theta := theta) (args_aligned := args_aligned); eauto.
    clear H1.
    induction H2 as [|arg param args' params' Hex Hrest IHrest]; constructor; eauto.
    destruct Hex as [kres_i Harg]. eexists. eapply IH; eauto.
  - eapply T_Match with (tau_s := tau_s) (kres_s := kres_s);
      [eapply IH; eauto | eauto |].
    clear H.
    match goal with
    | [ Hbranches : Forall _ branches |- _ ] =>
        induction Hbranches as [|pb branches' Hbranch Hrest IHrest]
    end; constructor; eauto.
    destruct Hbranch as [Gamma_p [tau_j [kres_j [Hbind [Hbody Heqtau]]]]].
      eauto_split.
      eapply IH; [eauto |].
      intro y. unfold ctx_concat.
      eapply ctx_lookup_concat_invariant; eauto.
  - eapply T_Let.
    + eapply IH; eauto.
    + eapply IH; eauto.
      intro y. unfold ctx_extend. simpl.
      destruct (String.eqb y x); [reflexivity | apply Heq].
  - eapply T_Seq; eapply IH; eauto.
  - eapply T_Bind.
    + eapply IH; eauto.
    + eapply IH; eauto.
      intro y. unfold ctx_extend. simpl.
      destruct (String.eqb y x); [reflexivity | apply Heq].
Qed.

(** Appending an extra context on the right preserves typing.  This
    is a special case of weakening: variables in [Delta] shadow any
    bindings in [Gamma], so the derivation structure is unchanged.
    Same [fix]-based proof strategy as [has_type_ctx_invariant]. *)
Lemma has_type_ctx_concat_right :
  forall Se Sf Sc Delta Gamma mu e tau kres,
    has_type Se Sf Sc Delta mu e (tau, kres) ->
    has_type Se Sf Sc (ctx_concat Delta Gamma) mu e (tau, kres).
Proof.
  fix IH 10.
  intros Se Sf Sc Delta Gamma mu e tau kres Hty.
  destruct Hty.
  - eapply T_Var. eapply ctx_lookup_concat_some_left; eauto.
  - constructor.
  - eapply T_Ascribe; eauto.
  - eapply T_App with (sigma := sigma) (theta := theta) (args_aligned := args_aligned); eauto.
    clear H2.
    induction H3 as [|arg param args' params' Hex Hrest IHrest]; constructor; eauto.
    destruct Hex as [kres_i Harg]. eexists. eapply IH; eauto.
  - eapply T_App_Partial with (sigma := sigma) (theta := theta) (indices := indices); eauto.
    clear H2 H3.
    induction H4 as [|arg idx args' idxs' Hhead Hrest IHrest]; constructor; eauto.
    destruct Hhead as [param [kres_i [Hnth Harg]]].
    exists param, kres_i. split; [eauto | eapply IH; eauto].
  - eapply T_Ctor with (sigma := sigma) (theta := theta) (args_aligned := args_aligned); eauto.
    clear H1.
    induction H2 as [|arg param args' params' Hex Hrest IHrest]; constructor; eauto.
    destruct Hex as [kres_i Harg]. eexists. eapply IH; eauto.
  - eapply T_Match with (tau_s := tau_s) (kres_s := kres_s);
      [eapply IH; eauto | eauto |].
    clear H.
    match goal with
    | [ Hbranches : Forall _ branches |- _ ] =>
        induction Hbranches as [|pb branches' Hbranch Hrest IHrest]
    end; constructor; eauto.
    destruct Hbranch as [Gamma_p [tau_j [kres_j [Hbind [Hbody Heqtau]]]]].
      eauto_split.
      replace (ctx_concat Gamma_p (ctx_concat Gamma0 Gamma))
        with (ctx_concat (ctx_concat Gamma_p Gamma0) Gamma)
        by (unfold ctx_concat; rewrite app_assoc; reflexivity).
      eapply IH; eauto.
  - eapply T_Let.
    + eapply IH; eauto.
    + replace (ctx_extend (ctx_concat Gamma0 Gamma) x tau1)
        with (ctx_concat (ctx_extend Gamma0 x tau1) Gamma)
        by (unfold ctx_extend, ctx_concat; reflexivity).
      eapply IH; eauto.
  - eapply T_Seq; eapply IH; eauto.
  - eapply T_Bind.
    + eapply IH; eauto.
    + replace (ctx_extend (ctx_concat Gamma0 Gamma) x tau1)
        with (ctx_concat (ctx_extend Gamma0 x tau1) Gamma)
        by (unfold ctx_extend, ctx_concat; reflexivity).
      eapply IH; eauto.
Qed.

(** Plain typing weakens to the right just like full typing: adding a
    shadowed suffix context preserves the derivation. *)
Lemma has_plain_type_ctx_concat_right :
  forall Se Sf Sc Delta Gamma mu e tau,
    has_plain_type Se Sf Sc Delta mu e tau ->
    has_plain_type Se Sf Sc (ctx_concat Delta Gamma) mu e tau.
Proof.
  intros Se Sf Sc Delta Gamma mu e tau [kres Hty].
  exists kres. eapply has_type_ctx_concat_right; eauto.
Qed.

(** Successful lookup implies that the queried variable name actually
    appears in the context's name list. *)
Lemma ctx_lookup_in_names :
  forall G x tau,
    ctx_lookup G x = Some tau ->
    In x (ctx_names G).
Proof.
  induction G as [|[y ty] G IH]; intros x tau H; simpl in *.
  - discriminate.
  - destruct (String.eqb x y) eqn:E.
    + apply String.eqb_eq in E. subst. simpl. auto.
    + right. eapply IH. exact H.
Qed.

(** Conversely, every name listed by [ctx_names] is backed by some concrete
    binding in the context. *)
Lemma ctx_names_lookup_some :
  forall G x,
    In x (ctx_names G) ->
    exists tau, ctx_lookup G x = Some tau.
Proof.
  induction G as [|[y ty] G IH]; intros x Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Hin|Hin].
    + subst. exists ty. simpl. rewrite String.eqb_refl. reflexivity.
    + destruct (IH _ Hin) as [tau Htau].
      simpl.
      destruct (String.eqb x y) eqn:E.
      * exists ty. reflexivity.
      * exists tau. exact Htau.
Qed.

(** The empty context is disjoint from any context. *)
Lemma ctx_disjoint_nil_right :
  forall G, ctx_disjoint G [].
Proof. intros G x Hin; simpl; tauto. Qed.

(** Disjointness from a concatenated context splits into disjointness from
    each component separately. *)
Lemma ctx_disjoint_concat_right :
  forall G1 G2 G3,
    ctx_disjoint G1 (ctx_concat G2 G3) ->
    ctx_disjoint G1 G2 /\ ctx_disjoint G1 G3.
Proof.
  intros G1 G2 G3 H.
  split; intros x Hin1 Hin2; apply (H x Hin1).
  - unfold ctx_names, ctx_concat. rewrite List.map_app. apply in_or_app. left. exact Hin2.
  - unfold ctx_names, ctx_concat. rewrite List.map_app. apply in_or_app. right. exact Hin2.
Qed.

(** If two contexts are name-disjoint and [x] is bound in the first, then
    the second must fail to look up [x]. *)
Lemma ctx_disjoint_lookup_none :
  forall G1 G2 x tau,
    ctx_disjoint G1 G2 ->
    ctx_lookup G1 x = Some tau ->
    ctx_lookup G2 x = None.
Proof.
  intros G1 G2 x tau Hdis H1.
  induction G2 as [|[y ty] G2 IH]; simpl; auto.
  destruct (String.eqb x y) eqn:E.
  - apply String.eqb_eq in E. subst.
    exfalso. apply (Hdis y).
    + eapply ctx_lookup_in_names. exact H1.
    + simpl. left. reflexivity.
  - apply IH.
    intros z Hin1 Hin2. apply (Hdis z Hin1). simpl. right. exact Hin2.
Qed.

(** A well-typed substitution environment contains a closed, well-typed
    expression for every variable it advertises. *)
Lemma subst_env_typed_lookup :
  forall Se Sf Sc mu rho Delta x tau,
    subst_env_typed Se Sf Sc mu rho Delta ->
    ctx_lookup Delta x = Some tau ->
    exists v,
      expr_lookup rho x = Some v /\
      has_plain_type Se Sf Sc [] mu v tau.
Proof.
  intros Se Sf Sc mu rho Delta x tau Henv.
  induction Henv; intros Hlookup; simpl in *.
  - discriminate.
  - destruct (String.eqb x x0) eqn:E.
    + apply String.eqb_eq in E. subst.
      inversion Hlookup; subst.
      exists v. split.
      * simpl. reflexivity.
      * exists kres. exact H.
    + apply IHHenv in Hlookup.
      destruct Hlookup as [v' [Hfind Hty]].
      exists v'. split.
      * simpl. destruct (String.eqb x x0); [discriminate|exact Hfind].
      * exact Hty.
Qed.

(** When lengths match, combining payloads with labels and projecting the
    first component recovers the original payload list. *)
Lemma map_fst_combine :
  forall (A B : Type) (xs : list A) (ys : list B),
    length xs = length ys ->
    List.map fst (combine xs ys) = xs.
Proof.
  intros A B xs.
  induction xs as [|x xs IH]; intros ys Hlen.
  - destruct ys as [|y ys]; simpl in *; [reflexivity|discriminate].
  - destruct ys as [|y ys]; simpl in *; [discriminate|].
    inversion Hlen. simpl. f_equal. apply IH. assumption.
Qed.

(** Dually, projecting the second component of a well-sized [combine]
    recovers the original label list. *)
Lemma map_snd_combine :
  forall (A B : Type) (xs : list A) (ys : list B),
    length xs = length ys ->
    List.map snd (combine xs ys) = ys.
Proof.
  intros A B xs.
  induction xs as [|x xs IH]; intros ys Hlen.
  - destruct ys as [|y ys]; simpl in *; [reflexivity|discriminate].
  - destruct ys as [|y ys]; simpl in *; [discriminate|].
    inversion Hlen. simpl. f_equal. apply IH. assumption.
Qed.

(** Picking one labeled payload removes exactly one matching pair and
    otherwise only permutes the list. *)
Lemma pick_case_payload_Permutation :
  forall (A : Type) c (xs : list (A * case_label)) a rest,
    pick_case_payload c xs = Some (a, rest) ->
    Permutation xs ((a, c) :: rest).
Proof.
  intros A c xs a rest. revert a rest.
  induction xs as [|[a0 c0] xs IH]; intros a rest Hpick; simpl in Hpick.
  - discriminate.
  - destruct (case_label_eq_dec c c0) as [->|Hneq].
    + 
      inversion Hpick; subst. apply Permutation_refl.
    + destruct (pick_case_payload c xs) as [[a' rest']|] eqn:Htail; try discriminate.
      injection Hpick. intros Hrest Ha. subst a rest.
      specialize (IH a' rest' eq_refl).
      eapply Permutation_trans.
      * apply perm_skip. exact IH.
      * apply perm_swap.
Qed.

(** Successful alignment only reorders payloads; it preserves exactly the
    multiset of provided payload expressions. *)
Lemma align_cases_payloads_Permutation :
  forall (A : Type) expected provided (aligned : list A),
    align_cases expected provided aligned ->
    Permutation aligned (List.map fst provided).
Proof.
  intros A expected.
  induction expected as [|c cs IH]; intros provided aligned Halign.
  - unfold align_cases in Halign. simpl in Halign.
    destruct provided; inversion Halign; constructor.
  - unfold align_cases in Halign. simpl in Halign.
    destruct (pick_case_payload c provided) as [[a provided']|] eqn:Hpick;
      try discriminate.
    destruct (align_cases_compute cs provided') as [rest|] eqn:Hrest;
      try discriminate.
    inversion Halign; subst. clear Halign.
    specialize (IH provided' rest Hrest).
    assert (Hperm : Permutation provided ((a, c) :: provided')).
    { eapply pick_case_payload_Permutation. exact Hpick. }
    apply Permutation_map with (f := @fst A case_label) in Hperm.
    simpl in Hperm.
    eapply Permutation_trans.
    + constructor. exact IH.
    + apply Permutation_sym. exact Hperm.
Qed.

(** Membership in the aligned payload list is equivalent to appearing in the
    original labeled argument list with some case label. *)
Lemma align_cases_in_payloads :
  forall (A : Type) expected provided (aligned : list A) a,
    align_cases expected provided aligned ->
    (In a aligned <-> exists c, In (a, c) provided).
Proof.
  intros A expected provided aligned a Halign.
  split.
  - intros Hin.
    pose proof (align_cases_payloads_Permutation A expected provided aligned Halign) as Hp.
    apply (Permutation_in _ Hp) in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [[a' c] [Heq Hin]].
    simpl in Heq. subst. exists c. exact Hin.
  - intros [c Hin].
    pose proof (align_cases_payloads_Permutation A expected provided aligned Halign) as Hp.
    apply (Permutation_in _ (Permutation_sym Hp)).
    apply in_map_iff.
    exists (a, c). split; [reflexivity|exact Hin].
Qed.

(** The variables syntactically bound by a pattern are exactly the
    names in the context produced by [pat_bind].  This is used by
    the substitution lemma to decide whether a variable is captured
    by a pattern in a match branch. *)
Lemma pat_bind_bound_vars_iff :
  forall Sc p tau Gamma x,
    pat_bind Sc p tau Gamma ->
    (In x (pat_bound_vars p) <-> In x (ctx_names Gamma)).
Proof.
  fix IH 6.
  intros Sc p tau Gamma x Hbind.
  destruct Hbind.
  - simpl. tauto.
  - simpl. split; intros Hin.
    + simpl in Hin. destruct Hin as [->|[]]. simpl. auto.
    + simpl in Hin. destruct Hin as [->|[]]. simpl. auto.
  - simpl. tauto.
  - simpl.
    assert (HlenFG : length pats_aligned = length Gammas).
    { symmetry. exact H3. }
    assert (Hcomb :
      In x (List.concat (List.map (fun pg => pat_bound_vars (fst pg)) (combine pats_aligned Gammas))) <->
      In x (ctx_names (List.concat (List.map snd (combine pats_aligned Gammas))))).
    {
      clear H H0 H1 H2 H3.
      induction H4 as [|[p' G'] tp restpg resttp Hpg Hrest IHrest]; simpl.
      - tauto.
      - rewrite in_app_iff.
        unfold ctx_names. simpl. rewrite List.map_app. rewrite in_app_iff.
        rewrite <- (IH Sc (fst (p', G')) (apply_subst bound (fst tp))
          (snd (p', G')) x Hpg).
        rewrite IHrest.
        tauto.
    }
    rewrite <- List.map_map in Hcomb.
    rewrite (map_fst_combine pat val_ctx pats_aligned Gammas HlenFG) in Hcomb.
    rewrite (map_snd_combine pat val_ctx pats_aligned Gammas HlenFG) in Hcomb.
    split; intros Hin.
    + apply in_concat in Hin.
      destruct Hin as [xs [Hinxs Hinx]].
      apply in_map_iff in Hinxs.
      destruct Hinxs as [[p0 c0] [Hxs Hinpats]]. simpl in Hxs. subst xs.
      assert (Hinp0 : In p0 pats_aligned).
      { apply (proj2 (align_cases_in_payloads _ _ _ _ p0 H2)).
        exists c0. exact Hinpats. }
      apply Hcomb.
      apply in_concat.
      exists (pat_bound_vars p0). split.
      * apply in_map_iff. exists p0. split; [reflexivity|].
        exact Hinp0.
      * exact Hinx.
    + apply Hcomb in Hin.
      apply in_concat in Hin.
      destruct Hin as [xs [Hinxs Hinx]].
      apply in_map_iff in Hinxs.
      destruct Hinxs as [p0 [Hxs Hinp0]]. subst xs.
      apply in_concat.
      exists (pat_bound_vars p0). split.
      * apply in_map_iff.
        destruct (proj1 (align_cases_in_payloads _ _ _ _ p0 H2) Hinp0) as [c Hinpc].
        exists (p0, c). split; [reflexivity|exact Hinpc].
      * exact Hinx.
Qed.

(** Any variable reported by [pat_bound_vars] really is bound in the context
    produced by [pat_bind]. *)
Lemma pat_bind_bound_lookup_some :
  forall Sc p tau Gamma x,
    pat_bind Sc p tau Gamma ->
    In x (pat_bound_vars p) ->
    exists tau', ctx_lookup Gamma x = Some tau'.
Proof.
  intros Sc p tau Gamma x Hbind Hin.
  apply ctx_names_lookup_some.
  apply (proj1 (pat_bind_bound_vars_iff Sc p tau Gamma x Hbind)).
  exact Hin.
Qed.

(** If a variable is not syntactically bound by the pattern, the binding
    context produced by [pat_bind] has no entry for it. *)
Lemma pat_bind_not_bound_lookup_none :
  forall Sc p tau Gamma x,
    pat_bind Sc p tau Gamma ->
    ~ In x (pat_bound_vars p) ->
    ctx_lookup Gamma x = None.
Proof.
  intros Sc p tau Gamma x Hbind Hnot.
  destruct (ctx_lookup Gamma x) eqn:Hlookup; auto.
  exfalso. apply Hnot.
  apply (proj2 (pat_bind_bound_vars_iff Sc p tau Gamma x Hbind)).
  eapply ctx_lookup_in_names. exact Hlookup.
Qed.

(** Substitution into branch bodies preserves semantic exhaustiveness because
    the branch patterns themselves are unchanged. *)
Lemma branches_exhaustive_subst :
  forall Se Sf Sc mu tau x v branches,
    branches_exhaustive Se Sf Sc mu tau branches ->
    branches_exhaustive Se Sf Sc mu tau
      (List.map (fun pb =>
        if in_dec String.string_dec x (pat_bound_vars (fst pb))
        then pb
        else (fst pb, subst x v (snd pb))
      ) branches).
Proof.
  intros Se Sf Sc mu tau x v branches Hexhaust w Hsem.
  destruct (Hexhaust w Hsem) as [p [body [rho [Hin Hmatch]]]].
  exists p.
  exists (if in_dec String.string_dec x (pat_bound_vars p)
    then body
    else subst x v body).
  exists rho.
  split.
  - apply in_map_iff.
    exists (p, body). split.
    + simpl.
      destruct (in_dec String.string_dec x (pat_bound_vars p)); reflexivity.
    + exact Hin.
  - exact Hmatch.
Qed.

(** A successful alignment produces exactly one payload for each expected
    case label. *)
Lemma align_cases_length :
  forall (A : Type) expected provided (aligned : list A),
    align_cases expected provided aligned ->
    length aligned = length expected.
Proof.
  intros A expected. induction expected as [|c cs IH]; intros provided aligned H.
  - unfold align_cases in H. simpl in H.
    destruct provided; inversion H. reflexivity.
  - unfold align_cases in H. simpl in H.
    destruct (pick_case_payload c provided) as [[a provided']|] eqn:Epick;
      try discriminate.
    destruct (align_cases_compute cs provided') as [rest|] eqn:Erest;
      try discriminate.
    inversion H; subst. simpl. f_equal.
    eapply IH. exact Erest.
Qed.

(** If the lengths match, pairing aligned payloads with the expected labels
    is already a valid alignment. *)
Lemma align_cases_combine :
  forall (A : Type) expected (aligned : list A),
    length aligned = length expected ->
    align_cases expected (combine aligned expected) aligned.
Proof.
  intros A expected. induction expected as [|c cs IH]; intros aligned Hlen.
  - destruct aligned; unfold align_cases; simpl in *; [reflexivity|discriminate].
  - destruct aligned as [|a aligned']; [discriminate|].
    inversion Hlen.
    unfold align_cases. simpl.
    destruct (case_label_eq_dec c c); [|contradiction].
    rewrite (IH aligned' H0).
    reflexivity.
Qed.

(** Applying a payload map commutes with case-based selection because the
    labels are unchanged. *)
Lemma pick_case_payload_map :
  forall (A B : Type) c (xs : list (A * case_label)) (f : A -> B) a rest,
    pick_case_payload c xs = Some (a, rest) ->
    pick_case_payload c (List.map (fun p => (f (fst p), snd p)) xs) =
      Some (f a, List.map (fun p => (f (fst p), snd p)) rest).
Proof.
  intros A B c xs.
  induction xs as [|[a0 c0] xs IH]; intros f a rest Hpick; simpl in *.
  - discriminate.
  - destruct (case_label_eq_dec c c0).
    + inversion Hpick; subst. reflexivity.
    + destruct (pick_case_payload c xs) as [[a' rest']|] eqn:Htail; try discriminate.
      injection Hpick. intros Hrest Ha. subst a rest.
      rewrite (IH f a' rest' eq_refl). reflexivity.
Qed.

(** Mapping over payload contents preserves alignment: only expressions
    change, never the case structure. *)
Lemma align_cases_map_payload :
  forall (A B : Type) expected (provided : list (A * case_label))
    (aligned : list A) (f : A -> B),
    align_cases expected provided aligned ->
    align_cases expected
      (List.map (fun p => (f (fst p), snd p)) provided)
      (List.map f aligned).
Proof.
  intros A B expected.
  induction expected as [|c cs IH]; intros provided aligned f Halign.
  - unfold align_cases in *. simpl in *.
    destruct provided; inversion Halign; reflexivity.
  - unfold align_cases in *. simpl in *.
    destruct (pick_case_payload c provided) as [[a provided']|] eqn:Hpick;
      try discriminate.
    destruct (align_cases_compute cs provided') as [rest|] eqn:Hrest;
      try discriminate.
    inversion Halign; subst. simpl.
    rewrite (pick_case_payload_map A B c provided f a provided' Hpick).
    rewrite (IH provided' rest f Hrest).
    reflexivity.
Qed.

(** Extracting case labels ignores payload contents, so payload maps leave
    the label sequence unchanged. *)
Lemma extract_cases_map_payload :
  forall (A B : Type) (f : A -> B) (args : list (A * case_label)),
    extract_cases (List.map (fun p => (f (fst p), snd p)) args) =
    extract_cases args.
Proof.
  intros A B f args.
  unfold extract_cases.
  induction args as [|[a c] args IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

(** Pointwise-equal contexts stay pointwise equal after the same single
    binding is added to both. *)
Lemma ctx_lookup_extend_invariant :
  forall G1 G2 x tau y,
    (forall z, ctx_lookup G1 z = ctx_lookup G2 z) ->
    ctx_lookup (ctx_extend G1 x tau) y = ctx_lookup (ctx_extend G2 x tau) y.
Proof.
  intros G1 G2 x tau y Heq.
  unfold ctx_extend. simpl.
  destruct (String.eqb y x); [reflexivity|apply Heq].
Qed.

(** ** Generalized Substitution Lemma *)

(** This is the key substitution lemma for type preservation.  It
    states that substituting a well-typed closed value [v] for
    variable [x] in a well-typed expression [e] preserves its plain
    type.

    The "generalized" qualifier refers to the extra flexibility in
    the source context: rather than requiring [Gamma_src] to be
    literally [ctx_extend Gamma x tau_x], we only require that it
    agrees pointwise on lookups.  This generalization is needed for
    the match-branch case, where the source context has pattern
    bindings prepended.

    The proof uses [fix IH 14] because:
    1. The typing judgment nests [Forall2] sub-derivations inside
       application/constructor rules, which standard [induction]
       cannot recurse into.
    2. The fixpoint must carry all 14 parameters so that recursive
       calls on sub-expressions (including match bodies and bind
       continuations) remain structurally decreasing.

    ** Branch structure **
    - Variable: split on [String.eqb x x0] to determine whether the
      substitution fires or not.
    - Literal: substitution is a no-op.
    - Ascription: recurse on the inner expression.
    - App/App-Partial/Ctor: recurse pointwise over the argument list.
    - Match: for each branch, split on [in_dec] to determine whether
      [x] is captured by the pattern.  If captured, the body keeps
      the old context (via [ctx_lookup_concat_extend_shadowed]);
      if not captured, recurse into the body (via
      [ctx_lookup_concat_extend_fresh]).
    - Let: recurse on the bound expression, then handle the binder with
      the same context-commutation argument used for [EBind].
    - Seq: recurse on both sub-expressions.
    - Bind: split on [String.eqb x x0] for the bound variable. *)
Lemma subst_preserves_typing_gen :
  forall Se Sf Sc Gamma_src Gamma mu x v tau_x kres_v e tau kres,
    has_type Se Sf Sc Gamma_src mu e (tau, kres) ->
    (forall y, ctx_lookup Gamma_src y = ctx_lookup (ctx_extend Gamma x tau_x) y) ->
    has_type Se Sf Sc [] mu v (tau_x, kres_v) ->
    has_plain_type Se Sf Sc Gamma mu (subst x v e) tau.
Proof.
  fix IH 14.
  intros Se Sf Sc Gamma_src Gamma mu x v tau_x kres_v e tau kres Hty Heq Hv.
  remember (tau, kres) as rk eqn:Hrk in Hty.
  destruct Hty; inversion Hrk; subst; clear Hrk.
  - simpl.
    destruct (String.eqb x x0) eqn:Ex.
    + apply String.eqb_eq in Ex. subst x.
      specialize (Heq x0).
      rewrite H in Heq.
      rewrite ctx_lookup_extend_same in Heq.
      inversion Heq; subst.
      exists kres_v.
      replace Gamma with (ctx_concat [] Gamma) by reflexivity.
      eapply has_type_ctx_concat_right; eauto.
    + apply String.eqb_neq in Ex.
      specialize (Heq x0).
      rewrite ctx_lookup_extend_diff in Heq.
      * exists None.
        eapply T_Var.
        rewrite <- Heq. eauto.
      * intro Heq'. apply Ex. symmetry. eauto.
  - simpl. exists None. constructor.
  - simpl.
    destruct (IH _ _ _ _ _ _ _ _ _ _ _ _ _ Hty Heq Hv)
      as [kres' Hsub].
    exists kres'. eapply T_Ascribe; eauto.
  - simpl.
    exists (Some (signature_return_case sigma)).
    eapply T_App with (sigma := sigma) (theta := theta)
      (args_aligned := List.map (subst x v) args_aligned); eauto.
    + eapply align_cases_map_payload; eauto.
    + clear H2.
      induction H3 as [|arg param args' params' Hex Hrest IHrest]; constructor; eauto.
      destruct Hex as [kres_i Harg].
      destruct (IH _ _ _ _ _ _ _ _ _ _ _ _ _ Harg Heq Hv) as [kres_i' Harg'].
      eexists; eauto.
  - simpl.
    exists None.
    eapply T_App_Partial with (sigma := sigma) (theta := theta) (indices := indices); eauto.
    + rewrite length_map. eauto.
    + rewrite extract_cases_map_payload. eauto.
    + clear H2 H3.
      induction H4 as [|arg idx args' idxs' Hhead Hrest IHrest]; constructor; eauto.
      destruct Hhead as [param [kres_i [Hnth Harg]]].
      destruct (IH _ _ _ _ _ _ _ _ _ _ _ _ _ Harg Heq Hv) as [kres_i' Harg'].
      exists param, kres_i'. split; eauto.
  - simpl.
    exists (Some (signature_return_case sigma)).
    eapply T_Ctor with (sigma := sigma) (theta := theta)
      (args_aligned := List.map (subst x v) args_aligned); eauto.
    + eapply align_cases_map_payload; eauto.
    + clear H1.
      induction H2 as [|arg param args' params' Hex Hrest IHrest]; constructor; eauto.
      destruct Hex as [kres_i Harg].
      destruct (IH _ _ _ _ _ _ _ _ _ _ _ _ _ Harg Heq Hv) as [kres_i' Harg'].
      eexists; eauto.
  - simpl.
    destruct (IH _ _ _ _ _ _ _ _ _ _ _ _ _ Hty Heq Hv)
      as [kres_s' Hscrut].
    exists None.
    eapply T_Match with (tau_s := tau_s) (kres_s := kres_s').
    + eauto.
    + eapply branches_exhaustive_subst; eauto.
    + match goal with
      | Hbranches : Forall _ branches |- _ =>
          clear H;
          induction Hbranches as [|[p body] branches' Hbranch Hrest IHrest]
      end.
      * constructor.
      * constructor.
        { destruct Hbranch as [Gamma_p [tau_j [kres_j [Hbind [Hbody Heqtau]]]]].
          simpl.
          destruct (in_dec String.string_dec x (pat_bound_vars p)) as [Hin|Hnin].
          - eauto_split.
            eapply has_type_ctx_invariant.
            + eauto.
            + intros y.
              lazymatch type of Hbody with
              | has_type _ _ _ (ctx_concat Gamma_p ?Gamma_src0) _ _ _ =>
                  rewrite (ctx_lookup_concat_invariant Gamma_p Gamma_src0
                    (ctx_extend Gamma x tau_x) y Heq)
              end.
              destruct (pat_bind_bound_lookup_some Sc p tau_s Gamma_p x Hbind Hin)
                as [tau_p Hlookup].
              eapply ctx_lookup_concat_extend_shadowed; eauto.
          - lazymatch type of Hbody with
            | has_type _ _ _ (ctx_concat Gamma_p ?Gamma_src0) _ _ _ =>
                destruct (IH Se Sf Sc (ctx_concat Gamma_p Gamma_src0) (ctx_concat Gamma_p Gamma)
                  mu x v tau_x kres_v body tau_j kres_j Hbody) as [kres_j' Hbody_sub]
            end.
            { intro y.
              lazymatch type of Hbody with
              | has_type _ _ _ (ctx_concat Gamma_p ?Gamma_src0) _ _ _ =>
                  rewrite (ctx_lookup_concat_invariant Gamma_p Gamma_src0
                    (ctx_extend Gamma x tau_x) y Heq)
              end.
              eapply ctx_lookup_concat_extend_fresh.
              eapply pat_bind_not_bound_lookup_none; eauto. }
            { eauto. }
            eauto_split. }
        { exact IHrest. }
  - simpl.
    destruct (IH _ _ _ _ _ _ _ _ _ _ _ _ _ Hty1 Heq Hv)
      as [kres1' H1'].
    destruct (String.eqb x x0) eqn:Ex.
    + apply String.eqb_eq in Ex. subst x.
      assert (Hbody' :
        has_type Se Sf Sc (ctx_extend Gamma x0 tau1) mu e2 (tau, kres)).
      { eapply has_type_ctx_invariant.
        - eauto.
        - intros y.
          rewrite (ctx_lookup_extend_invariant Gamma0 (ctx_extend Gamma x0 tau_x)
            x0 tau1 y Heq).
          apply ctx_lookup_extend_shadowed.
      }
      exists kres. eapply T_Let; eauto.
    + apply String.eqb_neq in Ex.
      destruct (IH Se Sf Sc (ctx_extend Gamma0 x0 tau1) (ctx_extend Gamma x0 tau1)
        mu x v tau_x kres_v e2 tau kres Hty2) as [kres2' H2'].
      { intro y.
        rewrite (ctx_lookup_extend_invariant Gamma0 (ctx_extend Gamma x tau_x)
          x0 tau1 y Heq).
        symmetry. apply ctx_lookup_extend_commute.
        intro Heq'. apply Ex. symmetry. eauto. }
      { eauto. }
      exists kres2'. eapply T_Let; eauto.
  - simpl.
    destruct (IH _ _ _ _ _ _ _ _ _ _ _ _ _ Hty1 Heq Hv)
      as [kres1' H1'].
    destruct (IH _ _ _ _ _ _ _ _ _ _ _ _ _ Hty2 Heq Hv)
      as [kres2' H2'].
    exists kres2'. eapply T_Seq; eauto.
  - simpl.
    destruct (IH _ _ _ _ _ _ _ _ _ _ _ _ _ Hty1 Heq Hv)
      as [kres1' H1'].
    destruct (String.eqb x x0) eqn:Ex.
    + apply String.eqb_eq in Ex. subst x.
      assert (Hbody' :
        has_type Se Sf Sc (ctx_extend Gamma x0 tau1) Eff e2 (tau, kres)).
      { eapply has_type_ctx_invariant.
        - eauto.
        - intros y.
          rewrite (ctx_lookup_extend_invariant Gamma0 (ctx_extend Gamma x0 tau_x)
            x0 tau1 y Heq).
          apply ctx_lookup_extend_shadowed.
      }
      exists kres. eapply T_Bind; eauto.
    + apply String.eqb_neq in Ex.
      destruct (IH Se Sf Sc (ctx_extend Gamma0 x0 tau1) (ctx_extend Gamma x0 tau1)
        Eff x v tau_x kres_v e2 tau kres Hty2) as [kres2' H2'].
      { intro y.
        rewrite (ctx_lookup_extend_invariant Gamma0 (ctx_extend Gamma x tau_x)
          x0 tau1 y Heq).
        symmetry. apply ctx_lookup_extend_commute.
        intro Heq'. apply Ex. symmetry. eauto. }
      { eauto. }
      exists kres2'. eapply T_Bind; eauto.
Qed.

(** Standard substitution lemma: a specialization of
    [subst_preserves_typing_gen] where [Gamma_src] is literally
    [ctx_extend Gamma x tau_x]. *)
Lemma subst_preserves_typing :
  forall Se Sf Sc Gamma mu x v tau_x kres_v e tau kres,
    has_type Se Sf Sc (ctx_extend Gamma x tau_x) mu e (tau, kres) ->
    has_type Se Sf Sc [] mu v (tau_x, kres_v) ->
    has_plain_type Se Sf Sc Gamma mu (subst x v e) tau.
Proof.
  intros Se Sf Sc Gamma mu x v tau_x kres_v e tau kres Hty Hv.
  eapply subst_preserves_typing_gen; eauto.
Qed.

(** Concatenating two well-typed substitution environments yields a
    well-typed environment for the concatenated context. *)
Lemma subst_env_typed_app :
  forall Se Sf Sc mu rho1 rho2 Gamma1 Gamma2,
    subst_env_typed Se Sf Sc mu rho1 Gamma1 ->
    subst_env_typed Se Sf Sc mu rho2 Gamma2 ->
    subst_env_typed Se Sf Sc mu (rho1 ++ rho2) (ctx_concat Gamma1 Gamma2).
Proof.
  intros Se Sf Sc mu rho1 rho2 Gamma1 Gamma2 Henv1 Henv2.
  induction Henv1.
  - simpl. exact Henv2.
  - simpl. econstructor.
    + exact H.
    + exact IHHenv1.
Qed.

(** Applying a whole well-typed substitution environment to a well-typed
    expression preserves the plain type.  This is the iterated form of
    the single-variable [subst_preserves_typing]. *)
Lemma subst_env_preserves_typing :
  forall Se Sf Sc mu rho Gamma e tau kres,
    subst_env_typed Se Sf Sc mu rho Gamma ->
    has_type Se Sf Sc Gamma mu e (tau, kres) ->
    has_plain_type Se Sf Sc [] mu (subst_env rho e) tau.
Proof.
  intros Se Sf Sc mu rho Gamma e tau kres Henv Hty.
  revert e tau kres Hty.
  induction Henv; intros e tau0 kres0 Hty.
  - simpl. exists kres0. exact Hty.
  - simpl.
    destruct (subst_preserves_typing Se Sf Sc Gamma mu x v tau kres e tau0 kres0 Hty H)
      as [kres1 Hsub].
    exact (IHHenv _ _ _ Hsub).
Qed.

(** Convert [Forall2] with existentially-quantified [kres] into
    [Forall2] with [has_plain_type].  These two representations
    carry the same information; we move between them as needed. *)
Lemma Forall2_typed_params_plain :
  forall Se Sf Sc Gamma mu bound (args : list expr) (params : list signature_param),
    Forall2 (fun arg param =>
      exists kres_i,
        has_type Se Sf Sc Gamma mu arg
          (apply_subst bound (fst param), kres_i))
      args params ->
    Forall2 (fun arg param =>
      has_plain_type Se Sf Sc Gamma mu arg
        (apply_subst bound (fst param)))
      args params.
Proof.
  intros Se Sf Sc Gamma mu bound args params Htyped.
  induction Htyped as [|arg param args' params' [kres_i Harg] Hrest IH].
  - constructor.
  - constructor; [exists kres_i; exact Harg | exact IH].
Qed.

(** [apply_subst [] t = t] lets us erase the empty substitution
    from a [Forall2] of plain-typed arguments. *)
Lemma Forall2_plain_subst_nil :
  forall Se Sf Sc Gamma mu (args : list expr) (params : list signature_param),
    Forall2 (fun arg param =>
      has_plain_type Se Sf Sc Gamma mu arg (apply_subst [] (fst param)))
      args params ->
    Forall2 (fun arg param =>
      has_plain_type Se Sf Sc Gamma mu arg (fst param))
      args params.
Proof.
  intros Se Sf Sc Gamma mu args params Hplain.
  induction Hplain as [|arg param args' params' Harg Hrest IHrest];
    constructor; auto.
  rewrite apply_subst_nil in Harg; exact Harg.
Qed.

(** When [align_cases] succeeds and [canonical_args] also succeeds,
    the canonical form is just [combine args_aligned expected]. *)
Lemma canonical_args_as_combine :
  forall expected args args_aligned args',
    align_cases expected args args_aligned ->
    canonical_args expected args = Some args' ->
    args' = combine args_aligned expected.
Proof.
  intros expected args args_aligned args' Halign Hcanon.
  unfold canonical_args in Hcanon; rewrite Halign in Hcanon; congruence.
Qed.

(** Canonicalization only reorders labeled arguments, so the payloads
    extracted from a canonical form are the aligned payload list. *)
Lemma canonical_args_payload_eq :
  forall expected args args_aligned args',
    align_cases expected args args_aligned ->
    canonical_args expected args = Some args' ->
    List.map fst args' = args_aligned.
Proof.
  intros expected args args_aligned args' Halign Hcanon.
  rewrite (canonical_args_as_combine _ _ _ _ Halign Hcanon).
  apply map_fst_combine.
  eapply align_cases_length. exact Halign.
Qed.

(** If a labeled argument list is already canonical, taking its payloads
    witnesses a successful alignment. *)
Lemma canonical_args_payloads :
  forall expected args,
    canonical_args expected args = Some args ->
    align_cases expected args (List.map fst args).
Proof.
  intros expected args Hcanon.
  unfold canonical_args in Hcanon.
  destruct (align_cases_compute expected args) as [aligned|] eqn:Halign; try discriminate.
  inversion Hcanon; subst.
  rewrite map_fst_combine.
  - apply align_cases_combine.
    eapply align_cases_length. exact Halign.
  - eapply align_cases_length. exact Halign.
Qed.

(** Any successful canonicalization exposes an aligned payload list when we
    forget the labels of the canonical output. *)
Lemma canonical_args_payloads_gen :
  forall expected args args',
    canonical_args expected args = Some args' ->
    align_cases expected args (List.map fst args').
Proof.
  intros expected args args' Hcanon.
  unfold canonical_args in Hcanon.
  destruct (align_cases_compute expected args) as [aligned|] eqn:Halign; try discriminate.
  inversion Hcanon; subst.
  rewrite map_fst_combine.
  - exact Halign.
  - eapply align_cases_length. exact Halign.
Qed.

(** Canonicalizing an argument list already built in canonical order does
    nothing. *)
Lemma canonical_args_refl :
  forall expected aligned,
    length aligned = length expected ->
    canonical_args expected (combine aligned expected) = Some (combine aligned expected).
Proof.
  intros expected aligned Hlen.
  unfold canonical_args.
  rewrite (align_cases_combine _ _ _ Hlen).
  reflexivity.
Qed.

(** If each payload is a value, then labeling them preserves the value
    predicate on labeled arguments. *)
Lemma value_payloads_combine :
  forall Se Sf F Sc mu payloads labels,
    value_payloads F Sc (Se:=Se) (Sf:=Sf) (mu:=mu) payloads ->
    length payloads = length labels ->
    value_labeled_args F Sc (Se:=Se) (Sf:=Sf) (mu:=mu) (combine payloads labels).
Proof.
  intros Se Sf F Sc mu payloads.
  induction payloads as [|v vs IH]; intros labels Hvals Hlen.
  - destruct labels; simpl in *; [constructor|discriminate].
  - destruct labels as [|c cs]; simpl in *; [discriminate|].
    inversion Hvals as [|v' vs' Hv Hvals']; subst.
    inversion Hlen; subst.
    constructor.
    + exact Hv.
    + apply IH; assumption.
Qed.

(** Forgetting the labels of a value-labeled argument list preserves the
    payload-value property. *)
Lemma value_labeled_args_payloads :
  forall Se Sf F Sc mu args,
    value_labeled_args F Sc (Se:=Se) (Sf:=Sf) (mu:=mu) args ->
    value_payloads F Sc (Se:=Se) (Sf:=Sf) (mu:=mu) (List.map fst args).
Proof.
  intros Se Sf F Sc mu args Hvals.
  induction Hvals as [|[arg c] rest Hv Hrest IH]; simpl.
  - constructor.
  - constructor; assumption.
Qed.

(** Labeling a payload list preserves [Forall2]-structured semantic-value
    evidence. *)
Lemma semantic_value_payloads_combine :
  forall Se Sf Sc mu payloads labels params,
    Forall2 (fun arg param =>
      semantic_value Se Sf Sc mu (fst param) arg)
      payloads params ->
    length payloads = length labels ->
    Forall2 (fun (arg : expr * case_label) (param : signature_param) =>
      semantic_value Se Sf Sc mu (fst param) (fst arg))
      (combine payloads labels) params.
Proof.
  intros Se Sf Sc mu payloads labels params Hsemantic.
  revert labels.
  induction Hsemantic as [|arg param payloads' params' Harg Hrest IH];
    intros labels Hlen.
  - destruct labels; simpl in Hlen; [constructor|discriminate].
  - destruct labels as [|label labels']; simpl in Hlen; [discriminate|].
    inversion Hlen; subst.
    constructor; [exact Harg|].
    eapply IH; eauto.
Qed.

(** Rewriting semantic-value premises under the empty substitution is
    definitionally harmless but convenient when exhaustiveness is phrased in
    terms of [apply_subst []]. *)
Lemma Forall2_semantic_subst_nil :
  forall Se Sf Sc mu args params,
    Forall2 (fun (arg : expr * case_label) (param : signature_param) =>
      semantic_value Se Sf Sc mu (fst param) (fst arg))
      args params ->
    Forall2 (fun (arg : expr * case_label) (param : signature_param) =>
      semantic_value Se Sf Sc mu (apply_subst [] (fst param)) (fst arg))
      args params.
Proof.
  intros Se Sf Sc mu args params Hsemantic.
  induction Hsemantic as [|arg param args' params' Harg Hrest IH]; constructor.
  - simpl. rewrite apply_subst_nil. exact Harg.
  - exact IH.
Qed.

(** A total alignment uses every provided argument exactly once, so provided
    and expected arities must match. *)
Lemma align_cases_provided_length :
  forall (A : Type) expected (provided : list (A * case_label)) aligned,
    align_cases expected provided aligned ->
    length provided = length expected.
Proof.
  intros A expected provided aligned Halign.
  pose proof (align_cases_payloads_Permutation A expected provided aligned Halign) as Hperm.
  apply Permutation_length in Hperm.
  rewrite length_map in Hperm.
  rewrite <- Hperm.
  eapply align_cases_length. exact Halign.
Qed.

(** Canonicalization succeeds only for fully matched calls, hence the
    original argument list has full signature arity. *)
Lemma canonical_args_length :
  forall expected args args',
    canonical_args expected args = Some args' ->
    length args = length expected.
Proof.
  intros expected args args' Hcanon.
  unfold canonical_args in Hcanon.
  destruct (align_cases_compute expected args) as [aligned|] eqn:Halign; try discriminate.
  inversion Hcanon; subst.
  eapply align_cases_provided_length. exact Halign.
Qed.

(** Same as [Forall2_typed_params_plain] -- present for backwards
    compatibility with call sites that use this name. *)
Lemma typed_args_plain :
  forall Se Sf Sc Gamma mu bound (args : list expr) (params : list signature_param),
    Forall2 (fun arg param =>
      exists kres_i,
        has_type Se Sf Sc Gamma mu arg
          (apply_subst bound (fst param), kres_i))
      args params ->
    Forall2 (fun arg param =>
      has_plain_type Se Sf Sc Gamma mu arg (apply_subst bound (fst param)))
      args params.
Proof.
  intros; eapply Forall2_typed_params_plain; eauto.
Qed.

(** Regular constructor signatures determine their type-variable
    instantiations from the instantiated result type. *)
Lemma regular_constructor_subst_unique :
  forall Sc C sigma (theta1 theta2 : list (tyvar_name * ty)) tau,
    ctor_ctx_regular Sc ->
    Sc C = Some sigma ->
    length theta1 = length (signature_tvars sigma) ->
    length theta2 = length (signature_tvars sigma) ->
    apply_subst (combine (signature_tvars sigma) (List.map snd theta1))
      (signature_return_ty sigma) = tau ->
    apply_subst (combine (signature_tvars sigma) (List.map snd theta2))
      (signature_return_ty sigma) = tau ->
    List.map snd theta1 = List.map snd theta2.
Proof.
  intros Sc C sigma theta1 theta2 tau Hregular Hsig Hlen1 Hlen2 Hret1 Hret2.
  destruct (Hregular C sigma Hsig) as
    [D [result_cases [ret_args [Hnodup_tvars [Hnodup_cases [Hlen_cases [Hshape Halign]]]]]]].
  rewrite Hshape in Hret1, Hret2.
  simpl in Hret1, Hret2.
  assert (Hprovided_eq :
    List.map (fun p =>
      (apply_subst (combine (signature_tvars sigma) (List.map snd theta1)) (fst p), snd p))
      ret_args =
    List.map (fun p =>
      (apply_subst (combine (signature_tvars sigma) (List.map snd theta2)) (fst p), snd p))
      ret_args).
  {
    rewrite <- Hret1 in Hret2.
    inversion Hret2; reflexivity.
  }
  pose proof (align_cases_map_payload ty ty result_cases ret_args
    (List.map TyVar (signature_tvars sigma))
    (apply_subst (combine (signature_tvars sigma) (List.map snd theta1))) Halign)
    as Halign1.
  pose proof (align_cases_map_payload ty ty result_cases ret_args
    (List.map TyVar (signature_tvars sigma))
    (apply_subst (combine (signature_tvars sigma) (List.map snd theta2))) Halign)
    as Halign2.
  rewrite <- Hprovided_eq in Halign2.
  pose proof (align_cases_deterministic _ result_cases
    (List.map (fun p =>
      (apply_subst (combine (signature_tvars sigma) (List.map snd theta1)) (fst p), snd p))
      ret_args)
    (List.map
      (apply_subst (combine (signature_tvars sigma) (List.map snd theta1)))
      (List.map TyVar (signature_tvars sigma)))
    (List.map
      (apply_subst (combine (signature_tvars sigma) (List.map snd theta2)))
      (List.map TyVar (signature_tvars sigma)))
    Halign1 Halign2) as Haligned_eq.
  rewrite (map_apply_subst_combine_tyvars
    (signature_tvars sigma) (List.map snd theta1) Hnodup_tvars) in Haligned_eq.
  2:{ rewrite length_map. exact Hlen1. }
  rewrite (map_apply_subst_combine_tyvars
    (signature_tvars sigma) (List.map snd theta2) Hnodup_tvars) in Haligned_eq.
  2:{ rewrite length_map. exact Hlen2. }
  exact Haligned_eq.
Qed.

(** As a corollary, regular constructor result equality determines all
    parameter instantiations. *)
Lemma regular_constructor_param_subst_eq :
  forall Sc C sigma (theta1 theta2 : list (tyvar_name * ty)) tau t,
    ctor_ctx_regular Sc ->
    Sc C = Some sigma ->
    length theta1 = length (signature_tvars sigma) ->
    length theta2 = length (signature_tvars sigma) ->
    apply_subst (combine (signature_tvars sigma) (List.map snd theta1))
      (signature_return_ty sigma) = tau ->
    apply_subst (combine (signature_tvars sigma) (List.map snd theta2))
      (signature_return_ty sigma) = tau ->
    apply_subst (combine (signature_tvars sigma) (List.map snd theta1)) t =
    apply_subst (combine (signature_tvars sigma) (List.map snd theta2)) t.
Proof.
  intros Sc C sigma theta1 theta2 tau t Hregular Hsig Hlen1 Hlen2 Hret1 Hret2.
  pose proof (regular_constructor_subst_unique
    Sc C sigma theta1 theta2 tau Hregular Hsig Hlen1 Hlen2 Hret1 Hret2) as Htys.
  now rewrite Htys.
Qed.

(** Inverting constructor pattern binding exposes exactly the data that the
    runtime constructor case needs:
    - the type-variable instantiation [theta] chosen by the pattern,
    - the aligned subpattern list [pats_aligned],
    - the per-subpattern binding contexts [Gammas],
    - and the fact that the overall binding environment is
      [List.concat Gammas].

    [pat_match_mutual_typed] uses this lemma as the static half of the
    constructor case: after runtime matching selects a constructor branch,
    this lemma recovers the binding obligations for each aligned
    subpattern without depending on Rocq's inversion-generated names. *)
Lemma pat_bind_ctor_cases :
  forall Sc C sigma pats tau Gamma,
    Sc C = Some sigma ->
    pat_bind Sc (PCtorPat C pats) tau Gamma ->
    exists (theta : list (tyvar_name * ty)) (pats_aligned : list pat)
      (Gammas : list val_ctx),
      length theta = length (signature_tvars sigma) /\
      apply_subst (combine (signature_tvars sigma) (List.map snd theta))
        (signature_return_ty sigma) = tau /\
      align_cases (extract_cases (signature_params sigma)) pats pats_aligned /\
      length Gammas = length pats_aligned /\
      Forall2 (fun (pg : pat * val_ctx) (tp : signature_param) =>
        pat_bind Sc (fst pg)
          (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (fst tp))
          (snd pg))
        (combine pats_aligned Gammas) (signature_params sigma) /\
      Gamma = List.concat Gammas.
Proof.
  intros Sc C sigma pats tau Gamma Hsig Hbind.
  inversion Hbind; subst.
  match goal with
  | Hsig_bind : Sc C = Some ?sigma_bind |- _ =>
      pose proof (ctor_ctx_deterministic Sc C sigma_bind sigma Hsig_bind Hsig)
        as -> 
  end.
  do 3 eexists.
  repeat split; eauto.
Qed.

(** Inverting plain typing for a constructor value exposes the dynamic facts
    needed by constructor-pattern typing:
    - the type-variable instantiation [theta] used by the constructor,
    - the aligned payload list [args_aligned],
    - the plain typing of each payload against the instantiated signature
      parameters,
    - and the resulting instantiated return type.

    This is the typing-side counterpart of [pat_bind_ctor_cases].  The proof
    first inverts [T_Ctor], then converts the existentially quantified
    payload typing premises into plain typing via [typed_args_plain]. *)
Lemma plain_typed_ctor_cases :
  forall Se Sf Sc mu C sigma args tau,
    Sc C = Some sigma ->
    has_plain_type Se Sf Sc [] mu (ECtor C args) tau ->
    exists (theta : list (tyvar_name * ty)) (args_aligned : list expr),
      length theta = length (signature_tvars sigma) /\
      align_cases (extract_cases (signature_params sigma)) args args_aligned /\
      Forall2 (fun arg param =>
        has_plain_type Se Sf Sc [] mu arg
          (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (fst param)))
        args_aligned (signature_params sigma) /\
      apply_subst (combine (signature_tvars sigma) (List.map snd theta))
        (signature_return_ty sigma) = tau.
Proof.
  intros Se Sf Sc mu C sigma args tau Hsig Hplain.
  destruct Hplain as [kres Hty].
  inversion Hty; subst.
  match goal with
  | bound := combine (signature_tvars ?sigma_ty) (List.map snd ?theta),
    Hsig_ty : Sc C = Some ?sigma_ty,
    Halign : align_cases (extract_cases (signature_params ?sigma_ty)) args ?args_aligned,
    Htyped_args : Forall2
      (fun arg param =>
        exists kres_i,
          has_type Se Sf Sc [] mu arg (apply_subst bound (fst param), kres_i))
      args_aligned
      (signature_params ?sigma_ty) |- _ =>
      pose proof (ctor_ctx_deterministic Sc C sigma_ty sigma Hsig_ty Hsig) as ->;
      pose proof (typed_args_plain Se Sf Sc [] mu
        bound
        args_aligned (signature_params sigma) Htyped_args) as Hplain_args
  end.
  do 2 eexists.
  repeat split; eauto.
Qed.

(** Pattern matching and aligned pattern-list matching preserve typing of the
    substitution environments they produce.  Proving the two statements
    together avoids rebuilding the list-level recursion inside the
    constructor case of [pat_match_typed].

    The constructor-pattern branch is the interesting one: it combines
    [pat_bind_ctor_cases] with [plain_typed_ctor_cases], uses constructor
    regularity to identify the static and dynamic type substitutions, and
    then rewrites the runtime payload list into the aligned list expected by
    the recursive hypothesis. *)
Lemma pat_match_mutual_typed :
  forall Se Sf Sc mu,
    ctor_ctx_regular Sc ->
    (forall p v rho,
      pat_match Sc p v rho ->
      forall tau Gamma_p,
        pat_bind Sc p tau Gamma_p ->
        has_plain_type Se Sf Sc [] mu v tau ->
        subst_env_typed Se Sf Sc mu rho Gamma_p) /\
    (forall pats vals rho,
      pats_match Sc pats vals rho ->
      forall bound Gammas params,
        length Gammas = length pats ->
        Forall2 (fun (pg : pat * val_ctx) (tp : signature_param) =>
          pat_bind Sc (fst pg) (apply_subst bound (fst tp)) (snd pg))
          (combine pats Gammas) params ->
        Forall2 (fun v tp =>
          has_plain_type Se Sf Sc [] mu v (apply_subst bound (fst tp)))
          vals params ->
        subst_env_typed Se Sf Sc mu rho (List.concat Gammas)).
Proof.
  intros Se Sf Sc mu Hregular.
  refine (pat_match_mutind Sc
    (fun p v rho _ =>
      forall tau Gamma_p,
        pat_bind Sc p tau Gamma_p ->
        has_plain_type Se Sf Sc [] mu v tau ->
        subst_env_typed Se Sf Sc mu rho Gamma_p)
    (fun pats vals rho _ =>
      forall bound Gammas params,
        length Gammas = length pats ->
        Forall2 (fun (pg : pat * val_ctx) (tp : signature_param) =>
          pat_bind Sc (fst pg) (apply_subst bound (fst tp)) (snd pg))
          (combine pats Gammas) params ->
        Forall2 (fun v tp =>
          has_plain_type Se Sf Sc [] mu v (apply_subst bound (fst tp)))
          vals params ->
        subst_env_typed Se Sf Sc mu rho (List.concat Gammas))
    _ _ _ _ _ _).
  - intros v tau Gamma_p Hbind Hv.
    apply pat_bind_wild_nil in Hbind. subst. constructor.
  - intros x v tau Gamma_p Hbind Hv.
    apply pat_bind_var_singleton in Hbind. subst.
    destruct Hv as [kres Hty].
    econstructor; [exact Hty|constructor].
  - intros c tau Gamma_p Hbind Hv.
    apply pat_bind_literal_nil in Hbind. subst. constructor.
  (** The constructor case is where the new inversion lemmas earn their
      keep.  We recover the static binding structure from
      [pat_bind_ctor_cases], the dynamic payload typing from
      [plain_typed_ctor_cases], show that both sides chose the same
      substitution by regularity, and then recurse on the aligned
      subpatterns. *)
  - intros C sigma pats pats_aligned args rho Hsig Hcanon Halign Hmatches IHpats
      tau Gamma_p Hbind Hv.
    destruct (pat_bind_ctor_cases Sc C sigma pats tau Gamma_p Hsig Hbind) as
      [theta_bind [pats_aligned_bind [Gammas
        [Hlen_bind [Hret_bind [Halign_bind [Hlen_Gammas [Hbinds HGamma]]]]]]]].
    destruct (plain_typed_ctor_cases Se Sf Sc mu C sigma args tau Hsig Hv) as
      [theta_ty [args_aligned
        [Hlen_ty [Halign_args [Hargs_plain Hret_ty]]]]].
    subst Gamma_p.
    pose proof (align_cases_deterministic pat
      (extract_cases (signature_params sigma)) pats pats_aligned_bind pats_aligned
      Halign_bind Halign) as Hpats_eq.
    subst pats_aligned_bind.
    pose proof (regular_constructor_subst_unique
      Sc C sigma theta_bind theta_ty tau
      Hregular Hsig Hlen_bind Hlen_ty Hret_bind Hret_ty) as Htheta_eq.
    pose proof (canonical_args_payload_eq
      (extract_cases (signature_params sigma)) args args_aligned args
      Halign_args Hcanon) as Hpayloads_eq.
    rewrite <- Hpayloads_eq in Hargs_plain.
    rewrite <- Htheta_eq in Hargs_plain.
    eapply IHpats; eauto.
  - intros bound Gammas params Hlen Hbinds Hvals.
    destruct Gammas; simpl in Hlen; [|discriminate].
    inversion Hbinds; inversion Hvals; constructor.
  - intros p v ps vs rho_p rho_ps Hmatch IHmatch Hmatches IHmatches
      bound Gammas params Hlen Hbinds Hvals.
    destruct Gammas as [|G Gs]; [discriminate|].
    inversion Hlen; subst.
    inversion Hbinds as [|pg0 param0 restpg resttp Hbind_head Hbind_tail]; subst.
    inversion Hvals as [|v0 param1 vs0 params0 Hv_head Hv_tail]; subst.
    apply subst_env_typed_app.
    + eapply IHmatch; eauto.
    + eapply IHmatches; eauto.
Qed.

(** Matching a typed closed value against a well-bound pattern produces a
    well-typed substitution environment.  Constructor patterns are the only
    interesting case: regularity of [Sc] is what lets us recover the payload
    types from the constructor result type. *)
Lemma pat_match_typed :
  forall Se Sf Sc mu p v rho tau Gamma_p,
    ctor_ctx_regular Sc ->
    pat_match Sc p v rho ->
    pat_bind Sc p tau Gamma_p ->
    has_plain_type Se Sf Sc [] mu v tau ->
    subst_env_typed Se Sf Sc mu rho Gamma_p.
Proof.
  intros Se Sf Sc mu p v rho tau Gamma_p Hregular Hmatch Hbind Hv.
  exact (proj1 (pat_match_mutual_typed Se Sf Sc mu Hregular)
    p v rho Hmatch tau Gamma_p Hbind Hv).
Qed.

(** The list-level version of [pat_match_typed], used for function-clause
    beta-reduction once the clause patterns have already been aligned. *)
Lemma pats_match_typed :
  forall Se Sf Sc mu pats vals rho Gammas params,
    ctor_ctx_regular Sc ->
    pats_match Sc pats vals rho ->
    length Gammas = length pats ->
    Forall2 (fun (pg : pat * val_ctx) (tp : signature_param) =>
      pat_bind Sc (fst pg) (fst tp) (snd pg))
      (combine pats Gammas) params ->
    Forall2 (fun v tp =>
      has_plain_type Se Sf Sc [] mu v (fst tp))
      vals params ->
    subst_env_typed Se Sf Sc mu rho (List.concat Gammas).
Proof.
  intros Se Sf Sc mu pats vals rho Gammas params Hregular Hmatches Hlen Hbinds Hvals.
  assert (Hbinds_nil :
    Forall2 (fun (pg : pat * val_ctx) (tp : signature_param) =>
      pat_bind Sc (fst pg) (apply_subst [] (fst tp)) (snd pg))
      (combine pats Gammas) params).
  {
    clear Hvals.
    induction Hbinds as [|pg tp pgs tps Hbind Hrest IH].
    - constructor.
    - constructor.
      + simpl. rewrite apply_subst_nil. exact Hbind.
      + exact IH.
  }
  assert (Hvals_nil :
    Forall2 (fun v tp =>
      has_plain_type Se Sf Sc [] mu v (apply_subst [] (fst tp)))
      vals params).
  {
    clear Hbinds Hmatches Hlen Hbinds_nil.
    induction Hvals as [|v tp vs tps Hv Hrest IH].
    - constructor.
    - constructor.
      + simpl. rewrite apply_subst_nil. exact Hv.
      + exact IH.
  }
  exact (proj2 (pat_match_mutual_typed Se Sf Sc mu Hregular)
    pats vals rho Hmatches [] Gammas params Hlen Hbinds_nil Hvals_nil).
Qed.

(** Stepping a payload list preserves the [Forall2]-structured evidence that
    each payload matches its parameter type. *)
Lemma step_exprs_preserves_typed_params :
  forall Se Sf Sc F mu bound (es es' : list expr) (params : list signature_param),
    (forall e0 e1 tau0 kres0,
      has_type Se Sf Sc [] mu e0 (tau0, kres0) ->
      step F Sc (Se:=Se) (Sf:=Sf) (mu:=mu) e0 e1 ->
      has_plain_type Se Sf Sc [] mu e1 tau0) ->
    step_exprs F Sc (Se:=Se) (Sf:=Sf) (mu:=mu) es es' ->
    Forall2 (fun arg param =>
      exists kres_i,
        has_type Se Sf Sc [] mu arg
          (apply_subst bound (fst param), kres_i))
      es params ->
    Forall2 (fun arg param =>
      exists kres_i,
        has_type Se Sf Sc [] mu arg
          (apply_subst bound (fst param), kres_i))
      es' params.
Proof.
  intros Se Sf Sc F mu bound es es' params Hpres Hsteps.
  revert params.
  induction Hsteps; intros params Htyped.
  - inversion Htyped as [|arg_hd param_hd es0 params0 Hhead Htail]; subst.
    constructor.
    + destruct Hhead as [kres_i Harg].
      destruct (Hpres _ _ _ _ Harg H) as [kres' Hsub].
      exists kres'. exact Hsub.
    + exact Htail.
  - inversion Htyped as [|arg_hd param_hd es0 params0 Hhead Htail]; subst.
    constructor.
    + exact Hhead.
    + eapply IHHsteps. exact Htail.
Qed.

(** Stepping labeled arguments preserves the typing evidence attached to the
    parameter indices they already matched. *)
Lemma step_args_preserves_typed_indices :
  forall Se Sf Sc F mu bound args args' sigma indices,
    (forall e0 e1 tau0 kres0,
      has_type Se Sf Sc [] mu e0 (tau0, kres0) ->
      step F Sc (Se:=Se) (Sf:=Sf) (mu:=mu) e0 e1 ->
      has_plain_type Se Sf Sc [] mu e1 tau0) ->
    step_args F Sc (Se:=Se) (Sf:=Sf) (mu:=mu) args args' ->
    Forall2 (fun arg idx =>
      exists param kres_i,
        nth_error (signature_params sigma) idx = Some param /\
        has_type Se Sf Sc [] mu (fst arg)
          (apply_subst bound (fst param), kres_i))
      args indices ->
    Forall2 (fun arg idx =>
      exists param kres_i,
        nth_error (signature_params sigma) idx = Some param /\
        has_type Se Sf Sc [] mu (fst arg)
          (apply_subst bound (fst param), kres_i))
      args' indices.
Proof.
  intros Se Sf Sc F mu bound args args' sigma indices Hpres Hsteps.
  revert indices.
  induction Hsteps; intros indices Htyped.
  - inversion Htyped as [|[arg_hd c_hd] idx_hd args0 idxs0 Hhead Htail]; subst.
    constructor.
    + destruct Hhead as [param [kres_i [Hnth Harg]]].
      destruct (Hpres _ _ _ _ Harg H) as [kres' Hsub].
      exists param, kres'. split; [exact Hnth | exact Hsub].
    + exact Htail.
  - inversion Htyped as [|[arg_hd c_hd] idx_hd args0 idxs0 Hhead Htail]; subst.
    constructor.
    + exact Hhead.
    + eapply IHHsteps. exact Htail.
Qed.

(** Stepping an argument does not change the case labels.  This is
    because stepping only changes payloads, not the label annotation. *)
Lemma step_args_extract_cases :
  forall Se Sf F Sc mu args args',
    step_args F Sc (Se:=Se) (Sf:=Sf) (mu:=mu) args args' ->
    extract_cases args = extract_cases args'.
Proof.
  intros Se Sf F Sc mu args args' Hsteps.
  induction Hsteps; simpl; [reflexivity | f_equal; assumption].
Qed.

(** When the signature is monomorphic, the type-variable binding is
    empty regardless of [theta]. *)
Lemma monomorphic_bound_nil :
  forall sigma (theta : list (tyvar_name * ty)),
    monomorphic_signature sigma ->
    combine (signature_tvars sigma) (List.map snd theta) = [].
Proof.
  intros sigma theta Hmono; unfold monomorphic_signature in Hmono.
  rewrite Hmono; reflexivity.
Qed.

(** A typed full application over a monomorphic signature is a full overload
    candidate for runtime resolution. *)
Lemma typed_full_app_candidate_mono :
  forall Se Sf Sc mu sigma (theta : list (tyvar_name * ty))
    args args_aligned,
    monomorphic_signature sigma ->
    length theta = length (signature_tvars sigma) ->
    align_cases (extract_cases (signature_params sigma)) args args_aligned ->
    Forall2 (fun arg param =>
      exists kres_i,
        has_type Se Sf Sc [] mu arg
          (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (fst param), kres_i))
      args_aligned (signature_params sigma) ->
    full_app_candidate Se Sf Sc mu sigma args.
Proof.
  intros Se Sf Sc mu sigma theta args args_aligned Hmono Hlen_theta Halign Htyped.
  exists args_aligned. split; [exact Halign|].
  pose proof (typed_args_plain Se Sf Sc [] mu
    (combine (signature_tvars sigma) (List.map snd theta))
    args_aligned (signature_params sigma) Htyped) as Hplain.
  rewrite (monomorphic_bound_nil sigma theta Hmono) in Hplain.
  eapply Forall2_plain_subst_nil; exact Hplain.
Qed.

(** A typed partial application over a monomorphic signature is a partial
    overload candidate for runtime resolution. *)
Lemma typed_partial_app_candidate_mono :
  forall Se Sf Sc mu sigma (theta : list (tyvar_name * ty))
    args indices,
    monomorphic_signature sigma ->
    length theta = length (signature_tvars sigma) ->
    length args < length (signature_params sigma) ->
    match_partial
      (extract_cases (signature_params sigma))
      (extract_cases args)
      indices ->
    Forall2 (fun arg idx =>
      exists param kres_i,
        nth_error (signature_params sigma) idx = Some param /\
        has_type Se Sf Sc [] mu (fst arg)
          (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (fst param), kres_i))
      args indices ->
    partial_app_candidate Se Sf Sc mu sigma args indices.
Proof.
  intros Se Sf Sc mu sigma theta args indices Hmono Hlen_theta Hlt Hmatch Htyped.
  repeat split; [exact Hlt | exact Hmatch |].
  clear Hlt Hmatch.
  induction Htyped as [|arg idx args' idxs' Hhead Hrest IH].
  - constructor.
  - constructor.
    + destruct Hhead as [param [kres_i [Hnth Harg]]].
      exists param. split; [exact Hnth|].
      apply has_type_plain in Harg.
      rewrite (monomorphic_bound_nil sigma theta Hmono) in Harg.
      simpl in Harg. rewrite apply_subst_nil in Harg. exact Harg.
    + exact IH.
Qed.

(** Reordering a well-typed full application into canonical form does not
    change its plain result type. *)
Lemma canonical_app_has_plain_type :
  forall Se Sf Sc mu f sigma (theta : list (tyvar_name * ty)) args args_aligned args',
    In sigma (Sf f) ->
    (Se f = true -> mu = Eff) ->
    length theta = length (signature_tvars sigma) ->
    align_cases (extract_cases (signature_params sigma)) args args_aligned ->
    Forall2 (fun arg param =>
      exists kres_i,
        has_type Se Sf Sc [] mu arg
          (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (fst param), kres_i))
      args_aligned (signature_params sigma) ->
    canonical_args (extract_cases (signature_params sigma)) args = Some args' ->
    has_plain_type Se Sf Sc [] mu (EApp f args')
      (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (signature_return_ty sigma)).
Proof.
  intros Se Sf Sc mu f sigma theta args args_aligned args'
    Hsig Hmode Hlen_theta Halign Htyped Hcanon.
  pose proof (canonical_args_as_combine
    (extract_cases (signature_params sigma)) args args_aligned args' Halign Hcanon) as Hcanon_eq.
  exists (Some (signature_return_case sigma)).
  eapply T_App with (sigma := sigma) (theta := theta) (args_aligned := args_aligned).
  - exact Hsig.
  - exact Hmode.
  - exact Hlen_theta.
  - rewrite Hcanon_eq.
    apply align_cases_combine.
    eapply align_cases_length. exact Halign.
  - exact Htyped.
Qed.

(** Once the canonical payload list is typed against the signature
    parameters, the enclosing full application is typed. *)
Lemma app_payloads_typed_has_plain_type :
  forall Se Sf Sc mu f sigma (theta : list (tyvar_name * ty)) payloads',
    In sigma (Sf f) ->
    (Se f = true -> mu = Eff) ->
    length theta = length (signature_tvars sigma) ->
    Forall2 (fun arg (param : signature_param) =>
      exists kres_i,
        has_type Se Sf Sc [] mu arg
          (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (fst param), kres_i))
      payloads' (signature_params sigma) ->
    has_plain_type Se Sf Sc [] mu
      (EApp f (combine payloads' (extract_cases (signature_params sigma))))
      (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (signature_return_ty sigma)).
Proof.
  intros Se Sf Sc mu f sigma theta payloads'
    Hsig Hmode Hlen_theta Htyped.
  assert (Hlen_payloads :
    length payloads' = length (extract_cases (signature_params sigma))).
  {
    pose proof (Forall2_length Htyped) as Hlen.
    unfold extract_cases. rewrite length_map. exact Hlen.
  }
  exists (Some (signature_return_case sigma)).
  eapply T_App with (sigma := sigma) (theta := theta) (args_aligned := payloads').
  - exact Hsig.
  - exact Hmode.
  - exact Hlen_theta.
  - apply align_cases_combine. exact Hlen_payloads.
  - exact Htyped.
Qed.

(** If payload typing survives a transformation of the canonical payload
    list, the whole application keeps the same plain type. *)
Lemma app_payloads_preserved_has_plain_type :
  forall Se Sf Sc mu f sigma (theta : list (tyvar_name * ty))
    args args_aligned payloads',
    In sigma (Sf f) ->
    (Se f = true -> mu = Eff) ->
    length theta = length (signature_tvars sigma) ->
    align_cases (extract_cases (signature_params sigma)) args args_aligned ->
    Forall2 (fun arg (param : signature_param) =>
      exists kres_i,
        has_type Se Sf Sc [] mu arg
          (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (fst param), kres_i))
      args_aligned (signature_params sigma) ->
    canonical_args (extract_cases (signature_params sigma)) args = Some args ->
    (forall (params : list signature_param),
      Forall2 (fun arg (param : signature_param) =>
        exists kres_i,
          has_type Se Sf Sc [] mu arg
            (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (fst param), kres_i))
        (List.map fst args) params ->
      Forall2 (fun arg (param : signature_param) =>
        exists kres_i,
          has_type Se Sf Sc [] mu arg
            (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (fst param), kres_i))
        payloads' params) ->
    has_plain_type Se Sf Sc [] mu
      (EApp f (combine payloads' (extract_cases (signature_params sigma))))
      (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (signature_return_ty sigma)).
Proof.
  intros Se Sf Sc mu f sigma theta args args_aligned payloads'
    Hsig Hmode Hlen_theta Halign Htyped Hcanon Hpreserved.
  pose proof (canonical_args_payload_eq
    (extract_cases (signature_params sigma)) args args_aligned args Halign Hcanon) as Halign_eq.
  pose proof (Hpreserved (signature_params sigma)) as Hpayloads_typed.
  rewrite Halign_eq in Hpayloads_typed.
  eapply app_payloads_typed_has_plain_type; eauto.
Qed.

(** A single step in the payload list of a canonical application preserves
    the plain type of the enclosing call. *)
Lemma app_payload_step_has_plain_type :
  forall Se Sf Sc F mu f sigma (theta : list (tyvar_name * ty)) args args_aligned payloads',
    In sigma (Sf f) ->
    (Se f = true -> mu = Eff) ->
    length theta = length (signature_tvars sigma) ->
    align_cases (extract_cases (signature_params sigma)) args args_aligned ->
    Forall2 (fun arg param =>
      exists kres_i,
        has_type Se Sf Sc [] mu arg
          (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (fst param), kres_i))
      args_aligned (signature_params sigma) ->
    canonical_args (extract_cases (signature_params sigma)) args = Some args ->
    step_exprs F Sc (Se:=Se) (Sf:=Sf) (mu:=mu) (List.map fst args) payloads' ->
    (forall e0 e1 tau0 kres0,
      has_type Se Sf Sc [] mu e0 (tau0, kres0) ->
      step F Sc (Se:=Se) (Sf:=Sf) (mu:=mu) e0 e1 ->
      has_plain_type Se Sf Sc [] mu e1 tau0) ->
    has_plain_type Se Sf Sc [] mu
      (EApp f (combine payloads' (extract_cases (signature_params sigma))))
      (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (signature_return_ty sigma)).
Proof.
  intros Se Sf Sc F mu f sigma theta args args_aligned payloads'
    Hsig Hmode Hlen_theta Halign Htyped Hcanon Hsteps Hpres.
  pose proof (canonical_args_payload_eq
    (extract_cases (signature_params sigma)) args args_aligned args Halign Hcanon) as Halign_eq.
  rewrite Halign_eq in Hsteps.
  pose proof (step_exprs_preserves_typed_params Se Sf Sc F mu
    (combine (signature_tvars sigma) (List.map snd theta))
    args_aligned payloads' (signature_params sigma) Hpres Hsteps Htyped) as Htyped'.
  assert (Hlen_payloads :
    length payloads' = length (extract_cases (signature_params sigma))).
  {
    pose proof (Forall2_length Htyped') as Hlen.
    unfold extract_cases. rewrite length_map. exact Hlen.
  }
  exists (Some (signature_return_case sigma)).
  eapply T_App with (sigma := sigma) (theta := theta) (args_aligned := payloads').
  - exact Hsig.
  - exact Hmode.
  - exact Hlen_theta.
  - apply align_cases_combine. exact Hlen_payloads.
  - exact Htyped'.
Qed.

(** A well-typed partial call computes the residual arrow type determined by
    the still-missing parameters. *)
Lemma partial_app_args_typed_has_plain_type :
  forall Se Sf Sc mu f sigma (theta : list (tyvar_name * ty)) args' indices,
    In sigma (Sf f) ->
    (Se f = true -> mu = Eff) ->
    length theta = length (signature_tvars sigma) ->
    length args' < length (signature_params sigma) ->
    match_partial
      (extract_cases (signature_params sigma))
      (extract_cases args')
      indices ->
    Forall2 (fun arg (idx : nat) =>
      exists param kres_i,
        nth_error (signature_params sigma) idx = Some param /\
        has_type Se Sf Sc [] mu (fst arg)
          (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (fst param), kres_i))
      args' indices ->
    has_plain_type Se Sf Sc [] mu (EApp f args')
      (List.fold_right TyArr
        (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (signature_return_ty sigma))
        (List.map (fun t => apply_subst (combine (signature_tvars sigma) (List.map snd theta)) t)
          (collect_at_indices
            (remaining_indices 0 (length (signature_params sigma)) indices)
            (signature_params sigma)))).
Proof.
  intros Se Sf Sc mu f sigma theta args' indices
    Hsig Hmode Hlen_theta Hlt Hmatch Htyped.
  exists None.
  eapply T_App_Partial with (sigma := sigma) (theta := theta) (indices := indices).
  - exact Hsig.
  - exact Hmode.
  - exact Hlen_theta.
  - exact Hlt.
  - exact Hmatch.
  - exact Htyped.
Qed.

(** If partial-application argument typing is preserved under an update, the
    resulting residual function type is unchanged. *)
Lemma partial_app_args_preserved_has_plain_type :
  forall Se Sf Sc mu f sigma (theta : list (tyvar_name * ty))
    args args' indices,
    In sigma (Sf f) ->
    (Se f = true -> mu = Eff) ->
    length theta = length (signature_tvars sigma) ->
    length args < length (signature_params sigma) ->
    match_partial
      (extract_cases (signature_params sigma))
      (extract_cases args)
      indices ->
    Forall2 (fun arg (idx : nat) =>
      exists param kres_i,
        nth_error (signature_params sigma) idx = Some param /\
        has_type Se Sf Sc [] mu (fst arg)
          (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (fst param), kres_i))
      args indices ->
    extract_cases args = extract_cases args' ->
    (forall (idxs : list nat),
      Forall2 (fun arg (idx : nat) =>
        exists param kres_i,
          nth_error (signature_params sigma) idx = Some param /\
          has_type Se Sf Sc [] mu (fst arg)
            (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (fst param), kres_i))
        args idxs ->
      Forall2 (fun arg (idx : nat) =>
        exists param kres_i,
          nth_error (signature_params sigma) idx = Some param /\
          has_type Se Sf Sc [] mu (fst arg)
            (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (fst param), kres_i))
        args' idxs) ->
    has_plain_type Se Sf Sc [] mu (EApp f args')
      (List.fold_right TyArr
        (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (signature_return_ty sigma))
        (List.map (fun t => apply_subst (combine (signature_tvars sigma) (List.map snd theta)) t)
          (collect_at_indices
            (remaining_indices 0 (length (signature_params sigma)) indices)
            (signature_params sigma)))).
Proof.
  intros Se Sf Sc mu f sigma theta args args' indices
    Hsig Hmode Hlen_theta Hlt Hmatch Htyped Hcases Hpreserved.
  pose proof (Hpreserved indices Htyped) as Htyped'.
  assert (Hlen_args' : length args' = length args).
  {
    pose proof (Forall2_length Htyped) as Hlen_args.
    pose proof (Forall2_length Htyped') as Hlen_args'.
    lia.
  }
  eapply partial_app_args_typed_has_plain_type; eauto.
  - rewrite Hlen_args'. exact Hlt.
  - rewrite <- Hcases. exact Hmatch.
Qed.

(** Stepping one argument of a partial application preserves the plain type
    of that partial application. *)
Lemma partial_app_arg_step_has_plain_type :
  forall Se Sf Sc F mu f sigma (theta : list (tyvar_name * ty)) args args' indices,
    In sigma (Sf f) ->
    (Se f = true -> mu = Eff) ->
    length theta = length (signature_tvars sigma) ->
    length args < length (signature_params sigma) ->
    match_partial
      (extract_cases (signature_params sigma))
      (extract_cases args)
      indices ->
    Forall2 (fun arg idx =>
      exists param kres_i,
        nth_error (signature_params sigma) idx = Some param /\
        has_type Se Sf Sc [] mu (fst arg)
          (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (fst param), kres_i))
      args indices ->
    step_args F Sc (Se:=Se) (Sf:=Sf) (mu:=mu) args args' ->
    (forall e0 e1 tau0 kres0,
      has_type Se Sf Sc [] mu e0 (tau0, kres0) ->
      step F Sc (Se:=Se) (Sf:=Sf) (mu:=mu) e0 e1 ->
      has_plain_type Se Sf Sc [] mu e1 tau0) ->
    has_plain_type Se Sf Sc [] mu (EApp f args')
      (List.fold_right TyArr
        (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (signature_return_ty sigma))
        (List.map (fun t => apply_subst (combine (signature_tvars sigma) (List.map snd theta)) t)
          (collect_at_indices
            (remaining_indices 0 (length (signature_params sigma)) indices)
            (signature_params sigma)))).
Proof.
  intros Se Sf Sc F mu f sigma theta args args' indices
    Hsig Hmode Hlen_theta Hlt Hmatch Htyped Hsteps Hpres.
  pose proof (step_args_preserves_typed_indices Se Sf Sc F mu
    (combine (signature_tvars sigma) (List.map snd theta))
    args args' sigma indices Hpres Hsteps Htyped) as Htyped'.
  assert (Hlen_args' : length args' = length args).
  {
    pose proof (Forall2_length Htyped) as Hlen_args.
    pose proof (Forall2_length Htyped') as Hlen_args'.
    lia.
  }
  pose proof (step_args_extract_cases Se Sf F Sc mu args args' Hsteps) as Hcases.
  exists None.
  eapply T_App_Partial with (sigma := sigma) (theta := theta) (indices := indices).
  - exact Hsig.
  - exact Hmode.
  - exact Hlen_theta.
  - rewrite Hlen_args'. exact Hlt.
  - rewrite <- Hcases. exact Hmatch.
  - exact Htyped'.
Qed.

(** Constructor arguments can be canonicalized just like function arguments
    without changing the resulting constructor type. *)
Lemma canonical_ctor_has_plain_type :
  forall Se Sf Sc mu C sigma (theta : list (tyvar_name * ty)) args args_aligned args',
    Sc C = Some sigma ->
    length theta = length (signature_tvars sigma) ->
    align_cases (extract_cases (signature_params sigma)) args args_aligned ->
    Forall2 (fun arg param =>
      exists kres_i,
        has_type Se Sf Sc [] mu arg
          (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (fst param), kres_i))
      args_aligned (signature_params sigma) ->
    canonical_args (extract_cases (signature_params sigma)) args = Some args' ->
    has_plain_type Se Sf Sc [] mu (ECtor C args')
      (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (signature_return_ty sigma)).
Proof.
  intros Se Sf Sc mu C sigma theta args args_aligned args'
    Hsig Hlen_theta Halign Htyped Hcanon.
  pose proof (canonical_args_as_combine
    (extract_cases (signature_params sigma)) args args_aligned args' Halign Hcanon) as Hcanon_eq.
  exists (Some (signature_return_case sigma)).
  eapply T_Ctor with (sigma := sigma) (theta := theta) (args_aligned := args_aligned).
  - exact Hsig.
  - exact Hlen_theta.
  - rewrite Hcanon_eq.
    apply align_cases_combine.
    eapply align_cases_length. exact Halign.
  - exact Htyped.
Qed.

(** Typed canonical payloads are enough to reconstruct a well-typed
    constructor application. *)
Lemma ctor_payloads_typed_has_plain_type :
  forall Se Sf Sc mu C sigma (theta : list (tyvar_name * ty)) payloads',
    Sc C = Some sigma ->
    length theta = length (signature_tvars sigma) ->
    Forall2 (fun arg (param : signature_param) =>
      exists kres_i,
        has_type Se Sf Sc [] mu arg
          (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (fst param), kres_i))
      payloads' (signature_params sigma) ->
    has_plain_type Se Sf Sc [] mu
      (ECtor C (combine payloads' (extract_cases (signature_params sigma))))
      (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (signature_return_ty sigma)).
Proof.
  intros Se Sf Sc mu C sigma theta payloads'
    Hsig Hlen_theta Htyped.
  assert (Hlen_payloads :
    length payloads' = length (extract_cases (signature_params sigma))).
  {
    pose proof (Forall2_length Htyped) as Hlen.
    unfold extract_cases. rewrite length_map. exact Hlen.
  }
  exists (Some (signature_return_case sigma)).
  eapply T_Ctor with (sigma := sigma) (theta := theta) (args_aligned := payloads').
  - exact Hsig.
  - exact Hlen_theta.
  - apply align_cases_combine. exact Hlen_payloads.
  - exact Htyped.
Qed.

(** If constructor payload typing is preserved across an update, the
    enclosing constructor keeps the same plain type. *)
Lemma ctor_payloads_preserved_has_plain_type :
  forall Se Sf Sc mu C sigma (theta : list (tyvar_name * ty))
    args args_aligned payloads',
    Sc C = Some sigma ->
    length theta = length (signature_tvars sigma) ->
    align_cases (extract_cases (signature_params sigma)) args args_aligned ->
    Forall2 (fun arg (param : signature_param) =>
      exists kres_i,
        has_type Se Sf Sc [] mu arg
          (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (fst param), kres_i))
      args_aligned (signature_params sigma) ->
    canonical_args (extract_cases (signature_params sigma)) args = Some args ->
    (forall (params : list signature_param),
      Forall2 (fun arg (param : signature_param) =>
        exists kres_i,
          has_type Se Sf Sc [] mu arg
            (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (fst param), kres_i))
        (List.map fst args) params ->
      Forall2 (fun arg (param : signature_param) =>
        exists kres_i,
          has_type Se Sf Sc [] mu arg
            (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (fst param), kres_i))
        payloads' params) ->
    has_plain_type Se Sf Sc [] mu
      (ECtor C (combine payloads' (extract_cases (signature_params sigma))))
      (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (signature_return_ty sigma)).
Proof.
  intros Se Sf Sc mu C sigma theta args args_aligned payloads'
    Hsig Hlen_theta Halign Htyped Hcanon Hpreserved.
  pose proof (canonical_args_payload_eq
    (extract_cases (signature_params sigma)) args args_aligned args Halign Hcanon) as Halign_eq.
  pose proof (Hpreserved (signature_params sigma)) as Hpayloads_typed.
  rewrite Halign_eq in Hpayloads_typed.
  eapply ctor_payloads_typed_has_plain_type; eauto.
Qed.

(** A single step in a constructor payload list preserves the plain type of
    the enclosing constructor application. *)
Lemma ctor_payload_step_has_plain_type :
  forall Se Sf Sc F mu C sigma (theta : list (tyvar_name * ty)) args args_aligned payloads',
    Sc C = Some sigma ->
    length theta = length (signature_tvars sigma) ->
    align_cases (extract_cases (signature_params sigma)) args args_aligned ->
    Forall2 (fun arg param =>
      exists kres_i,
        has_type Se Sf Sc [] mu arg
          (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (fst param), kres_i))
      args_aligned (signature_params sigma) ->
    canonical_args (extract_cases (signature_params sigma)) args = Some args ->
    step_exprs F Sc (Se:=Se) (Sf:=Sf) (mu:=mu) (List.map fst args) payloads' ->
    (forall e0 e1 tau0 kres0,
      has_type Se Sf Sc [] mu e0 (tau0, kres0) ->
      step F Sc (Se:=Se) (Sf:=Sf) (mu:=mu) e0 e1 ->
      has_plain_type Se Sf Sc [] mu e1 tau0) ->
    has_plain_type Se Sf Sc [] mu
      (ECtor C (combine payloads' (extract_cases (signature_params sigma))))
      (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (signature_return_ty sigma)).
Proof.
  intros Se Sf Sc F mu C sigma theta args args_aligned payloads'
    Hsig Hlen_theta Halign Htyped Hcanon Hsteps Hpres.
  pose proof (canonical_args_payload_eq
    (extract_cases (signature_params sigma)) args args_aligned args Halign Hcanon) as Halign_eq.
  rewrite Halign_eq in Hsteps.
  pose proof (step_exprs_preserves_typed_params Se Sf Sc F mu
    (combine (signature_tvars sigma) (List.map snd theta))
    args_aligned payloads' (signature_params sigma) Hpres Hsteps Htyped) as Htyped'.
  assert (Hlen_payloads :
    length payloads' = length (extract_cases (signature_params sigma))).
  {
    pose proof (Forall2_length Htyped') as Hlen.
    unfold extract_cases. rewrite length_map. exact Hlen.
  }
  exists (Some (signature_return_case sigma)).
  eapply T_Ctor with (sigma := sigma) (theta := theta) (args_aligned := payloads').
  - exact Hsig.
  - exact Hlen_theta.
  - apply align_cases_combine. exact Hlen_payloads.
  - exact Htyped'.
Qed.

(** Beta-reduction preserves typing once a clause has semantically matched
    the canonical argument list.  The proof reconstructs the aligned clause
    patterns from [clause_core_ok], uses [pats_match_typed] to type the
    substitution environment produced by runtime matching, and then applies
    [subst_env_preserves_typing]. *)
Lemma app_beta_has_plain_type :
  forall Se Sf Sc mu f sigma (theta : list (tyvar_name * ty))
    args args_aligned cl rho,
    ctor_ctx_regular Sc ->
    monomorphic_signature sigma ->
    (Se f = true -> mu = Eff) ->
    length theta = length (signature_tvars sigma) ->
    align_cases (extract_cases (signature_params sigma)) args args_aligned ->
    Forall2 (fun arg param =>
      exists kres_i,
        has_type Se Sf Sc [] mu arg
          (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (fst param), kres_i))
      args_aligned (signature_params sigma) ->
    canonical_args (extract_cases (signature_params sigma)) args = Some args ->
    clause_core_ok Se Sf Sc f sigma cl ->
    clause_matches Sc sigma cl args rho ->
    has_plain_type Se Sf Sc [] mu
      (subst_env rho (clause_body cl))
      (signature_return_ty sigma).
Proof.
  intros Se Sf Sc mu f sigma theta args args_aligned cl rho
    Hregular Hmono Hmode Hlen_theta Halign Htyped Hcanon Hcore Hmatch.
  destruct Hcore as
    [_ [_ [pats_aligned_core
      [Gammas [Halign_core [_ [Hlen_Gammas [Hbinds Hbody_plain]]]]]]]].
  destruct Hmatch as [pats_aligned_match [Halign_match Hmatches]].
  pose proof (align_cases_deterministic pat
    (extract_cases (signature_params sigma))
    (clause_pats cl) pats_aligned_core pats_aligned_match
    Halign_core Halign_match) as Hpats_eq.
  subst pats_aligned_match.
  pose proof (typed_args_plain Se Sf Sc [] mu
    (combine (signature_tvars sigma) (List.map snd theta))
    args_aligned (signature_params sigma) Htyped) as Hargs_plain.
  pose proof (canonical_args_payload_eq
    (extract_cases (signature_params sigma)) args args_aligned args Halign Hcanon) as Hargs_eq.
  assert (Hargs_plain_mono :
    Forall2 (fun v tp =>
      has_plain_type Se Sf Sc [] mu v (fst tp))
      (List.map fst args) (signature_params sigma)).
  {
    rewrite Hargs_eq.
    rewrite (monomorphic_bound_nil sigma theta Hmono) in Hargs_plain.
    eapply Forall2_plain_subst_nil.
    exact Hargs_plain.
  }
  assert (Henv_typed :
    subst_env_typed Se Sf Sc mu rho (List.concat Gammas)).
  {
    eapply pats_match_typed; eauto.
  }
  pose proof (Hbody_plain mu Hmode) as Hbody.
  destruct Hbody as [kres_body Hbody'].
  exact (subst_env_preserves_typing Se Sf Sc mu
    rho (List.concat Gammas) (clause_body cl)
    (signature_return_ty sigma) kres_body Henv_typed Hbody').
Qed.

(** Reducing a [match] through a semantically matching branch preserves
    typing because [pat_match_typed] reconstructs a well-typed substitution
    environment for that branch. *)
Lemma match_branch_has_plain_type :
  forall Se Sf Sc mu es tau_s kres_s branches p body rho tau,
    ctor_ctx_regular Sc ->
    has_type Se Sf Sc [] mu es (tau_s, kres_s) ->
    Forall (fun pb =>
      exists Gamma_p tau_j kres_j,
        pat_bind Sc (fst pb) tau_s Gamma_p /\
        has_type Se Sf Sc (ctx_concat Gamma_p []) mu (snd pb) (tau_j, kres_j) /\
        tau_j = tau
    ) branches ->
    In (p, body) branches ->
    pat_match Sc p es rho ->
    has_plain_type Se Sf Sc [] mu
      (subst_env rho body)
      tau.
Proof.
  intros Se Sf Sc mu es tau_s kres_s branches p body rho tau
    Hregular Hscrut Hbranches Hin Hmatch.
  apply Forall_forall with (x := (p, body)) in Hbranches; [|exact Hin].
  destruct Hbranches as [Gamma_p [tau_j [kres_j [Hbind [Hbody Heqtau]]]]].
  subst tau_j.
  unfold ctx_concat in Hbody.
  rewrite app_nil_r in Hbody.
  assert (Henv_pat :
    subst_env_typed Se Sf Sc mu rho Gamma_p).
  {
    eapply pat_match_typed; eauto; now exists kres_s.
  }
  exact (subst_env_preserves_typing Se Sf Sc mu
    rho Gamma_p body tau kres_j Henv_pat Hbody).
Qed.

(** The following lemmas extract individual facts from the
    [fun_entry_ctx_ok] invariant.  They are used by the preservation
    proof's local tactics to avoid repeating the [destruct] pattern
    every time. *)

(** Every declared signature has a corresponding runtime entry in the
    overload set for that function name. *)
Lemma fun_entry_ctx_complete_entry :
  forall Se Sf Sc F f sigma,
    fun_entry_ctx_ok Se Sf Sc F ->
    In sigma (Sf f) ->
    exists entry, In entry (F f) /\ fun_entry_signature entry = sigma.
Proof.
  intros Se Sf Sc F f sigma [_ [Hcomplete _]] Hsig.
  eauto.
Qed.

(** Function entries used by evaluation are monomorphic. *)
Lemma fun_entry_ctx_entry_monomorphic :
  forall Se Sf Sc F f entry,
    fun_entry_ctx_ok Se Sf Sc F ->
    In entry (F f) ->
    monomorphic_signature (fun_entry_signature entry).
Proof.
  intros Se Sf Sc F f entry [Hsound _] Hentry.
  destruct (Hsound _ _ Hentry) as [_ [Hmono _]]; exact Hmono.
Qed.

(** Runtime clauses inherit the pre-computed [clause_core_ok] package
    recorded in [fun_entry_ctx_ok]. *)
Lemma fun_entry_ctx_clause_core :
  forall Se Sf Sc F f entry cl,
    fun_entry_ctx_ok Se Sf Sc F ->
    In entry (F f) ->
    In cl (fun_entry_clauses entry) ->
    clause_core_ok Se Sf Sc f (fun_entry_signature entry) cl.
Proof.
  intros Se Sf Sc F f entry cl [Hsound _] Hentry Hin.
  destruct (Hsound _ _ Hentry) as [_ [_ [Hclauses _]]].
  eapply Forall_forall; eauto.
Qed.

(** A resolved full application uses the same signature as any other full
    candidate for that call site. *)
Lemma fun_entry_ctx_full_resolves_signature :
  forall Se Sf Sc F mu f sigma entry args,
    fun_entry_ctx_ok Se Sf Sc F ->
    In sigma (Sf f) ->
    full_app_candidate Se Sf Sc mu sigma args ->
    full_app_resolves Se Sf Sc F mu f args entry ->
    sigma = fun_entry_signature entry.
Proof.
  intros Se Sf Sc F mu f sigma entry args Henv Hsig Hcand Hresolve.
  destruct Hresolve as [Hentry [_ Huniq]].
  destruct (fun_entry_ctx_complete_entry _ _ _ _ _ _ Henv Hsig) as [entry_sigma [Hin_sigma Hiface_sigma]].
  rewrite <- Hiface_sigma.
  assert (Hcand_sigma :
    full_app_candidate Se Sf Sc mu (fun_entry_signature entry_sigma) args).
  { rewrite Hiface_sigma. exact Hcand. }
  eapply Huniq; eauto.
Qed.

(** Likewise for partial applications: the resolved runtime entry agrees with
    any other partial candidate for that call site. *)
Lemma fun_entry_ctx_partial_resolves_signature :
  forall Se Sf Sc F mu f sigma entry args indices_typed indices_resolved,
    fun_entry_ctx_ok Se Sf Sc F ->
    In sigma (Sf f) ->
    partial_app_candidate Se Sf Sc mu sigma args indices_typed ->
    partial_app_resolves Se Sf Sc F mu f args entry indices_resolved ->
    sigma = fun_entry_signature entry.
Proof.
  intros Se Sf Sc F mu f sigma entry args indices_typed indices_resolved
    Henv Hsig Hcand Hresolve.
  destruct Hresolve as [Hentry [_ [_ Huniq]]].
  destruct (fun_entry_ctx_complete_entry _ _ _ _ _ _ Henv Hsig) as [entry_sigma [Hin_sigma Hiface_sigma]].
  rewrite <- Hiface_sigma.
  assert (Hcand_sigma :
    partial_app_candidate Se Sf Sc mu (fun_entry_signature entry_sigma) args indices_typed).
  { rewrite Hiface_sigma. exact Hcand. }
  eapply Huniq; eauto.
Qed.

(** If a call site is a full candidate for some declared signature, then it
    cannot resolve as a partial application at runtime. *)
Lemma full_candidate_not_partial_resolved :
  forall Se Sf Sc F mu f sigma entry args indices,
    fun_entry_ctx_ok Se Sf Sc F ->
    In sigma (Sf f) ->
    full_app_candidate Se Sf Sc mu sigma args ->
    partial_app_resolves Se Sf Sc F mu f args entry indices ->
    False.
Proof.
  intros Se Sf Sc F mu f sigma entry args indices Henv Hsig Hfull Hresolve.
  destruct Hresolve as [Hentry [Hpartial [Hnofull Huniq]]].
  destruct (fun_entry_ctx_complete_entry _ _ _ _ _ _ Henv Hsig) as [entry_sigma [Hin_sigma Hiface_sigma]].
  assert (Hfull_sigma :
    full_app_candidate Se Sf Sc mu (fun_entry_signature entry_sigma) args).
  { rewrite Hiface_sigma. exact Hfull. }
  eapply Hnofull; eauto.
Qed.

(** Dually, a partial candidate cannot step through a full runtime
    resolution. *)
Lemma partial_candidate_not_full_resolved :
  forall Se Sf Sc F mu f sigma entry args indices,
    fun_entry_ctx_ok Se Sf Sc F ->
    In sigma (Sf f) ->
    partial_app_candidate Se Sf Sc mu sigma args indices ->
    full_app_resolves Se Sf Sc F mu f args entry ->
    False.
Proof.
  intros Se Sf Sc F mu f sigma entry args indices Henv Hsig Hpartial Hresolve.
  destruct Hresolve as [Hentry_full [Hfull Huniq]].
  destruct Henv as [_ [Hcomplete [_ [_ Hno_overlap]]]].
  destruct (Hcomplete _ _ Hsig) as [entry_sigma [Hin_sigma Hiface_sigma]].
  assert (Hpartial_sigma :
    partial_app_candidate Se Sf Sc mu (fun_entry_signature entry_sigma) args indices).
  { rewrite Hiface_sigma. exact Hpartial. }
  exact (Hno_overlap mu f entry entry_sigma args indices
    Hentry_full Hin_sigma Hfull Hpartial_sigma).
Qed.

(** Runtime entries inherit the semantic exhaustiveness package recorded in
    [fun_entry_ctx_ok]. *)
Lemma fun_entry_ctx_entry_exhaustive :
  forall Se Sf Sc F f entry mu,
    fun_entry_ctx_ok Se Sf Sc F ->
    In entry (F f) ->
    mode_compatible Se f mu ->
    clauses_exhaustive Se Sf Sc mu
      (fun_entry_signature entry) (fun_entry_clauses entry).
Proof.
  intros Se Sf Sc F f entry mu [Hsound _] Hentry Hmode.
  destruct (Hsound _ _ Hentry) as [_ [_ [_ Hexhaustive]]].
  exact (Hexhaustive mu Hmode).
Qed.

(** A closed, well-typed full application resolves to the overload whose
    signature appears in the typing derivation. *)
Lemma typed_full_app_resolves :
  forall Se Sf Sc F mu f sigma (theta : list (tyvar_name * ty))
    args args_aligned,
    fun_entry_ctx_ok Se Sf Sc F ->
    In sigma (Sf f) ->
    (Se f = true -> mu = Eff) ->
    length theta = length (signature_tvars sigma) ->
    align_cases (extract_cases (signature_params sigma)) args args_aligned ->
    Forall2 (fun arg param =>
      exists kres_i,
        has_type Se Sf Sc [] mu arg
          (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (fst param), kres_i))
      args_aligned (signature_params sigma) ->
    exists entry,
      full_app_resolves Se Sf Sc F mu f args entry /\
      fun_entry_signature entry = sigma.
Proof.
  intros Se Sf Sc F mu f sigma theta args args_aligned
    Henv Hsig Hmode Hlen_theta Halign Htyped.
  destruct (fun_entry_ctx_complete_entry _ _ _ _ _ _ Henv Hsig) as [entry [Hentry Hifc]].
  pose proof (fun_entry_ctx_entry_monomorphic _ _ _ _ _ _ Henv Hentry) as Hmono_entry.
  assert (Hmono_sigma : monomorphic_signature sigma).
  { rewrite <- Hifc. exact Hmono_entry. }
  assert (Hcand_sigma : full_app_candidate Se Sf Sc mu sigma args).
  { eapply typed_full_app_candidate_mono; eauto. }
  assert (Hcand_entry : full_app_candidate Se Sf Sc mu (fun_entry_signature entry) args).
  { rewrite Hifc. exact Hcand_sigma. }
  destruct Henv as [_ [_ [Huniq_full _]]].
  exists entry. split.
  - split.
    + exact Hentry.
    + split.
      * exact Hcand_entry.
      * intros entry' Hentry' Hcand'.
        eapply Huniq_full; eauto.
  - exact Hifc.
Qed.

(** Likewise for a closed, well-typed partial application. *)
Lemma typed_partial_app_resolves :
  forall Se Sf Sc F mu f sigma (theta : list (tyvar_name * ty))
    args indices,
    fun_entry_ctx_ok Se Sf Sc F ->
    In sigma (Sf f) ->
    (Se f = true -> mu = Eff) ->
    length theta = length (signature_tvars sigma) ->
    length args < length (signature_params sigma) ->
    match_partial
      (extract_cases (signature_params sigma))
      (extract_cases args)
      indices ->
    Forall2 (fun arg idx =>
      exists param kres_i,
        nth_error (signature_params sigma) idx = Some param /\
        has_type Se Sf Sc [] mu (fst arg)
          (apply_subst (combine (signature_tvars sigma) (List.map snd theta)) (fst param), kres_i))
      args indices ->
    exists entry,
      partial_app_resolves Se Sf Sc F mu f args entry indices /\
      fun_entry_signature entry = sigma.
Proof.
  intros Se Sf Sc F mu f sigma theta args indices
    Henv Hsig Hmode Hlen_theta Hlt Hmatch Htyped.
  destruct (fun_entry_ctx_complete_entry _ _ _ _ _ _ Henv Hsig) as [entry [Hentry Hifc]].
  pose proof (fun_entry_ctx_entry_monomorphic _ _ _ _ _ _ Henv Hentry) as Hmono_entry.
  assert (Hmono_sigma : monomorphic_signature sigma).
  { rewrite <- Hifc. exact Hmono_entry. }
  assert (Hcand_sigma : partial_app_candidate Se Sf Sc mu sigma args indices).
  { eapply typed_partial_app_candidate_mono; eauto. }
  assert (Hcand_entry : partial_app_candidate Se Sf Sc mu (fun_entry_signature entry) args indices).
  { rewrite Hifc. exact Hcand_sigma. }
  destruct Henv as [_ [_ [_ [Huniq_partial Hno_overlap]]]].
  exists entry. split.
  - refine (conj Hentry
      (conj Hcand_entry
        (conj
          (fun entry' Hentry' Hfull' =>
             Hno_overlap mu f entry' entry args indices
               Hentry' Hentry Hfull' Hcand_entry)
          (fun entry' indices' Hentry' Hcand' =>
             Huniq_partial mu f entry' entry args indices' indices
               Hentry' Hentry Hcand' Hcand_entry)))).
  - exact Hifc.
Qed.

(** A fully aligned call necessarily supplies exactly one argument per
    signature parameter. *)
Lemma aligned_signature_args_length :
  forall (A : Type) (sigma : signature)
    (args : list (A * case_label)) aligned,
    align_cases (extract_cases (signature_params sigma)) args aligned ->
    length args = length (signature_params sigma).
Proof.
  intros A sigma args aligned Halign.
  pose proof (align_cases_provided_length _ _ _ _ Halign) as Hlen.
  unfold extract_cases in Hlen. rewrite length_map in Hlen.
  exact Hlen.
Qed.

(** Canonicalized arguments also have full signature arity. *)
Lemma canonical_signature_args_length :
  forall (sigma : signature)
    (args args' : list (expr * case_label)),
    canonical_args (extract_cases (signature_params sigma)) args = Some args' ->
    length args = length (signature_params sigma).
Proof.
  intros sigma args args' Hcanon.
  pose proof (canonical_args_length _ _ _ Hcanon) as Hlen.
  unfold extract_cases in Hlen. rewrite length_map in Hlen.
  exact Hlen.
Qed.

(** A fully aligned application cannot simultaneously be a partial one. *)
Lemma aligned_signature_args_not_partial :
  forall (A : Type) (sigma : signature)
    (args : list (A * case_label)) aligned,
    align_cases (extract_cases (signature_params sigma)) args aligned ->
    length args < length (signature_params sigma) ->
    False.
Proof.
  intros A sigma args aligned Halign Hlt.
  pose proof (aligned_signature_args_length A sigma args aligned Halign) as Hlen.
  lia.
Qed.

(** Canonical arguments also rule out the partial-application case. *)
Lemma canonical_signature_args_not_partial :
  forall (sigma : signature)
    (args args' : list (expr * case_label)),
    canonical_args (extract_cases (signature_params sigma)) args = Some args' ->
    length args < length (signature_params sigma) ->
    False.
Proof.
  intros sigma args args' Hcanon Hlt.
  pose proof (canonical_signature_args_length sigma args args' Hcanon) as Hlen.
  lia.
Qed.

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
      lemma to learn that the signature variable equals the runtime entry's
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

(** Every closed runtime value inhabits the corresponding semantic-value
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
