(** * Kip Syntax *)
(** Foundational syntax and shared helper definitions for the core Kip development. *)

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

(** A static-semantics judgment returns both the ordinary type and the
    optional return-case annotation produced by the expression. *)
Definition result_ty := (ty * result_case)%type.

(* ================================================================= *)
(** ** Interfaces *)
(* ================================================================= *)

(** [signature_param] pairs a parameter type with the case label that
    must appear at call sites. *)
Definition signature_param := (ty * case_label)%type.

(** Signatures are the shared contract format for constructors and
    functions.  They package quantified type variables, case-labeled
    parameters, and the return information used by the static semantics,
    overload resolution, and dynamic matching. *)
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

(** [fun_clause] is the shared representation of one function clause for the
    static and dynamic semantics: a function name, its case-labeled patterns,
    and the body executed when the clause matches. *)
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
