(** * Kip Static Facts *)
(** Proof infrastructure for the static semantics. *)

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

(** Literals are plain values, so their static-semantics judgment carries no
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
