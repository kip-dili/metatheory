(** * Kip Dynamic Facts *)
(** Proof infrastructure connecting the dynamic semantics to the static semantics. *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Sorting.Permutation.
From Stdlib Require Import Ascii.
From Stdlib Require Import Floats.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Lia.
From KipCore Require Import Syntax.
From KipCore Require Import Static.
From KipCore Require Import StaticFacts.
From KipCore Require Import Dynamic.
Import ListNotations.
Open Scope string_scope.

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

(** If two contexts agree on every variable lookup, then any static-semantics
    derivation under one context transfers to the other.

    The proof uses [fix IH 10] instead of standard [induction]
    because the static-semantics judgment contains [Forall2]-structured
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
    1. The static-semantics judgment nests [Forall2] sub-derivations inside
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
    dynamic constructor case needs:
    - the type-variable instantiation [theta] chosen by the pattern,
    - the aligned subpattern list [pats_aligned],
    - the per-subpattern binding contexts [Gammas],
    - and the fact that the overall binding environment is
      [List.concat Gammas].

    [pat_match_mutual_typed] uses this lemma as the static half of the
    constructor case: after dynamic matching selects a constructor branch,
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
    then rewrites the dynamic payload list into the aligned list expected by
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
    candidate for the dynamic semantics. *)
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
    overload candidate for the dynamic semantics. *)
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
    substitution environment produced by dynamic matching, and then applies
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

(** Every declared signature has a corresponding executable entry in the
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

(** Executable clauses inherit the pre-computed [clause_core_ok] package
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

(** Likewise for partial applications: the resolved entry agrees with any
    other partial candidate for that call site. *)
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
    cannot resolve as a partial application in the dynamic semantics. *)
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

(** Dually, a partial candidate cannot step through a full resolution in the
    dynamic semantics. *)
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

(** Executable entries inherit the semantic exhaustiveness package recorded in
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
