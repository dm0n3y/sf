(** * StlcProp: Properties of STLC *)

Require Export Stlc.
Require Import JRWTactics.
Require Import DmoonTactics.

Module STLCProp.
Import STLC.

(** In this chapter, we develop the fundamental theory of the Simply
    Typed Lambda Calculus -- in particular, the type safety
    theorem. *)

(* ###################################################################### *)
(** * Canonical Forms *)

Lemma canonical_forms_bool : forall t,
  empty ||- t \in TBool ->
  value t ->
  (t = ttrue) \/ (t = tfalse).
Proof.
  intros t HT HVal.
  inversion HVal; intros; subst; try inversion HT; auto.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  empty ||- t \in (TArrow T1 T2) ->
  value t ->
  exists x u, t = tabs x T1 u.
Proof.
  intros t T1 T2 HT HVal.
  inversion HVal; intros; subst; try inversion HT; subst; auto.
  exists x0. exists t0.  auto.
Qed.
   

(* ###################################################################### *)
(** * Progress *)

(** As before, the _progress_ theorem tells us that closed, well-typed
    terms are not stuck: either a well-typed term is a value, or it
    can take an evaluation step.  The proof is a relatively
    straightforward extension of the progress proof we saw in the
    [Types] chapter. *)

Theorem progress : forall t T, 
     empty ||- t \in T ->
     value t \/ exists t', t ==> t'.

(** _Proof_: by induction on the derivation of [||- t \in T].

    - The last rule of the derivation cannot be [T_Var], since a
      variable is never well typed in an empty context.

    - The [T_True], [T_False], and [T_Abs] cases are trivial, since in
      each of these cases we know immediately that [t] is a value.

    - If the last rule of the derivation was [T_App], then [t = t1
      t2], and we know that [t1] and [t2] are also well typed in the
      empty context; in particular, there exists a type [T2] such that
      [||- t1 \in T2 -> T] and [||- t2 \in T2].  By the induction
      hypothesis, either [t1] is a value or it can take an evaluation
      step.

        - If [t1] is a value, we now consider [t2], which by the other
          induction hypothesis must also either be a value or take an
          evaluation step.

            - Suppose [t2] is a value.  Since [t1] is a value with an
              arrow type, it must be a lambda abstraction; hence [t1
              t2] can take a step by [ST_AppAbs].

            - Otherwise, [t2] can take a step, and hence so can [t1
              t2] by [ST_App2].

        - If [t1] can take a step, then so can [t1 t2] by [ST_App1].

    - If the last rule of the derivation was [T_If], then [t = if t1
      then t2 else t3], where [t1] has type [Bool].  By the IH, [t1]
      either is a value or takes a step.

        - If [t1] is a value, then since it has type [Bool] it must be
          either [true] or [false].  If it is [true], then [t] steps
          to [t2]; otherwise it steps to [t3].

        - Otherwise, [t1] takes a step, and therefore so does [t] (by
          [ST_If]).
*)

Proof with eauto.
  intros t T Ht.
  remember (@empty ty) as Gamma.
  has_type_cases (induction Ht) Case; subst Gamma...
  Case "T_Var".
    (* contradictory: variables cannot be typed in an 
       empty context *)
    inversion H. 

  Case "T_App". 
    (* [t] = [t1 t2].  Proceed by cases on whether [t1] is a 
       value or steps... *)
    right. destruct IHHt1...
    SCase "t1 is a value".
      destruct IHHt2...
      SSCase "t2 is also a value".
        assert (exists x0 t0, t1 = tabs x0 T11 t0).
        eapply canonical_forms_fun; eauto.
        destruct H1 as [x0 [t0 Heq]]. subst.
        exists ([x0:=t2]t0)...

      SSCase "t2 steps".
        inversion H0 as [t2' Hstp]. exists (tapp t1 t2')...

    SCase "t1 steps".
      inversion H as [t1' Hstp]. exists (tapp t1' t2)...

  Case "T_If".
    right. destruct IHHt1...
    
    SCase "t1 is a value".
      destruct (canonical_forms_bool t1); subst; eauto. 

    SCase "t1 also steps".
      inversion H as [t1' Hstp]. exists (tif t1' t2 t3)...
Qed.

(** **** Exercise: 3 stars, optional (progress_from_term_ind) *)
(** Show that progress can also be proved by induction on terms
    instead of induction on typing derivations. *)

Ltac find_hastype_inv := 
  match goal with
    | [ H : _ ||- _ \in _ |- _ ] => inversion H; subst
  end.

Ltac find_hastype_invc :=
  match goal with
    | [ H : _ ||- ttrue \in TArrow _ _ |- _ ] => inversion H
    | [ H : _ ||- tfalse \in TArrow _ _ |- _ ] => inversion H
    | [ H : _ ||- _ \in _ |- _ ] => inversion H; subst; clear H
  end.

Ltac find_value_invc :=
  match goal with
    | [ H : value _ |- _ ] => inversion H; subst; clear H
  end.

Ltac break_exists :=
  match goal with
    | [ H : exists _, _ |- _ ] => destruct H
  end.


Theorem progress' : forall t T,
     empty ||- t \in T ->
     value t \/ exists t', t ==> t'.
Proof with auto.
  intros t.
  t_cases (induction t) Case; intros T Ht...
  - find_hastype_invc. discriminate.
  - right.
    find_hastype_inv. repeat find_apply_hyp_hyp.
    intuition; 
      try solve [repeat break_exists; eauto].
    inversion H; subst;
      eauto;
      repeat find_hastype_invc.
  - right.
    find_hastype_inv.
    destruct (IHt1 TBool); eauto.
    + find_value_invc;
        eauto;
        find_hastype_invc.
    + break_exists. eauto.
Qed.

(** [] *)

(* ###################################################################### *)
(** * Preservation *)

(** The other half of the type soundness property is the preservation
    of types during reduction.  For this, we need to develop some
    technical machinery for reasoning about variables and
    substitution.  Working from top to bottom (the high-level property
    we are actually interested in to the lowest-level technical lemmas
    that are needed by various cases of the more interesting proofs),
    the story goes like this:

      - The _preservation theorem_ is proved by induction on a typing
        derivation, pretty much as we did in the [Types] chapter.  The
        one case that is significantly different is the one for the
        [ST_AppAbs] rule, which is defined using the substitution
        operation.  To see that this step preserves typing, we need to
        know that the substitution itself does.  So we prove a...

      - _substitution lemma_, stating that substituting a (closed)
        term [s] for a variable [x] in a term [t] preserves the type
        of [t].  The proof goes by induction on the form of [t] and
        requires looking at all the different cases in the definition
        of substitition.  This time, the tricky cases are the ones for
        variables and for function abstractions.  In both cases, we
        discover that we need to take a term [s] that has been shown
        to be well-typed in some context [Gamma] and consider the same
        term [s] in a slightly different context [Gamma'].  For this
        we prove a...

      - _context invariance_ lemma, showing that typing is preserved
        under "inessential changes" to the context [Gamma] -- in
        particular, changes that do not affect any of the free
        variables of the term.  For this, we need a careful definition
        of

      - the _free variables_ of a term -- i.e., the variables occuring
        in the term that are not in the scope of a function
        abstraction that binds them.
*)

(* ###################################################################### *)
(** ** Free Occurrences *)

(** A variable [x] _appears free in_ a term _t_ if [t] contains some
    occurrence of [x] that is not under an abstraction labeled [x].  For example: 
      - [y] appears free, but [x] does not, in [\x:T->U. x y] 
      - both [x] and [y] appear free in [(\x:T->U. x y) x] 
      - no variables appear free in [\x:T->U. \y:T. x y]  *)

Inductive appears_free_in : id -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (tvar x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (tapp t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (tapp t1 t2)
  | afi_abs : forall x y T11 t12,
      y <> x  ->
      appears_free_in x t12 ->
      appears_free_in x (tabs y T11 t12)
  | afi_if1 : forall x t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x (tif t1 t2 t3)
  | afi_if2 : forall x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x (tif t1 t2 t3)
  | afi_if3 : forall x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x (tif t1 t2 t3).

Tactic Notation "afi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "afi_var"
  | Case_aux c "afi_app1" | Case_aux c "afi_app2" 
  | Case_aux c "afi_abs" 
  | Case_aux c "afi_if1" | Case_aux c "afi_if2" 
  | Case_aux c "afi_if3" ].

Hint Constructors appears_free_in.

(** A term in which no variables appear free is said to be _closed_. *)

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

(* ###################################################################### *)
(** ** Substitution *)

(** We first need a technical lemma connecting free variables and
    typing contexts.  If a variable [x] appears free in a term [t],
    and if we know [t] is well typed in context [Gamma], then it must
    be the case that [Gamma] assigns a type to [x]. *)

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma ||- t \in T ->
   exists T', Gamma x = Some T'.

(** _Proof_: We show, by induction on the proof that [x] appears free
      in [t], that, for all contexts [Gamma], if [t] is well typed
      under [Gamma], then [Gamma] assigns some type to [x].

      - If the last rule used was [afi_var], then [t = x], and from
        the assumption that [t] is well typed under [Gamma] we have
        immediately that [Gamma] assigns a type to [x].

      - If the last rule used was [afi_app1], then [t = t1 t2] and [x]
        appears free in [t1].  Since [t] is well typed under [Gamma],
        we can see from the typing rules that [t1] must also be, and
        the IH then tells us that [Gamma] assigns [x] a type.

      - Almost all the other cases are similar: [x] appears free in a
        subterm of [t], and since [t] is well typed under [Gamma], we
        know the subterm of [t] in which [x] appears is well typed
        under [Gamma] as well, and the IH gives us exactly the
        conclusion we want.

      - The only remaining case is [afi_abs].  In this case [t =
        \y:T11.t12], and [x] appears free in [t12]; we also know that
        [x] is different from [y].  The difference from the previous
        cases is that whereas [t] is well typed under [Gamma], its
        body [t12] is well typed under [(Gamma, y:T11)], so the IH
        allows us to conclude that [x] is assigned some type by the
        extended context [(Gamma, y:T11)].  To conclude that [Gamma]
        assigns a type to [x], we appeal to lemma [extend_neq], noting
        that [x] and [y] are different variables. *)

Proof.
  intros x t T Gamma H H0. generalize dependent Gamma. 
  generalize dependent T. 
  afi_cases (induction H) Case; 
         intros; try solve [inversion H0; eauto].
  Case "afi_abs".
    inversion H1; subst.
    apply IHappears_free_in in H7.
    rewrite extend_neq in H7; assumption.
Qed.

(** Next, we'll need the fact that any term [t] which is well typed in
    the empty context is closed -- that is, it has no free variables. *)

(** **** Exercise: 2 stars, optional (typable_empty__closed) *)

Ltac find_afi_invc :=
  match goal with
    | [ H : appears_free_in _ _ |- _ ] => inversion H; subst; clear H
  end.

Corollary typable_empty__closed : forall t T, 
    empty ||- t \in T  ->
    closed t.
Proof.
  unfold closed, not. intros.
  destruct (free_in_context _ _ _ _ H0 H).
  discriminate.
Qed.

(** [] *)

(** Sometimes, when we have a proof [Gamma ||- t : T], we will need to
    replace [Gamma] by a different context [Gamma'].  When is it safe
    to do this?  Intuitively, it must at least be the case that
    [Gamma'] assigns the same types as [Gamma] to all the variables
    that appear free in [t]. In fact, this is the only condition that
    is needed. *)

Lemma context_invariance : forall Gamma Gamma' t T,
     Gamma ||- t \in T  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' ||- t \in T.

(** _Proof_: By induction on the derivation of [Gamma ||- t \in T].

      - If the last rule in the derivation was [T_Var], then [t = x]
        and [Gamma x = T].  By assumption, [Gamma' x = T] as well, and
        hence [Gamma' ||- t \in T] by [T_Var].

      - If the last rule was [T_Abs], then [t = \y:T11. t12], with [T
        = T11 -> T12] and [Gamma, y:T11 ||- t12 \in T12].  The induction
        hypothesis is that for any context [Gamma''], if [Gamma,
        y:T11] and [Gamma''] assign the same types to all the free
        variables in [t12], then [t12] has type [T12] under [Gamma''].
        Let [Gamma'] be a context which agrees with [Gamma] on the
        free variables in [t]; we must show [Gamma' ||- \y:T11. t12 \in
        T11 -> T12].

        By [T_Abs], it suffices to show that [Gamma', y:T11 ||- t12 \in
        T12].  By the IH (setting [Gamma'' = Gamma', y:T11]), it
        suffices to show that [Gamma, y:T11] and [Gamma', y:T11] agree
        on all the variables that appear free in [t12].  

        Any variable occurring free in [t12] must either be [y], or
        some other variable.  [Gamma, y:T11] and [Gamma', y:T11]
        clearly agree on [y].  Otherwise, we note that any variable
        other than [y] which occurs free in [t12] also occurs free in
        [t = \y:T11. t12], and by assumption [Gamma] and [Gamma']
        agree on all such variables, and hence so do [Gamma, y:T11]
        and [Gamma', y:T11].

      - If the last rule was [T_App], then [t = t1 t2], with [Gamma ||-
        t1 \in T2 -> T] and [Gamma ||- t2 \in T2].  One induction
        hypothesis states that for all contexts [Gamma'], if [Gamma']
        agrees with [Gamma] on the free variables in [t1], then [t1]
        has type [T2 -> T] under [Gamma']; there is a similar IH for
        [t2].  We must show that [t1 t2] also has type [T] under
        [Gamma'], given the assumption that [Gamma'] agrees with
        [Gamma] on all the free variables in [t1 t2].  By [T_App], it
        suffices to show that [t1] and [t2] each have the same type
        under [Gamma'] as under [Gamma].  However, we note that all
        free variables in [t1] are also free in [t1 t2], and similarly
        for free variables in [t2]; hence the desired result follows
        by the two IHs.
*)

Proof with eauto.
  intros. 
  generalize dependent Gamma'.
  has_type_cases (induction H) Case; intros; auto.
  Case "T_Var".
    apply T_Var. rewrite <- H0...
  Case "T_Abs".
    apply T_Abs.
    apply IHhas_type. intros x1 Hafi.
    (* the only tricky step... the [Gamma'] we use to 
       instantiate is [extend Gamma x T11] *)
    unfold extend. destruct (eq_id_dec x0 x1)... 
  Case "T_App".
    apply T_App with T11...  
Qed.

(** Now we come to the conceptual heart of the proof that reduction
    preserves types -- namely, the observation that _substitution_
    preserves types.

    Formally, the so-called _Substitution Lemma_ says this: suppose we
    have a term [t] with a free variable [x], and suppose we've been
    able to assign a type [T] to [t] under the assumption that [x] has
    some type [U].  Also, suppose that we have some other term [v] and
    that we've shown that [v] has type [U].  Then, since [v] satisfies
    the assumption we made about [x] when typing [t], we should be
    able to substitute [v] for each of the occurrences of [x] in [t]
    and obtain a new term that still has type [T]. *)

(** _Lemma_: If [Gamma,x:U ||- t \in T] and [||- v \in U], then [Gamma ||-
    [x:=v]t \in T]. *)

Lemma substitution_preserves_typing : forall Gamma x U t v T,
     extend Gamma x U ||- t \in T ->
     empty ||- v \in U   ->
     Gamma ||- [x:=v]t \in T.

(** One technical subtlety in the statement of the lemma is that we
    assign [v] the type [U] in the _empty_ context -- in other words,
    we assume [v] is closed.  This assumption considerably simplifies
    the [T_Abs] case of the proof (compared to assuming [Gamma ||- v \in
    U], which would be the other reasonable assumption at this point)
    because the context invariance lemma then tells us that [v] has
    type [U] in any context at all -- we don't have to worry about
    free variables in [v] clashing with the variable being introduced
    into the context by [T_Abs].

    _Proof_: We prove, by induction on [t], that, for all [T] and
    [Gamma], if [Gamma,x:U ||- t \in T] and [||- v \in U], then [Gamma ||-
    [x:=v]t \in T].
 
      - If [t] is a variable, there are two cases to consider, depending
        on whether [t] is [x] or some other variable.

          - If [t = x], then from the fact that [Gamma, x:U ||- x \in T] we
            conclude that [U = T].  We must show that [[x:=v]x = v] has
            type [T] under [Gamma], given the assumption that [v] has
            type [U = T] under the empty context.  This follows from
            context invariance: if a closed term has type [T] in the
            empty context, it has that type in any context.

          - If [t] is some variable [y] that is not equal to [x], then
            we need only note that [y] has the same type under [Gamma,
            x:U] as under [Gamma].

      - If [t] is an abstraction [\y:T11. t12], then the IH tells us,
        for all [Gamma'] and [T'], that if [Gamma',x:U ||- t12 \in T']
        and [||- v \in U], then [Gamma' ||- [x:=v]t12 \in T'].

        The substitution in the conclusion behaves differently,
        depending on whether [x] and [y] are the same variable name.

        First, suppose [x = y].  Then, by the definition of
        substitution, [[x:=v]t = t], so we just need to show [Gamma ||-
        t \in T].  But we know [Gamma,x:U ||- t : T], and since the
        variable [y] does not appear free in [\y:T11. t12], the
        context invariance lemma yields [Gamma ||- t \in T].

        Second, suppose [x <> y].  We know [Gamma,x:U,y:T11 ||- t12 \in
        T12] by inversion of the typing relation, and [Gamma,y:T11,x:U
        ||- t12 \in T12] follows from this by the context invariance
        lemma, so the IH applies, giving us [Gamma,y:T11 ||- [x:=v]t12 \in
        T12].  By [T_Abs], [Gamma ||- \y:T11. [x:=v]t12 \in T11->T12], and
        by the definition of substitution (noting that [x <> y]),
        [Gamma ||- \y:T11. [x:=v]t12 \in T11->T12] as required.

      - If [t] is an application [t1 t2], the result follows
        straightforwardly from the definition of substitution and the
        induction hypotheses.

      - The remaining cases are similar to the application case.

    Another technical note: This proof is a rare case where an
    induction on terms, rather than typing derivations, yields a
    simpler argument.  The reason for this is that the assumption
    [extend Gamma x U ||- t \in T] is not completely generic, in
    the sense that one of the "slots" in the typing relation -- namely
    the context -- is not just a variable, and this means that Coq's
    native induction tactic does not give us the induction hypothesis
    that we want.  It is possible to work around this, but the needed
    generalization is a little tricky.  The term [t], on the other
    hand, _is_ completely generic. *)

Proof with eauto.
  intros Gamma x U t v T Ht Ht'.
  generalize dependent Gamma. generalize dependent T. 
  t_cases (induction t) Case; intros T Gamma H;
    (* in each case, we'll want to get at the derivation of H *)
    inversion H; subst; simpl...
  Case "tvar".
    rename i into y. destruct (eq_id_dec x y).
    SCase "x=y".
      subst. 
      rewrite extend_eq in H2.
      inversion H2; subst. clear H2.
                  eapply context_invariance... intros x Hcontra.
      destruct (free_in_context _ _ T empty Hcontra) as [T' HT']...
      inversion HT'.
    SCase "x<>y".
      apply T_Var. rewrite extend_neq in H2... 
  Case "tabs".
    rename i into y. apply T_Abs.
    destruct (eq_id_dec x y).
    SCase "x=y".
      eapply context_invariance...
      subst.
      intros x Hafi. unfold extend.
      destruct (eq_id_dec y x)...
    SCase "x<>y".
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold extend.
      destruct (eq_id_dec y z)...
      subst. rewrite neq_id... 
Qed.

(** The substitution lemma can be viewed as a kind of "commutation"
    property.  Intuitively, it says that substitution and typing can
    be done in either order: we can either assign types to the terms
    [t] and [v] separately (under suitable contexts) and then combine
    them using substitution, or we can substitute first and then
    assign a type to [ [x:=v] t ] -- the result is the same either
    way. *)

(* ###################################################################### *)
(** ** Main Theorem *)

(** We now have the tools we need to prove preservation: if a closed
    term [t] has type [T], and takes an evaluation step to [t'], then [t']
    is also a closed term with type [T].  In other words, the small-step
    evaluation relation preserves types.
*)

Theorem preservation : forall t t' T,
     empty ||- t \in T  ->
     t ==> t'  ->
     empty ||- t' \in T.

(** _Proof_: by induction on the derivation of [||- t \in T].

    - We can immediately rule out [T_Var], [T_Abs], [T_True], and
      [T_False] as the final rules in the derivation, since in each of
      these cases [t] cannot take a step.

    - If the last rule in the derivation was [T_App], then [t = t1
      t2].  There are three cases to consider, one for each rule that
      could have been used to show that [t1 t2] takes a step to [t'].

        - If [t1 t2] takes a step by [ST_App1], with [t1] stepping to
          [t1'], then by the IH [t1'] has the same type as [t1], and
          hence [t1' t2] has the same type as [t1 t2].

        - The [ST_App2] case is similar.

        - If [t1 t2] takes a step by [ST_AppAbs], then [t1 =
          \x:T11.t12] and [t1 t2] steps to [[x:=t2]t12]; the
          desired result now follows from the fact that substitution
          preserves types.

    - If the last rule in the derivation was [T_If], then [t = if t1
      then t2 else t3], and there are again three cases depending on
      how [t] steps.

        - If [t] steps to [t2] or [t3], the result is immediate, since
          [t2] and [t3] have the same type as [t].

        - Otherwise, [t] steps by [ST_If], and the desired conclusion
          follows directly from the induction hypothesis.
*)

Proof with eauto.
  remember (@empty ty) as Gamma. 
  intros t t' T HT. generalize dependent t'.   
  has_type_cases (induction HT) Case;
       intros t' HE; subst Gamma; subst; 
       try solve [inversion HE; subst; auto].
  Case "T_App".
    inversion HE; subst...
    (* Most of the cases are immediate by induction, 
       and [eauto] takes care of them *)
    SCase "ST_AppAbs".
      apply substitution_preserves_typing with T11...
      inversion HT1...  
Qed.

(** **** Exercise: 2 stars (subject_expansion_stlc) *)
(** An exercise in the [Types] chapter asked about the subject
    expansion property for the simple language of arithmetic and
    boolean expressions.  Does this property hold for STLC?  That is,
    is it always the case that, if [t ==> t'] and [has_type t' T],
    then [empty ||- t \in T]?  If so, prove it.  If not, give a
    counter-example not involving conditionals.

    No.  By [ST_AppAbs], we have [tapp (tabs x TBool TFalse) (tabs x TBool TFalse)
    ==> TFalse], and [empty ||- TFalse \in TBool].  However, the original
    term [tapp (tabs x TBool TFalse) (tabs x TBool TFalse)] is ill-typed.
[]
*)


(* ###################################################################### *)
(** * Type Soundness *)

(** **** Exercise: 2 stars, optional (type_soundness) *)

(** Put progress and preservation together and show that a well-typed
    term can _never_ reach a stuck state.  *)

Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ value t.

Corollary soundness : forall t t' T,
  empty ||- t \in T -> 
  t ==>* t' ->
  ~(stuck t').
Proof.
  intros t t' T Hhas_type Hmulti. unfold stuck.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti.
  - destruct (progress _ _ Hhas_type); auto.
  - apply IHHmulti; auto.
    eapply preservation; eauto.
Qed. 

(* ###################################################################### *)
(** * Uniqueness of Types *)

(** **** Exercise: 3 stars (types_unique) *)
(** Another pleasant property of the STLC is that types are
    unique: a given term (in a given context) has at most one
    type. *)
(** Formalize this statement and prove it. *)

Lemma types_unique :
  forall t Gamma T T',
    Gamma ||- t \in T ->
    Gamma ||- t \in T' ->
    T = T'.
Proof.
  intros.
  generalize dependent T'.
  induction H; intros; 
    find_hastype_invc;
    repeat find_apply_hyp_hyp;
    congruence.
Qed.

(** [] *)

(* ###################################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 1 star (progress_preservation_statement) *)
(** Without peeking, write down the progress and preservation
    theorems for the simply typed lambda-calculus. *)

(*
  progress : For all closed terms t (that is, t is well-typed in the empty
  context), t is either a value or can step to some other term t'.

  preservation : For all closed terms t of type T, if t can step to some
  other term t', then t' is also a closed term of type T.

*)

(** [] *)




(** **** Exercise: 2 stars (stlc_variation1) *)
(** Suppose we add a new term [zap] with the following reduction rule:
                         ---------                  (ST_Zap)
                         t ==> zap
and the following typing rule:
                      ----------------               (T_Zap)
                      Gamma ||- zap : T
    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]  becomes false.

      - Progress  remains true.

      - Preservation  remains true.

[]
*)

(** **** Exercise: 2 stars (stlc_variation2) *)
(** Suppose instead that we add a new term [foo] with the following reduction rules:
                       -----------------                (ST_Foo1)
                       (\x:A. x) ==> foo 

                         ------------                   (ST_Foo2)
                         foo ==> true
    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]  becomes false.
        
        [tapp (\x:TBool.x) TFalse ==> tapp foo TFalse] and
        [tapp (\x:TBool.x) TFalse ==> TFalse]

      - Progress  remains true.

      - Preservation  becomes false.  [foo] has no type.

[]
*)

(** **** Exercise: 2 stars (stlc_variation3) *)
(** Suppose instead that we remove the rule [ST_App1] from the [step]
    relation. Which of the following properties of the STLC remain
    true in the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]  remains true.

      - Progress  becomes false.

        [tapp (tif ttrue (\x:TBool.x) (\x:TBool.x)) TTrue] is not a value,
        but cannot step to another term.

      - Preservation  remains true.

[]
*)

(** **** Exercise: 2 stars, optional (stlc_variation4) *)
(** Suppose instead that we add the following new rule to the reduction relation:
            ----------------------------------        (ST_FunnyIfTrue)
            (if true then t1 else t2) ==> true
    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]  becomes false.

      - Progress  remains true.

      - Preservation  becomes false.

*)

(** **** Exercise: 2 stars, optional (stlc_variation5) *)
(** Suppose instead that we add the following new rule to the typing relation:
                 Gamma ||- t1 \in Bool->Bool->Bool
                     Gamma ||- t2 \in Bool
                 ------------------------------          (T_FunnyApp)
                    Gamma ||- t1 t2 \in Bool
    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]  remains true.

      - Progress  remains true.

      - Preservation  becomes false.

*)

(** **** Exercise: 2 stars, optional (stlc_variation6) *)
(** Suppose instead that we add the following new rule to the typing relation:
                     Gamma ||- t1 \in Bool
                     Gamma ||- t2 \in Bool
                    ---------------------               (T_FunnyApp')
                    Gamma ||- t1 t2 \in Bool
    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]  remains true.

      - Progress  becomes false.

        By [T_FunnyApp'], [empty ||- TTrue TTrue \in TBool], but this
        term is neither a value nor can step to another term.

      - Preservation  remains true.

*)

(** **** Exercise: 2 stars, optional (stlc_variation7) *)
(** Suppose we add the following new rule to the typing
    relation of the STLC:
                         ------------------- (T_FunnyAbs)
                         ||- \x:Bool.t \in Bool
    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]  

      - Progress  

      - Preservation

[]
*)

End STLCProp.

(* ###################################################################### *)
(* ###################################################################### *)
(** ** Exercise: STLC with Arithmetic *) 

(** To see how the STLC might function as the core of a real
    programming language, let's extend it with a concrete base
    type of numbers and some constants and primitive
    operators. *)

Module STLCArith.

(** To types, we add a base type of natural numbers (and remove
    booleans, for brevity) *)

Inductive ty : Type :=
  | TArrow : ty -> ty -> ty
  | TNat   : ty.

(** To terms, we add natural number constants, along with
    successor, predecessor, multiplication, and zero-testing... *)

Inductive tm : Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | tnat  : nat -> tm
  | tsucc : tm -> tm
  | tpred : tm -> tm
  | tmult : tm -> tm -> tm
  | tif0  : tm -> tm -> tm -> tm.

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar" | Case_aux c "tapp" 
  | Case_aux c "tabs" | Case_aux c "tnat" 
  | Case_aux c "tsucc" | Case_aux c "tpred"
  | Case_aux c "tmult" | Case_aux c "tif0" ].

(** **** Exercise: 4 stars (stlc_arith) *)
(** Finish formalizing the definition and properties of the STLC extended
    with arithmetic.  Specifically:

    - Copy the whole development of STLC that we went through above (from
      the definition of values through the Progress theorem), and
      paste it into the file at this point.

    - Extend the definitions of the [subst] operation and the [step]
      relation to include appropriate clauses for the arithmetic operators.

    - Extend the proofs of all the properties (up to [soundness]) of
      the original STLC to deal with the new syntactic forms.  Make
      sure Coq accepts the whole file. *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
              value (tabs x T t)
  | v_nat : forall n,
              value (tnat n).


Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
    | tvar y =>
        if eq_id_dec x y then s else t
    | tapp t1 t2 =>
        tapp ([x := s] t1) ([x := s] t2)
    | tabs y T t1 =>
        tabs y T (if eq_id_dec x y then t1 else ([x := s] t1))
    | tnat n =>
        tnat n
    | tsucc t1 =>
        tsucc ([x := s] t1)
    | tpred t1 =>
        tpred ([x := s] t1)
    | tmult t1 t2 =>
        tmult ([x := s] t1) ([x := s] t2)
    | tif0 t1 t2 t3 =>
        tif0 ([x := s] t1) ([x := s] t2) ([x := s] t3)
  end

where "'[' x ':=' s ']' t" := (subst x s t).


Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs  : forall x T t12 v2,
                   value v2 ->
                   tapp (tabs x T t12) v2 ==> [x := v2] t12
  | ST_App1    : forall t1 t1' t2,
                   t1 ==> t1' ->
                   tapp t1 t2 ==> tapp t1' t2
  | ST_App2    : forall v1 t2 t2',
                   value v1 ->
                   t2 ==> t2' ->
                   tapp v1 t2 ==> tapp v1 t2'
  | ST_SuccFin : forall n,
                   tsucc (tnat n) ==> tnat (S n)
  | ST_Succ    : forall t1 t1',
                   t1 ==> t1' ->
                   tsucc t1 ==> tsucc t1'
  | ST_PredZ   : tpred (tnat O) ==> tnat O
  | ST_PredNZ  : forall n,
                   tpred (tnat (S n)) ==> tnat n
  | ST_Pred    : forall t1 t1',
                   t1 ==> t1' ->
                   tpred t1 ==> tpred t1'
  | ST_MultFin : forall n1 n2,
                   tmult (tnat n1) (tnat n2) ==> tnat (n1 * n2)
  | ST_Mult1   : forall t1 t1' t2,
                   t1 ==> t1' ->
                   tmult t1 t2 ==> tmult t1' t2
  | ST_Mult2   : forall n1 t2 t2',
                   t2 ==> t2' ->
                   tmult (tnat n1) t2 ==> tmult (tnat n1) t2'
  | ST_IfZ     : forall t2 t3,
                   tif0 (tnat O) t2 t3 ==> t2
  | ST_IfNZ    : forall n t2 t3,
                   tif0 (tnat (S n)) t2 t3 ==> t3
  | ST_If      : forall t1 t1' t2 t3,
                   t1 ==> t1' ->
                   tif0 t1 t2 t3 ==> tif0 t1' t2 t3

where "t1 '==>' t2" := (step t1 t2).


Definition context := partial_map ty.


Reserved Notation "Gamma '||-' t '\in' T" (at level 40).
    
Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var  : forall Gamma x T,
               Gamma x = Some T ->
               Gamma ||- tvar x \in T
  | T_App  : forall T11 T12 Gamma t1 t2,
               Gamma ||- t1 \in TArrow T11 T12 -> 
               Gamma ||- t2 \in T11 -> 
               Gamma ||- tapp t1 t2 \in T12
  | T_Abs  : forall Gamma x T11 T12 t12,
               extend Gamma x T11 ||- t12 \in T12 -> 
               Gamma ||- tabs x T11 t12 \in TArrow T11 T12
  | T_Nat  : forall Gamma n,
               Gamma ||- (tnat n) \in TNat
  | T_Succ : forall Gamma t1,
               Gamma ||- t1 \in TNat ->
               Gamma ||- (tsucc t1) \in TNat
  | T_Pred : forall Gamma t1,
               Gamma ||- t1 \in TNat ->
               Gamma ||- (tpred t1) \in TNat
  | T_Mult : forall Gamma t1 t2,
               Gamma ||- t1 \in TNat ->
               Gamma ||- t2 \in TNat ->
               Gamma ||- (tmult t1 t2) \in TNat
  | T_If   : forall t1 t2 t3 T Gamma,
               Gamma ||- t1 \in TNat ->
               Gamma ||- t2 \in T ->
               Gamma ||- t3 \in T ->
               Gamma ||- tif0 t1 t2 t3 \in T

where "Gamma '||-' t '\in' T" := (has_type Gamma t T).
        
Tactic Notation "ht_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_App" 
  | Case_aux c "T_Abs" | Case_aux c "T_Nat" 
  | Case_aux c "T_Succ" | Case_aux c "T_Pred"
  | Case_aux c "T_Mult" | Case_aux c "T_If" ].


Ltac find_value_invc :=
  match goal with
    | [ H : value _ |- _ ] => inversion H; subst; clear H
  end.

Ltac find_hastype_invc :=
  match goal with
    | [ H : _ ||- (tnat _) \in TArrow _ _ |- _ ] => inversion H
    | [ H : _ ||- (tabs _ _ _) \in TNat |- _ ] => inversion H
    | [ H : _ ||- _ \in _ |- _ ] => inversion H; subst; clear H
  end.

Ltac break_exists :=
  match goal with
    | [ H : exists _, _ |- _ ] => destruct H
  end.

Ltac destruct_tif0 :=       
  match goal with
    | [ |- context [tif0 (tnat ?n) _ _] ] => destruct n
  end.

Hint Constructors value.
Hint Constructors has_type.
Hint Constructors step.

Theorem progress : 
  forall t T, 
    empty ||- t \in T ->
    value t \/ exists t', t ==> t'.
Proof with (eexists; eauto).
  intros.
  remember empty as Gamma.
  ht_cases (induction H) Case; subst; try discriminate; repeat concludes; auto.
  - right. 
    intuition; 
      try solve [repeat break_exists; eexists; eauto].
    inversion H1; subst; find_hastype_invc...
  - right.
    intuition;
      [ find_value_invc; find_hastype_invc | break_exists ];
      eexists; eauto.
  - right.
    intuition;
      [ find_value_invc; find_hastype_invc; destruct n | break_exists ];
      eexists; eauto.
  - right.
    intuition;
      repeat (find_value_invc; find_hastype_invc);
      repeat break_exists;
      eexists; eauto.
  - right.
    intuition;
      repeat (find_value_invc; find_hastype_invc);
      try destruct_tif0;
      repeat break_exists;
      eauto.
Qed.


Inductive appears_free_in : id -> tm -> Prop :=
  | afi_var   : forall x, 
                  appears_free_in x (tvar x)
  | afi_app1  : forall x t1 t2,
                  appears_free_in x t1 ->
                  appears_free_in x (tapp t1 t2)
  | afi_app2  : forall x t1 t2,
                  appears_free_in x t2 ->
                  appears_free_in x (tapp t1 t2)
  | afi_abs   : forall x y t1 T,
                  y <> x ->
                  appears_free_in x t1 ->
                  appears_free_in x (tabs y T t1)
  | afi_succ  : forall x t1,
                  appears_free_in x t1 ->
                  appears_free_in x (tsucc t1)
  | afi_pred  : forall x t1,
                  appears_free_in x t1 ->
                  appears_free_in x (tpred t1)
  | afi_mult1 : forall x t1 t2,
                  appears_free_in x t1 ->
                  appears_free_in x (tmult t1 t2)
  | afi_mult2 : forall x t1 t2,
                  appears_free_in x t2 ->
                  appears_free_in x (tmult t1 t2)
  | aif_if1   : forall x t1 t2 t3,
                  appears_free_in x t1 ->
                  appears_free_in x (tif0 t1 t2 t3)
  | aif_if2   : forall x t1 t2 t3,
                  appears_free_in x t2 ->
                  appears_free_in x (tif0 t1 t2 t3)
  | aif_if3   : forall x t1 t2 t3,
                  appears_free_in x t3 ->
                  appears_free_in x (tif0 t1 t2 t3).

Definition closed (t : tm) :=
  forall x, 
    ~ appears_free_in x t.

Lemma free_in_context :
  forall x t Gamma T,
    appears_free_in x t ->
    Gamma ||- t \in T ->
    exists T', Gamma x = Some T'.
Proof with eauto.
  intros.
  generalize dependent Gamma.
  generalize dependent T.
  induction H; 
    intros; 
    find_hastype_invc...
  find_apply_hyp_hyp.
  break_exists.
  rewrite extend_neq in H1...
Qed.

Corollary typable_empty__closed :
  forall t T,
    empty ||- t \in T ->
    closed t.
Proof.           
  unfold closed, not. intros.
  destruct (free_in_context _ _ _ _ H0 H).
  discriminate.
Qed.

Hint Constructors appears_free_in.

Lemma context_invariance : forall Gamma Gamma' t T,
     Gamma ||- t \in T  ->
     (forall x, appears_free_in x t -> Gamma' x = Gamma x) ->
     Gamma' ||- t \in T.
Proof with eauto.
  intros.
  generalize dependent Gamma'.
  induction H; intros; auto.
  - apply T_Var.
    rewrite <- H...
  - eapply T_App...
  - apply T_Abs, IHhas_type.
    intros.
    destruct (eq_id_dec x x0); subst.
    + repeat rewrite extend_eq; auto.
    + repeat rewrite extend_neq; auto.
Qed.      
        
Hint Unfold closed.
Hint Unfold not.

Axiom functional_extensionality :
  forall (A B : Type)
         (f g : A -> B),
    (forall x, f x = g x) ->
    f = g.
      
Lemma extend_permute :
  forall (Gamma : context) T U x y z,
    x <> y ->
    extend (extend Gamma x T) y U z = extend (extend Gamma y U) x T z.
Proof.
  admit.
Qed.

Lemma substitution_preserves_typing :
  forall Gamma x U T t v,
    extend Gamma x U ||- t \in T ->
    empty ||- v \in U ->
    Gamma ||- [x := v] t \in T.
Proof with eauto.
  intros.
  remember (extend Gamma x U) as G.
  generalize dependent v.
  generalize dependent U.
  generalize dependent x.
  generalize dependent Gamma.
  induction H; intros; simpl in *; subst...
  - break_match; subst.
    + rewrite extend_eq in H; inversion H; subst.
      eapply context_invariance...
      intros.
      apply typable_empty__closed in H0.
      exfalso.
      unfold closed in *.
      unfold not in *.
      eapply H0...
    + rewrite extend_neq in H; auto.
  - apply T_Abs.
    break_match; subst.
    + eapply context_invariance...
      intros.
      rewrite extend_shadow...
    + eapply IHhas_type...
      apply functional_extensionality.
      intros.
      apply extend_permute...
Qed.

Theorem preservation :
  forall t t' T,
    empty ||- t \in T ->
    t ==> t' ->
    empty ||- t' \in T.
Proof with eauto.
  intros.
  generalize dependent T.
  induction H0; intros; find_hastype_invc; eauto.
  eapply substitution_preserves_typing...
  inversion H4; subst...
Qed.



  

(** [] *)

End STLCArith.

(* $Date: 2014-04-23 09:37:37 -0400 (Wed, 23 Apr 2014) $ *)

