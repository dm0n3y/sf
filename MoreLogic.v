(** * More Logic *)

Require Export "Prop".

(* ############################################################ *)
(** * Existential Quantification *)

(** Another critical logical connective is _existential
    quantification_.  We can express it with the following
    definition: *)

Inductive ex (X:Type) (P : X->Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.

(** That is, [ex] is a family of propositions indexed by a type [X]
    and a property [P] over [X].  In order to give evidence for the
    assertion "there exists an [x] for which the property [P] holds"
    we must actually name a _witness_ -- a specific value [x] -- and
    then give evidence for [P x], i.e., evidence that [x] has the
    property [P]. 

*)


(** *** *)
(** Coq's [Notation] facility can be used to introduce more
    familiar notation for writing existentially quantified
    propositions, exactly parallel to the built-in syntax for
    universally quantified propositions.  Instead of writing [ex nat
    ev] to express the proposition that there exists some number that
    is even, for example, we can write [exists x:nat, ev x].  (It is
    not necessary to understand exactly how the [Notation] definition
    works.) *)

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

(** *** *)
(** We can use the usual set of tactics for
    manipulating existentials.  For example, to prove an
    existential, we can [apply] the constructor [ex_intro].  Since the
    premise of [ex_intro] involves a variable ([witness]) that does
    not appear in its conclusion, we need to explicitly give its value
    when we use [apply]. *)

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (witness:=2). 
  reflexivity.  Qed.

(** Note that we have to explicitly give the witness. *)

(** *** *)
(** Or, instead of writing [apply ex_intro with (witness:=e)] all the
    time, we can use the convenient shorthand [exists e], which means
    the same thing. *)

Example exists_example_1' : exists n, n + (n * n) = 6.
Proof.
  exists 2. 
  reflexivity.  Qed.

(** *** *)
(** Conversely, if we have an existential hypothesis in the
    context, we can eliminate it with [inversion].  Note the use
    of the [as...] pattern to name the variable that Coq
    introduces to name the witness value and get evidence that
    the hypothesis holds for the witness.  (If we don't
    explicitly choose one, Coq will just call it [witness], which
    makes proofs confusing.) *)
  
Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n H.
  inversion H as [m Hm]. 
  exists (2 + m).  
  apply Hm.  Qed. 


(** Here is another example of how to work with existentials. *)
Lemma exists_example_3 : 
  exists (n:nat), even n /\ beautiful n.
Proof.
(* WORKED IN CLASS *)
  exists 8.
  split.
  unfold even. simpl. reflexivity.
  apply b_sum with (n:=3) (m:=5).
  apply b_3. apply b_5.
Qed.

(** **** Exercise: 1 star, optional (english_exists) *)
(** In English, what does the proposition 
      ex nat (fun n => beautiful (S n))
]] 
    mean? *)

(* There exists a natural number [n] such that [S n] is beautiful. *)

(** **** Exercise: 1 star (dist_not_exists) *)
(** Prove that "[P] holds for all [x]" implies "there is no [x] for
    which [P] does not hold." *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof. 
  unfold not.
  intros.
  destruct H0 as [x H0].
  apply H0.
  apply H.
Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (not_exists_dist) *)
(** (The other direction of this theorem requires the classical "law
    of the excluded middle".) *)

Lemma excluded_middle__classic : 
  excluded_middle -> classic.
Proof.
  intros.
  apply peirce__classic,
        implies_to_or__peirce,
        de_morgan__implies_to_or,
        excluded_middle__de_morgan.
  assumption.
Qed.

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  unfold not.
  intros H X P H0.
  destruct (H (forall x, P x)).
  - assumption.
  - unfold not in *.
    apply ex_falso_quodlibet.
    apply H0.
    destruct (H ((exists x, P x) -> False)).
    + apply ex_falso_quodlibet.
      apply H0.
      Admitted.

(** [] *)

(** **** Exercise: 2 stars (dist_exists_or) *)
(** Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  split.
  - intros.
    destruct H as [x H].
    destruct H.
    + apply or_introl.
      exists x.
      assumption.
    + apply or_intror.
      exists x.
      assumption.
  - intros.
    destruct H; destruct H.
    + exists witness.
      apply or_introl.
      assumption.
    + exists witness.
      apply or_intror.
      assumption.
Qed.

(** [] *)

(* ###################################################### *)
(** * Evidence-carrying booleans. *)

(** So far we've seen two different forms of equality predicates:
[eq], which produces a [Prop], and
the type-specific forms, like [beq_nat], that produce [boolean]
values.  The former are more convenient to reason about, but
we've relied on the latter to let us use equality tests 
in _computations_.  While it is straightforward to write lemmas
(e.g. [beq_nat_true] and [beq_nat_false]) that connect the two forms,
using these lemmas quickly gets tedious. 
*)

(** *** *)
(** 
It turns out that we can get the benefits of both forms at once 
by using a construct called [sumbool]. *)

Inductive sumbool (A B : Prop) : Set :=
 | left : A -> sumbool A B 
 | right : B -> sumbool A B.

Notation "{ A } + { B }" :=  (sumbool A B) : type_scope.

(** Think of [sumbool] as being like the [boolean] type, but instead
of its values being just [true] and [false], they carry _evidence_
of truth or falsity. This means that when we [destruct] them, we
are left with the relevant evidence as a hypothesis -- just as with [or].
(In fact, the definition of [sumbool] is almost the same as for [or].
The only difference is that values of [sumbool] are declared to be in
[Set] rather than in [Prop]; this is a technical distinction 
that allows us to compute with them.) *) 

(** *** *)

(** Here's how we can define a [sumbool] for equality on [nat]s *)

Theorem eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  (* WORKED IN CLASS *)
  intros n.
  induction n as [|n'].
  Case "n = 0".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      left. reflexivity.
    SCase "m = S m'".
      right. intros contra. inversion contra.
  Case "n = S n'".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      right. intros contra. inversion contra.
    SCase "m = S m'". 
      destruct IHn' with (m := m') as [eq | neq].
      left. apply f_equal.  apply eq.
      right. intros Heq. inversion Heq as [Heq']. apply neq. apply Heq'.
Defined. 
  
(** Read as a theorem, this says that equality on [nat]s is decidable:
that is, given two [nat] values, we can always produce either 
evidence that they are equal or evidence that they are not.
Read computationally, [eq_nat_dec] takes two [nat] values and returns
a [sumbool] constructed with [left] if they are equal and [right] 
if they are not; this result can be tested with a [match] or, better,
with an [if-then-else], just like a regular [boolean]. 
(Notice that we ended this proof with [Defined] rather than [Qed]. 
The only difference this makes is that the proof becomes _transparent_,
meaning that its definition is available when Coq tries to do reductions,
which is important for the computational interpretation.)
*) 

(** *** *)
(** 
Here's a simple example illustrating the advantages of the [sumbool] form. *)

Definition override' {X: Type} (f: nat->X) (k:nat) (x:X) : nat->X:=
  fun (k':nat) => if eq_nat_dec k k' then x else f k'.

Theorem override_same' : forall (X:Type) x1 k1 k2 (f : nat->X),
  f k1 = x1 -> 
  (override' f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 k2 f. intros Hx1.
  unfold override'.
  destruct (eq_nat_dec k1 k2).   (* observe what appears as a hypothesis *)
  Case "k1 = k2".
    rewrite <- e.
    symmetry. apply Hx1.
  Case "k1 <> k2". 
    reflexivity.  Qed.

(** Compare this to the more laborious proof (in MoreCoq.v) for the 
   version of [override] defined using [beq_nat], where we had to
   use the auxiliary lemma [beq_nat_true] to convert a fact about booleans
   to a Prop. *)


(** **** Exercise: 1 star (override_shadow') *)
Theorem override_shadow' : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  (override' (override' f k1 x2) k1 x1) k2 = (override' f k1 x1) k2.
Proof.
  intros.
  unfold override'.
  destruct (eq_nat_dec k1 k2); reflexivity.
Qed.

(** [] *)






(* ####################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars (all_forallb) *)
(** Inductively define a property [all] of lists, parameterized by a
    type [X] and a property [P : X -> Prop], such that [all X P l]
    asserts that [P] is true for every element of the list [l]. *)

Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
  | all_nil  : all X P nil
  | all_cons : forall x l, P x -> all X P l -> all X P (x :: l).

(** Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Poly]: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

(** Using the property [all], write down a specification for [forallb],
    and prove that it satisfies the specification. Try to make your 
    specification as precise as possible.

    Are there any important properties of the function [forallb] which
    are not captured by your specification? *)

Lemma forallb_spec : 
  forall (X : Type) (l : list X) (test : X -> bool),
    forallb test l = true <-> all X (fun x => test x = true) l.
Proof.
  split.
  - induction l; intros.
    + apply all_nil.
    + apply all_cons; simpl in *.
      * destruct (test x); auto; discriminate.
      * apply IHl.
        destruct (test x); auto; discriminate.
  - intros.
    induction H.
    + reflexivity.
    + simpl in *.
      rewrite H.
      assumption.
Qed.

(** [] *)

(** **** Exercise: 4 stars, advanced (filter_challenge) *)
(** One of the main purposes of Coq is to prove that programs match
    their specifications.  To this end, let's prove that our
    definition of [filter] matches a specification.  Here is the
    specification, written out informally in English.

    Suppose we have a set [X], a function [test: X->bool], and a list
    [l] of type [list X].  Suppose further that [l] is an "in-order
    merge" of two lists, [l1] and [l2], such that every item in [l1]
    satisfies [test] and no item in [l2] satisfies test.  Then [filter
    test l = l1].

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example, 
    [1,4,6,2,3]
    is an in-order merge of
    [1,6,2]
    and
    [4,3].
    Your job is to translate this specification into a Coq theorem and
    prove it.  (Hint: You'll need to begin by defining what it means
    for one list to be a merge of two others.  Do this with an
    inductive relation, not a [Fixpoint].)  *)

Inductive iom {X : Type} : list X -> list X -> list X -> Prop :=
  | iom_nil   : iom [] [] []
  | iom_left  : forall l l1 l2 x, iom l l1 l2 -> iom (x :: l) (x :: l1) l2
  | iom_right : forall l l1 l2 x, iom l l1 l2 -> iom (x :: l) l1 (x :: l2).

Theorem filter_spec : 
  forall (X : Type) (l l1 l2 : list X) (test : X -> bool),
    iom l l1 l2 ->
      all X (fun x => test x = true) l1 ->
        all X (fun x => test x = false) l2 ->
          filter test l = l1.
Proof.
  induction 1; intros.
  - reflexivity.
  - inversion H0; subst.
    simpl in *.
    rewrite H4.
    f_equal.
    apply IHiom; assumption.
  - inversion H1; subst.
    simpl in *.
    rewrite H4.
    apply IHiom; assumption.
Qed.

(** [] *)

(** **** Exercise: 5 stars, advanced, optional (filter_challenge_2) *)
(** A different way to formally characterize the behavior of [filter]
    goes like this: Among all subsequences of [l] with the property
    that [test] evaluates to [true] on all their members, [filter test
    l] is the longest.  Express this claim formally and prove it. *)

Theorem filter_max_length : 
  forall (X : Type) (l l' : list X) (test : X -> bool),
    subseq l' l ->
      all X (fun x => test x = true) l' ->
        length l' <= length (filter test l).
Proof.
  induction 1; intros.
  - apply Le.le_0_n.
  - inversion H0; subst.
    + apply Le.le_0_n.
    + simpl in *.
      destruct (test x).
      * simpl in *.
        apply le_S, IHsubseq, all_cons; assumption.
      * apply IHsubseq, all_cons; assumption.
  - inversion H0; subst.
    simpl in *.
    rewrite H3.
    simpl in *.
    apply Le.le_n_S, IHsubseq; assumption.
Qed.

(** [] *)

(** **** Exercise: 4 stars, advanced (no_repeats) *)
(** The following inductively defined proposition... *)

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

(** ...gives us a precise way of saying that a value [a] appears at
    least once as a member of a list [l]. 

    Here's a pair of warm-ups about [appears_in].
*)

Lemma appears_in_app : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
  induction xs; intros.
  - simpl in *.
    apply or_intror; assumption.
  - inversion H; subst.
    + apply or_introl, ai_here.
    + destruct (IHxs ys x0).
      * assumption.
      * apply or_introl, ai_later; assumption.
      * apply or_intror; assumption.
Qed.

Lemma app_appears_in : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  destruct 1.
  - induction H; simpl in *.
    + apply ai_here.
    + apply ai_later; assumption.
  - induction xs; simpl in *.
    + assumption.
    + apply ai_later; assumption.
Qed.

(** Now use [appears_in] to define a proposition [disjoint X l1 l2],
    which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in common. *)

Inductive disjoint (X : Type) : list X -> list X -> Prop :=
  | disj_nil    : disjoint X [] []
  | disj_cons_l : forall (l1 l2 : list X) (x : X),
                    ~ appears_in x l2 -> 
                      disjoint X l1 l2 -> disjoint X (x :: l1) l2
  | disj_cons_r : forall (l1 l2 : list X) (x : X),
                    ~ appears_in x l1 -> 
                      disjoint X l1 l2 -> disjoint X l1 (x :: l2).

(** Next, use [appears_in] to define an inductive proposition
    [no_repeats X l], which should be provable exactly when [l] is a
    list (with elements of type [X]) where every member is different
    from every other.  For example, [no_repeats nat [1,2,3,4]] and
    [no_repeats bool []] should be provable, while [no_repeats nat
    [1,2,1]] and [no_repeats bool [true,true]] should not be.  *)

Inductive no_repeats (X : Type) : list X -> Prop :=
  | nr_nil  : no_repeats X []
  | nr_cons : forall l x, 
                ~(appears_in x l) -> no_repeats X l -> no_repeats X (x :: l).

(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [no_repeats] and [++] (list append).  *)


Lemma disjoint_comm : 
  forall (X : Type) (l1 l2 : list X),
    disjoint X l1 l2 -> disjoint X l2 l1.
Proof.
  induction 1.
  - apply disj_nil.
  - apply disj_cons_r; assumption.
  - apply disj_cons_l; assumption.
Qed.

Lemma disjoint_cons : 
  forall (X : Type) (l1 l2 : list X) (x : X),
    disjoint X (x :: l1) l2 -> ~(appears_in x l2) /\ disjoint X l1 l2.
Proof.
  intros.
  remember (x :: l1) as l.
  induction H; intros; subst.
  - discriminate.
  - inversion Heql; subst.
    split; assumption.
  - destruct (IHdisjoint (eq_refl (x :: l1))); auto.
    split.
    + unfold not. intros.
      Hint Constructors appears_in.
      inversion H3; subst; auto.
    + apply disj_cons_r; unfold not; auto.
Qed.
      
Theorem no_repeats_app : 
  forall (X : Type) (l1 : list X),
    no_repeats X l1 ->
      forall (l2 : list X),
        no_repeats X l2 ->
          disjoint X l1 l2 ->
            no_repeats X (l1 ++ l2).
Proof.
  induction 1; intros; simpl in *.
  - assumption.
  - apply nr_cons.
    + unfold not. intros.
      destruct (appears_in_app X l l2 x H3).
      * auto.
      * destruct (disjoint_cons X l l2 x H2); auto.
    + apply IHno_repeats.
      * assumption.
      * apply disjoint_cons with (x := x) (l1 := l) (l2 := l2).
        assumption.
Qed.

(*
I initially tried to define disjoint as below, and did not get anywhere.
The lesson here is that I should inductively define things such that
every element/prop has a unique path from a base element.  The problem
with the definition below is that I can have arbitrarily many disj_comm
constructors applied to an element and still get the same proposition back.
A more mechanical perspective is that assuming a prop was last constructed
by disj_comm, we are given very little information that was needed to
construct the statement.  
*)
   
Inductive disjoint' (X : Type) : list X -> list X -> Prop :=
  | disj_nil' : forall l, disjoint' X [] l
  | disj_cons : forall l1 l2 x, 
                  ~(appears_in x l1) -> disjoint' X l1 l2 -> disjoint' X l1 (x :: l2)
  | disj_comm : forall l1 l2, disjoint' X l1 l2 -> disjoint' X l2 l1.

(** [] *)


(** **** Exercise: 3 stars (nostutter) *)
(** Formulating inductive definitions of predicates is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help at all (except from your study group partner, if
    you have one).

    We say that a list of numbers "stutters" if it repeats the same
    number consecutively.  The predicate "[nostutter mylist]" means
    that [mylist] does not stutter.  Formulate an inductive definition
    for [nostutter].  (This is different from the [no_repeats]
    predicate in the exercise above; the sequence [1,4,1] repeats but
    does not stutter.) *)

Inductive nostutter:  list nat -> Prop :=
  | ns_nil    : nostutter []
  | ns_single : forall n, nostutter [n]
  | ns_cons   : forall n m l, 
                  n <> m -> nostutter (m :: l) -> nostutter (n :: m :: l). 

(** Make sure each of these tests succeeds, but you are free
    to change the proof if the given one doesn't work for you.
    Your definition might be different from mine and still correct,
    in which case the examples might need a different proof.
   
    The suggested proofs for the examples (in comments) use a number
    of tactics we haven't talked about, to try to make them robust
    with respect to different possible ways of defining [nostutter].
    You should be able to just uncomment and use them as-is, but if
    you prefer you can also prove each example with more basic
    tactics.  *)

Example test_nostutter_1:      nostutter [3;1;4;1;5;6].
Proof. repeat constructor; apply beq_nat_false; auto. Qed.

Example test_nostutter_2:  nostutter [].
Proof. repeat constructor; apply beq_nat_false; auto. Qed.

Example test_nostutter_3:  nostutter [5].
Proof. repeat constructor; apply beq_nat_false; auto. Qed.

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
Proof. intro.
  repeat match goal with 
    h: nostutter _ |- _ => inversion h; clear h; subst 
  end.
  contradiction H1; auto. Qed.

(** [] *)

(** **** Exercise: 4 stars, advanced (pigeonhole principle) *)
(** The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some 
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First a pair of useful lemmas (we already proved these for lists
    of naturals, but not for arbitrary lists). *)

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2. 
Proof. 
  induction l1; intros; simpl in *; auto.
Qed.

Lemma appears_in_app_split : forall (X:Type) (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  induction 1.
  - exists [], l.
    reflexivity.
  - destruct IHappears_in as [l1 [l2 IHappears_in]].
    exists (b :: l1), l2.
    rewrite IHappears_in.
    reflexivity.
Qed.

(** Now define a predicate [repeats] (analogous to [no_repeats] in the
   exercise above), such that [repeats X l] asserts that [l] contains
   at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  | repeats_new : forall x l, appears_in x l -> repeats (x :: l)
  | repeats_old : forall x l, repeats l -> repeats (x :: l).

(*
  | repeats_pair : forall x l, repeats (x :: (snoc l x))
  | repeats_cons : forall x l, repeats l -> repeats (x :: l)
  | repeats_snoc : forall x l, repeats l -> repeats (snoc l x).
*)

(** Now here's a way to formalize the pigeonhole principle. List [l2]
    represents a list of pigeonhole labels, and list [l1] represents
    the labels assigned to a list of items: if there are more items
    than labels, at least two items must have the same label.  This
    proof is much easier if you use the [excluded_middle] hypothesis
    to show that [appears_in] is decidable, i.e. [forall x
    l, (appears_in x l) \/ ~ (appears_in x l)].  However, it is also
    possible to make the proof go through _without_ assuming that
    [appears_in] is decidable; if you can manage to do this, you will
    not need the [excluded_middle] hypothesis. *)

Theorem appears_before_cons : forall (X : Type) x y (xs : list X),
  appears_in x (y :: xs) -> x <> y -> appears_in x xs.
Proof.
  intros.
  inversion H; subst.
  - apply ex_falso_quodlibet, H0.
    reflexivity.
  - assumption.
Qed.

Theorem pigeonhole_principle: forall (X:Type) (l1 l2:list X), 
   excluded_middle -> 
   (forall x, appears_in x l1 -> appears_in x l2) -> 
   length l2 < length l1 -> 
   repeats l1.  
Proof.
  induction l1; intros; simpl in *.
  - inversion H1.
  - unfold excluded_middle in *.
    destruct (H (appears_in x l1)).
    + apply repeats_new, H2.      
    + destruct (appears_in_app_split X x l2 (H0 x (ai_here x l1))) 
        as [l1' [l2' Hl2]]; subst.
      apply repeats_old, IHl1 with (l2 := l1' ++ l2').
      * assumption.
      * {
          intros.
          destruct (H (x0 = x)); subst.
          - contradiction H2.
          - apply app_appears_in.
            pose proof (H0 x0 (ai_later x0 x l1 H3)).
            destruct (appears_in_app X l1' (x :: l2') x0 H5).
            + left. assumption.
            + right.
              apply appears_before_cons with (y := x); assumption.
        }
      * rewrite app_length in *.
        simpl in *.
        rewrite plus_comm in *.
        simpl in *.
        unfold lt in *.
        apply Le.le_S_n.
        assumption.
Qed.            

(** [] *)

(* FILL IN HERE *)


(* $Date: 2014-02-22 09:43:41 -0500 (Sat, 22 Feb 2014) $ *)
