
(* An import of LibExec from TLC *)

Set Implicit Arguments.
From TLC Require Import LibTactics.
From TLC Require Export LibBool LibLogic LibReflect.
Generalizable Variable P.

Hint Rewrite true_eq_isTrue_eq false_eq_isTrue_eq : rew_istrue.

(* ********************************************************************** *)
(** * Decidable predicates *)

(** [Decidable P] asserts that there exists a boolean
    value indicating whether [P] is true. The definition
    is interesting when this boolean is computable and
    can lead to code extraction. *)

Class Decidable (P:Prop) := decidable_make {
  decide : bool;
  decide_spec : decide = isTrue P }.
Hint Rewrite @decide_spec : rew_refl.
Arguments decide P {Decidable}.

(** Notation [ifb P then x else y] can be used for
    testing a proposition [P] for which there exists an
    instance of [Decidable P]. *)
Notation "'ifb' P 'then' v1 'else' v2" :=
  (if decide P then v1 else v2)
  (at level 200, right associativity) : type_scope.

(** In classical logic, any proposition is decidable; of course,
    we do not want to use this lemma as an instance because
    it cannot be extracted to executable code. *)
Lemma prop_decidable : forall (P:Prop), Decidable P.
Proof using. intros. applys~ decidable_make (isTrue P). Qed.

(** In constructive logic, any proposition with a proof of
    that is constructively true or false is decidable. *)
Definition sumbool_decidable : forall (P:Prop),
  {P}+{~P} -> Decidable P.
Proof using.
  introv H. applys decidable_make
    (match H with left _ => true | right _ => false end).
  rewrite isTrue_eq_if. destruct H; case_if; tryfalse; auto.
Defined.

Definition decidable_sumbool : forall P : Prop,
    Decidable P -> {P}+{~P}.
Proof using.
  introv D. destruct (decide P) eqn: H; rewrite decide_spec in H.
  - rewrite* isTrue_eq_true_eq in H.
  - rewrite* isTrue_eq_false_eq in H.
Defined.

(** [sumbool_decidable] and [decidable_sumbool] just wrap their
    property as expected. *)
Lemma sumbool_decidable_decidable_sumbool : forall P (d : {P}+{~P}),
  decidable_sumbool (sumbool_decidable d) = d.
Proof using.
  introv. unfolds.
  asserts R1: (forall (d : bool) B C C1 C2,
    d ->
    (if d as b return (d = b -> B) then
      fun H => C1 H
    else fun H => C2 H) eq_refl = C ->
    exists E, C1 E = C).
   clear. introv D Eq. destruct d; tryfalse. eexists. apply Eq.
  lets R1': (rm R1) (@decide P (sumbool_decidable d)).
  asserts R2: (forall (d : bool) B C C1 C2,
    !d ->
    (if d as b return (d = b -> B) then
      fun H => C1 H
    else fun H => C2 H) eq_refl = C ->
    exists E, C2 E = C).
   clear. introv D Eq. destruct d; tryfalse. eexists. apply Eq.
  lets R2': (rm R2) (@decide P (sumbool_decidable d)).
  unfold sumbool_decidable. case_if as I.
  - forwards (E&Eq): R1'.
    + rewrite decide_spec. rew_istrue~.
    + reflexivity.
    + rewrite <- Eq. fequals.
  - forwards (E&Eq): R2'.
    + rewrite decide_spec. rew_istrue~.
    + reflexivity.
    + rewrite <- Eq. fequals.
Qed.

Global Instance Decidable_impl : forall A B : Prop,
    Decidable A -> Decidable B -> Decidable (A -> B).
  introv (da&Ha) (db&Hb).
  destruct da; destruct db; rew_istrue in *;
    solve [
      apply decidable_make with true; rew_istrue*
    | apply decidable_make with false; rew_istrue* ].
Defined.

Global Instance Decidable_equiv : forall A B : Prop,
    (A <-> B) -> Decidable A -> Decidable B.
  introv E. apply prop_ext in E. substs~.
Defined.

(** Extending the [case_if] tactic to support [if decide] *)
Lemma Decidable_dec : forall (P:Prop) {H: Decidable P} (A:Type) (x y:A),
  exists (Q : {P}+{~P}),
  (if decide P then x else y) = (if Q then x else y).
Proof using.
  intros. exists (classicT P).
  rewrite decide_spec.
  case_if as C; case_if as C';
  first [ rewrite isTrue_True in C
        | rewrite isTrue_False in C
        | idtac ]; autos*; false*.
Qed.

Ltac case_if_on_tactic_core E Eq ::=
  match E with
  | @decide ?P ?M =>
      let Q := fresh in let Eq := fresh in
      forwards (Q&Eq): (@Decidable_dec P M);
      rewrite Eq in *; clear Eq; destruct Q
  | _ =>
    match type of E with
    | {_}+{_} => destruct E as [Eq|Eq]; try subst_hyp Eq
    | _ => let X := fresh in
           sets_eq <- X Eq: E;
           destruct X
    end
  end.

(** Rewriting lemma *)
Lemma istrue_decide : forall `{Decidable P},
  istrue (decide P) = P.
Proof using. intros. rewrite decide_spec. rew_istrue~. Qed.

Lemma decide_prove : forall `{Decidable P},
  P -> istrue (decide P).
Proof using. intros. rewrite~ istrue_decide. Qed.

Lemma decide_def : forall `{Decidable P},
  (decide P) = (If P then true else false).
Proof using. intros. rewrite decide_spec. rewrite isTrue_eq_if. case_if*. Qed.

Lemma decide_cases : forall `{Decidable P},
  (P /\ decide P = true) \/ (~ P /\ decide P = false).
Proof using. intros. rewrite decide_spec. rewrite isTrue_eq_if. case_if*. Qed.

(** Dedicability instances *)
Global Instance true_decidable : Decidable True.
Proof using. applys decidable_make true. rew_istrue~. Qed.

Global Instance false_decidable : Decidable False.
Proof using. applys decidable_make false. rew_istrue~. Qed.

Global Instance bool_decidable : forall (b : bool), Decidable (b).
Proof using. introv. applys (@decidable_make (istrue b) b). rew_isTrue~. Qed.

Global Instance not_decidable : forall (P : Prop),
  Decidable P -> Decidable (~ P).
Proof using.
  (* --TODO: cleanup proof *)
  introv [dec spec]. applys decidable_make (neg dec).
  rew_isTrue. rewrite~ spec.
Qed.

Global Instance or_decidable : forall (P Q : Prop),
  Decidable P -> Decidable Q ->
  Decidable (P \/ Q).
Proof using.
  intros. applys decidable_make (decide P || decide Q).
  rew_isTrue. repeat rewrite~ @decide_spec.
Qed.

Global Instance and_decidable : forall P Q,
  Decidable P -> Decidable Q ->
  Decidable (P /\ Q).
Proof using.
  intros. applys decidable_make (decide P && decide Q).
  rew_isTrue. repeat rewrite~ @decide_spec.
Qed.

Global Instance If_dec : forall P Q R,
  Decidable P -> Decidable Q -> Decidable R ->
  Decidable (If P then Q else R).
Proof using.
  intros. applys decidable_make (if decide P then decide Q else decide R).
  rewrite decide_spec. rew_isTrue~. repeat rewrite~ @decide_spec.
Qed.

(* ********************************************************************** *)
(** * Comparable types *)

(** [Comparable A] asserts that there exists a decidable
    equality over values of type [A] *)
Class Comparable (A:Type) := make_comparable {
  comparable : forall (x y:A), Decidable (x = y) }.

#[global]
Hint Resolve @comparable : typeclass_instances.

(** In classical logic, any type is comparable; of course,
    we do not want to use this lemma as an instance because
    it cannot be extracted to executable code. *)
Lemma type_comparable : forall (A:Type), Comparable A.
Proof using. constructor. intros. applys~ prop_decidable. Qed.

(** [Comparable] can be proved by exhibiting a boolean
    comparison function *)
Lemma comparable_beq : forall A (f:A->A->bool),
  (forall x y, (istrue (f x y)) <-> (x = y)) ->
  Comparable A.
Proof using.
  introv H. constructors. intros.
  applys decidable_make (f x y).
  rewrite isTrue_eq_if. extens.
  rewrite H. rewrite <- isTrue_eq_if. rew_istrue~. iff~.
Qed.

(** [Comparable] can be proved by exhibiting a decidability
    result in the form of a strong sum *)
(* --TODO: rename dec_to_comparable *)
Lemma comparable_of_dec : forall (A:Type),
  (forall x y : A, {x = y} + {x <> y}) ->
  Comparable A.
Proof using.
  introv H. constructors. intros.
  applys decidable_make (if H x y then true else false).
  destruct (H x y); rew_istrue~.
Qed.

(** Comparison for booleans *)
Instance bool_comparable : Comparable bool.
Proof using.
  applys (comparable_beq Bool.eqb).
  destruct x; destruct y; simpl; auto_false*.
Qed.

Global Instance prop_eq_decidable : forall P Q,
  Decidable P -> Decidable Q ->
  Decidable (P = Q).
Proof using.
  intros. applys decidable_make (decide (decide P = decide Q)).
  extens. repeat rewrite decide_spec. rew_istrue.
  iff E.
    do 2 rewrite isTrue_eq_if in E.
     extens. case_if; case_if; auto_false*.
    subst*.
Qed.

(**************************************************************)
(** * Computable epsilon operator *)

(** [Pickable P] asserts the existence of computable witness
    of a value that satisfies the predicate [P]. When an
    instance of [Pickable P] can be derived using the typeclass
    mechanism, one may write [pick P] to denote an arbitrary
    value that satisfies the predicate P. This operation is
    typically useful for extraction, in order to associate
    computable values to predicates. *)

Class Pickable (A : Type) (P : A -> Prop) := pickable_make {
  pick : A;
  pick_spec : (exists a, P a) -> P pick }.
Arguments pick [A] P {Pickable}.

(** Instances of pickable *)
Global Instance eq_pickable : forall (A : Type) (a : A), (* --TODO: use `{Inhab A} *)
  Pickable (eq a).
Proof using.
  (* --TODO: clean up proof *)
  introv. applys pickable_make a.
  intro. reflexivity.
Qed.

(**************************************************************)
(** * Computable epsilon operator *)

Require Import Lia String.
From TLC Require Import LibInt.

(* ---------------------------------------------------------------------- *)
(** ** Comparison *)

Fixpoint nat_compare (x y : nat) :=
  match x, y with
  | O, O => true
  | S x', S y' => nat_compare x' y'
  | _, _ => false
  end.

Instance nat_comparable : Comparable nat.
Proof using.
  applys (comparable_beq nat_compare).
  induction x; destruct y; simpl.
  autos*.
  auto_false.
  auto_false.
  asserts_rewrite ((S x = S y) = (x = y)).
    extens. iff; lia.
  autos*.
Defined.

Instance string_comparable : Comparable string.
Proof using. applys comparable_of_dec string_dec. Defined.

(* ********************************************************************** *)
(** * Comparable *)
(**************************************************************)

(** ** Extension to Stdlib comparisons *)
(* --TODO: remove dependency on stdlib by removing following two lemmas *)

Definition comparison_compare c1 c2 :=
  match c1, c2 with
  | Eq, Eq => true
  | Datatypes.Lt, Datatypes.Lt => true
  | Datatypes.Gt, Datatypes.Gt => true
  | _, _ => false
  end.

Global Instance comparison_comparable : Comparable comparison.
  applys comparable_beq comparison_compare. intros x y.
  destruct x; destruct y; simpl; iff H; inverts~ H;
   tryfalse; auto; try congruence.
Defined.

Global Instance int_comparable : Comparable int%I.
Proof using.
  applys comparable_beq (fun i j => decide (i ?= j = Eq)). intros x y.
  simpl; rewrite decide_spec; rew_istrue; iff H; rewrite Z.compare_eq_iff in * |- *; auto.
Defined.

(* ********************************************************************** *)
(** * Comparable *)

Definition prod_compare {A B : Type} `{Comparable A} `{Comparable B} (x y : A * B) :=
  let (x1, x2) := x in let (y1, y2) := y in
  decide (x1 = y1 /\ x2 = y2).

Global Instance prod_comparable : forall A B : Type,
  Comparable A -> Comparable B -> Comparable (A * B).
Proof using.
  introv CA CB. applys comparable_beq (@prod_compare A B _ _). intros x y.
  destruct x; destruct y; simpl; rewrite decide_spec; rew_istrue; iff H; inverts~ H;
   tryfalse; auto; try congruence.
Defined.

Definition option_compare {A} `{Comparable A} (o1 o2 : option A) :=
  match o1, o2 with
  | None, None => true
  | Some v1, Some v2 => decide (v1 = v2)
  | _, _ => false
  end.

Global Instance option_comparable : forall {A} `{Comparable A},
  Comparable (option A).
Proof using.
  intros.
  applys (comparable_beq option_compare).
  destruct x; destruct y; simpl; try rewrite decide_spec; rew_istrue; iff; auto_false*; congruence.
Defined.

(* ********************************************************************** *)
(** * Comparable *)

Global Instance unit_comparable : Comparable unit.
Proof using.
  apply make_comparable. intros [] [].
  applys decidable_make true. rew_istrue~.
Defined.

(* ********************************************************************** *)
(** * Comparison as boolean values *)
(* ---------------------------------------------------------------------- *)

(** ** Properties of boolean comparison *)
(* ---------------------------------------------------------------------- *)

(** ** Notation for comparison in [bool] are [x '= y] and [x '<> y] *)
Notation "x ''=' y :> A" := (isTrue (@eq A x y))
  (at level 70, y at next level, only parsing) : comp_scope.
Notation "x ''<>' y :> A" := (isTrue (~ (@eq A x y)))
  (at level 69, y at next level, only parsing) : comp_scope.
Notation "x ''=' y" := (isTrue (@eq _ x y))
  (at level 70, y at next level, no associativity) : comp_scope.
Notation "x ''<>' y" := (isTrue (~ (@eq _ x y)))
  (at level 69, y at next level, no associativity) : comp_scope.

Open Scope comp_scope.

Lemma eqb_eq : forall A (x y:A),
  x = y ->
  (x '= y) = true.
Proof using. intros. subst. apply~ isTrue_eq_true. Qed.

Lemma eqb_self : forall A (x:A),
  (x '= x) = true.
Proof using. intros. apply~ eqb_eq. Qed.

Lemma eqb_neq : forall A (x y:A),
  x <> y ->
  (x '= y) = false.
Proof using. intros. subst. apply~ isTrue_eq_false. Qed.

Lemma neqb_eq : forall A (x y:A),
  x = y ->
  (x '<> y) = false.
Proof using. intros. subst. rewrite~ isTrue_eq_false. Qed.

Lemma neqb_neq : forall A (x y:A),
  x <> y ->
  (x '<> y) = true.
Proof using. intros. subst. rewrite~ isTrue_eq_true. Qed.

Lemma neqb_self : forall A (x:A),
  (x '<> x) = false.
Proof using. intros. apply~ neqb_eq. Qed.

Lemma eqb_sym : forall A (x y : A),
  (x '= y) = (y '= x).
Proof using.
  introv. tests D: (x = y).
   rewrite~ eqb_self.
   do 2 rewrite~ eqb_neq.
Qed.
