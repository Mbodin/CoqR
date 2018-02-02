(** MonadTactics.
  Provides tactics to easily manipulate the monads defined in Monads.v and Loops.v. **)

Set Implicit Arguments.
Require Export Monads Loops.


(** * Updating the type of a result **)

Definition aborting_result A (r : result A) :=
  match r with
  | result_success _ _ => false
  | _ => true
  end.

Definition convert_type_monad A B (r : result A) :
    aborting_result r ->
    result B.
  intros H. destruct r eqn: E; (solve [false~ H] || clear H);
  match type of E with _ = ?C =>
    let rec rep C :=
      match C with
      | ?f A => constr:(f B)
      | ?f ?arg =>
        let f := rep f in constr:(f arg)
      end in
    let r := rep C in exact r
  end.
Defined.
Arguments convert_type_monad [A B] r.

Lemma convert_type_monad_aborting : forall A B (r : result A) H,
  aborting_result (convert_type_monad r H : result B).
Proof. introv. destruct r; (reflexivity || false*). Qed.

Lemma convert_type_monad_change_proof : forall A B (r : result A) H1 H2,
  (convert_type_monad r H1 : result B) = convert_type_monad r H2.
Proof. introv. destruct r; (reflexivity || false*). Qed.

Lemma convert_type_monad_transitive : forall A B C (r : result A) H1 H2,
  convert_type_monad (convert_type_monad r H1 : result B) H2
  = (convert_type_monad r H1 : result C).
Proof. introv. destruct r; (reflexivity || false*). Qed.

(** This tactic tries to simplify as much as can be threaded versions of [convert_type_monad]. **)
Ltac clean_convert_type_one :=
  let term_trans A C r H1 := constr:(@convert_type_monad A C r H1) in
  match goal with
  | |- context [ @convert_type_monad ?B ?C (@convert_type_monad ?A _ ?r ?H1) ?H2 ] =>
    let t := term_trans A C r H1 in
    asserts_rewrite (convert_type_monad (convert_type_monad r H1) H2 = t);
    [ apply convert_type_monad_transitive |]
  | H : context [ @convert_type_monad ?B ?C (@convert_type_monad ?A _ ?r ?H1) ?H2 ] |- _ =>
    let t := term_trans A C r H1 in
    asserts_rewrite (convert_type_monad (convert_type_monad r H1) H2 = t) in H;
    [ apply convert_type_monad_transitive |]
  end.

Ltac clean_convert_type := repeat clean_convert_type_one.


(** * Simplifying monads **)

(** ** Lemmae **)

Lemma let_success_pass : forall A B S r (cont : state -> A -> result B),
  let%success a := result_success S r using S in cont S a
  = 'let a := r in cont S a.
Proof. reflexivity. Qed.

Lemma let_success_abort : forall A B r (cont : state -> A -> result B) H,
  let%success a := r using S in cont S a = convert_type_monad r H.
Proof. introv. destruct r; (reflexivity || false*). Qed.

(** ** Tactics **)

(** This tactics unfolds terms of the form ['let a := […] in let (a1, …, an) := a in …]. **)
Ltac mlet_name :=
  try let_name;
  repeat match goal with
  | |- context [ let (a1, a2) := ?r in _ ] =>
     match goal with
     | E : r = _ |- _ =>
       rewrite E;
       match goal with
       | |- context [ r ] => idtac
       | _ => clear E; try clear r
       end
     end
  end.

Ltac rewrite_let_name :=
  match goal with
  | |- context A [ 'let a := (?a1, ?a2) in let (b1, b2) := ?c in _ ] =>
    match c with a => ?? end
  end.

Ltac munfold :=
  repeat match goal with
  | |- context [ let%success a := ?r using S in _ ] =>
    first [
        rewrite let_success_pass; rewrite_let_name
      | let H := fresh "H" in
        asserts H: (aborting_result r);
        [ reflexivity
        | rewrite let_success_abort with (H := H) ] ]
  end.

Definition f (x : nat) := (1, 2, false, x).

Goal forall S,
  let%success (a, b, c, d) := result_success S (f 42) using S in result_success S c = result_impossible S "".
  introv. munfold.
