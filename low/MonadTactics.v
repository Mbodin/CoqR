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
Proof. introv. destruct r; (reflexivity || inverts~ H). Qed.

Lemma convert_type_monad_change_proof : forall A B (r : result A) H1 H2,
  (convert_type_monad r H1 : result B) = convert_type_monad r H2.
Proof. introv. destruct r; (reflexivity || inverts~ H1). Qed.

Lemma convert_type_monad_transitive : forall A B C (r : result A) H1 H2,
  convert_type_monad (convert_type_monad r H1 : result B) H2
  = (convert_type_monad r H1 : result C).
Proof. introv. destruct r; (reflexivity || inverts~ H1). Qed.

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

Lemma add_stack_pass : forall A fname S (a : A),
  add%stack fname in (result_success S a) = result_success S a.
Proof. reflexivity. Qed.

Lemma add_stack_aborts : forall A fname (r : result A),
  aborting_result r ->
  aborting_result (add%stack fname in r).
Proof. introv H. destruct r; (reflexivity || inverts~ H). Qed.

Lemma if_success_pass : forall A B S a (cont : state -> A -> result B),
  let%success a := result_success S a using S in cont S a
  = 'let a := a in cont S a.
Proof. reflexivity. Qed.

Lemma if_success_aborts : forall A B r (cont : state -> A -> result B),
  aborting_result r ->
  aborting_result (let%success a := r using S in cont S a).
Proof. introv H. destruct r; (reflexivity || inverts~ H). Qed.

Lemma if_success_abort : forall A B r (cont : state -> A -> result B) H,
  let%success a := r using S in cont S a = convert_type_monad r H.
Proof. introv. destruct r; (reflexivity || inverts~ H). Qed.

Lemma if_defined_pass : forall A B S a (cont : state -> A -> result B),
  let%defined a := Some a using S in cont S a
  = 'let a := a in cont S a.
Proof. reflexivity. Qed.

Lemma if_defined_aborts : forall A B S (cont : state -> A -> result B),
  aborting_result (let%defined a := None using S in cont S a).
Proof. reflexivity. Qed.

Definition if_defined_abort : forall A B S (cont : state -> A -> result B),
    let%defined a := None using S in cont S a
    = result_impossible_stack S _ _
  := fun _ _ _ _ => eq_refl.

(* TODO: From [if_is_prim], maybe tactics for read and write. *)


(** ** Tactics **)

Ltac get_pass_lemma t :=
  match get_head t with
  | add_stack => constr:(add_stack_pass)
  | if_success => constr:(if_success_pass)
  | if_defined => constr:(if_defined_pass)
  end.

Ltac get_aborts_lemma t :=
  match get_head t with
  | add_stack => constr:(add_stack_aborts)
  | if_success => constr:(if_success_aborts)
  | if_defined => constr:(if_defined_aborts)
  end.

Ltac get_abort_lemma t :=
  match get_head t with
  | if_success => constr:(if_success_abort)
  | if_defined => constr:(if_defined_abort)
  end.

(** To speed up computations, we directly fail if a result is not already fully computed. **)
Ltac result_computed r :=
  match get_head r with
  | result_success => idtac
  | result_longjump => idtac
  | result_error_stack => idtac
  | result_impossible_stack => idtac
  | result_not_implemented_stack => idtac
  | result_bottom => idtac
  end.

Ltac munfold_with_result t r :=
  result_computed r;
  first [
      let P := get_pass_lemma t in
      rewrite~ P
    | let A := get_abort_lemma t in
      first [
          rewrite A
        | let H := fresh "Habort" in
          asserts H: (aborting_result r);
          [ first [
                reflexivity
              | let AT := get_aborts_lemma t in
                apply* AT ]
          | rewrite A with H ] ] ].

Ltac munfold_without_result t :=
  first [
      let P := get_pass_lemma t in
      rewrite~ P
    | let A := get_abort_lemma t in
      rewrite A ].

Ltac munfold :=
  match goal with
  | |- context [ add_stack ?fname ?r ] =>
    munfold_with_result (add_stack fname r) r
  | |- context [ if_success ?r ?cont ] =>
    munfold_with_result (if_success r cont) r
  | |- context [ if_defined ?S ?o ?cont ] =>
    munfold_without_result (if_defined S o cont)
  | |- context [ result_skip ?S ] =>
    unfolds result_skip
  | |- context [ if_then_else_success ?b ?c1 ?c2 ] =>
    unfolds if_then_else_success
  | |- context [ if_then_success ?b ?c ?cont ] =>
    unfolds if_then_success
  | |- context [ if_option_defined ?c ?cont1 ?cont2 ] =>
    unfolds if_option_defined
  end.

Ltac munfolds :=
  repeat (munfold; repeat let_simpl).
