(** MonadTactics.
  Provides tactics to easily manipulate the monads defined in Monads.v and Loops.v. **)

Set Implicit Arguments.
Require Export Monads Loops.


(** * Some useful definitions **)

(** Aborting results **)

Definition aborting_result A (r : result A) :=
  match r with
  | result_success _ _ => false
  | _ => true
  end.

Definition impossible_result A (r : result A) :=
  match r with
  | result_impossible_stack _ _ _ => true
  | _ => false
  end.


(** ** Updating the type of a result **)

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

(** This tactic tries to simplify as much as can be threaded versions
  of [convert_type_monad]. **)
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


(** ** Getting the parameters of an impossible result **)

Definition get_impossible_stack_state A (r : result A) :=
  match r with
  | result_impossible_stack S0 _ _ => S0
  | _ => arbitrary
  end.

Definition get_impossible_stack_stack A (r : result A) :=
  match r with
  | result_impossible_stack _ st _ => st
  | _ => arbitrary
  end.

Definition get_impossible_stack_message A (r : result A) :=
  match r with
  | result_impossible_stack _ _ msg => msg
  | _ => arbitrary
  end.

Lemma rewrite_impossible_result : forall A (r : result A),
  impossible_result r ->
  r = result_impossible_stack
        (get_impossible_stack_state r)
        (get_impossible_stack_stack r)
        (get_impossible_stack_message r).
Proof. introv I. destruct r; tryfalse. reflexivity. Qed.


(** ** Some useful tactics **)

Ltac destruct_PrimSxp_struct p :=
  let p_offset := fresh p "offset" in
  destruct p as [p_offset].

Ltac destruct_SymSxp_struct s :=
  let s_pname := fresh s "pname" in
  let s_value := fresh s "value" in
  let s_internal := fresh s "internal" in
  destruct s as [s_pname s_value s_internal].

Ltac destruct_ListSxp_struct l :=
  let l_carval := fresh l "carval" in
  let l_cdrval := fresh l "cdrval" in
  let l_tagval := fresh l "tagval" in
  destruct l as [l_carval l_cdrval l_tagval].

Ltac destruct_EnvSxp_struct e :=
  let e_frame := fresh e "frame" in
  let e_enclos := fresh e "enclos" in
  destruct e as [e_frame e_enclos].

Ltac destruct_CloSxp_struct c :=
  let c_formals := fresh c "formals" in
  let c_body := fresh c "body" in
  let c_env := fresh c "env" in
  destruct c as [c_formals c_body c_env].

Ltac destruct_PromSxp_struct p :=
  let p_value := fresh p "value" in
  let p_expr := fresh p "expr" in
  let p_env := fresh p "env" in
  destruct p as [p_value p_expr p_env].

Ltac destruct_NonVector_SExpRec_aux deep e_ :=
  let e_header := fresh e_ "header" in
  let e_data := fresh e_ "data" in
  destruct e_ as [e_header e_data];
  let e_prim := fresh e_ "prim" in
  let e_sym := fresh e_ "sym" in
  let e_list := fresh e_ "list" in
  let e_env := fresh e_ "env" in
  let e_clo := fresh e_ "clo" in
  let e_prom := fresh e_ "prom" in
  let inner t e_i :=
    match deep with
    | true => t e_i
    | false => idtac
    end in
  destruct e_data as [ e_prim | e_sym | e_list | e_env | e_clo | e_prom ];
    [ inner destruct_PrimSxp_struct e_prim
    | inner destruct_SymSxp_struct e_sym
    | inner destruct_ListSxp_struct e_list
    | inner destruct_EnvSxp_struct e_env
    | inner destruct_CloSxp_struct e_clo
    | inner destruct_PromSxp_struct e_prom ].

Ltac destruct_NonVector_SExpRec_deep := destruct_NonVector_SExpRec_aux true.
Ltac destruct_NonVector_SExpRec := destruct_NonVector_SExpRec_aux false.

Ltac destruct_SExpRec_aux deep1 deep2 e_ :=
  let e_nonVector := fresh e_ "nonVector" in
  let e_vectorChar := fresh e_ "vectorChar" in
  let e_vectorInteger := fresh e_ "vectorInteger" in
  let e_vectorComplex := fresh e_ "vectorComplex" in
  let e_vectorReal := fresh e_ "vectorReal" in
  let e_vectorPointer := fresh e_ "vectorPointer" in
  destruct e_ as [ e_nonVector | e_vectorChar | e_vectorInteger
                 | e_vectorComplex | e_vectorReal | e_vectorPointer];
  [ match deep1 with
    | true => destruct_NonVector_SExpRec_aux deep2 e_nonVector
    | false => idtac
    end | .. ].

Ltac destruct_SExpRec_deep := destruct_SExpRec_aux true false.
Ltac destruct_SExpRec_deep_full := destruct_SExpRec_aux true true.
Ltac destruct_SExpRec := destruct_SExpRec_aux false false.


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
    impossible_result (let%defined a := None using S in cont S a).
Proof. reflexivity. Qed.

Lemma if_is_prim_pass : forall A S header offset (cont : _ -> _ -> result A),
  let%prim a_, a_prim :=
    make_NonVector_SExpRec header (make_PrimSxp_struct offset) using S in
    cont a_ a_prim
  = cont (make_NonVector_SExpRec header (make_PrimSxp_struct offset))
      (make_PrimSxp_struct offset).
Proof. reflexivity. Qed.

Lemma if_is_prim_aborts : forall A S (e_ : SExpRec) (cont : _ -> _ -> result A),
  (forall header offset,
    e_ <> make_NonVector_SExpRec header (make_PrimSxp_struct offset)) ->
  aborting_result (let%prim a_, a_prim := e_ using S in cont a_ a_prim).
Proof. introv D. destruct_SExpRec_deep_full e_; (reflexivity || false~ D). Qed.

Lemma if_is_prim_abort : forall A S (e_ : SExpRec) (cont : _ -> _ -> result A),
  (forall header offset,
    e_ <> make_NonVector_SExpRec header (make_PrimSxp_struct offset)) ->
  impossible_result (let%prim a_, a_prim := e_ using S in cont a_ a_prim).
Proof. introv D. destruct_SExpRec_deep_full e_; (reflexivity || false~ D). Qed.

Lemma if_is_sym_pass : forall A S header pname value internal (cont : _ -> _ -> result A),
  let%sym a_, a_sym :=
    make_NonVector_SExpRec header (make_SymSxp_struct pname value internal) using S in
    cont a_ a_sym
  = cont (make_NonVector_SExpRec header (make_SymSxp_struct pname value internal))
      (make_SymSxp_struct pname value internal).
Proof. reflexivity. Qed.

Lemma if_is_sym_aborts : forall A S (e_ : SExpRec) (cont : _ -> _ -> result A),
  (forall header pname value internal,
    e_ <> make_NonVector_SExpRec header (make_SymSxp_struct pname value internal)) ->
  aborting_result (let%sym a_, a_sym := e_ using S in cont a_ a_sym).
Proof. introv D. destruct_SExpRec_deep_full e_; (reflexivity || false~ D). Qed.

Lemma if_is_sym_abort : forall A S (e_ : SExpRec) (cont : _ -> _ -> result A),
  (forall header pname value internal,
    e_ <> make_NonVector_SExpRec header (make_SymSxp_struct pname value internal)) ->
  impossible_result (let%sym a_, a_sym := e_ using S in cont a_ a_sym).
Proof. introv D. destruct_SExpRec_deep_full e_; (reflexivity || false~ D). Qed.

Lemma if_is_list_pass : forall A S header car cdr tag (cont : _ -> _ -> result A),
  let%list a_, a_list :=
    make_NonVector_SExpRec header (make_ListSxp_struct car cdr tag) using S in
    cont a_ a_list
  = cont (make_NonVector_SExpRec header (make_ListSxp_struct car cdr tag))
      (make_ListSxp_struct car cdr tag).
Proof. reflexivity. Qed.

Lemma if_is_list_aborts : forall A S (e_ : SExpRec) (cont : _ -> _ -> result A),
  (forall header car cdr tag,
    e_ <> make_NonVector_SExpRec header (make_ListSxp_struct car cdr tag)) ->
  aborting_result (let%list a_, a_list := e_ using S in cont a_ a_list).
Proof. introv D. destruct_SExpRec_deep_full e_; (reflexivity || false~ D). Qed.

Lemma if_is_list_abort : forall A S (e_ : SExpRec) (cont : _ -> _ -> result A),
  (forall header car cdr tag,
    e_ <> make_NonVector_SExpRec header (make_ListSxp_struct car cdr tag)) ->
  impossible_result (let%list a_, a_list := e_ using S in cont a_ a_list).
Proof. introv D. destruct_SExpRec_deep_full e_; (reflexivity || false~ D). Qed.

Lemma if_is_env_pass : forall A S header frame enclos (cont : _ -> _ -> result A),
  let%env a_, a_env :=
    make_NonVector_SExpRec header (make_EnvSxp_struct frame enclos) using S in
    cont a_ a_env
  = cont (make_NonVector_SExpRec header (make_EnvSxp_struct frame enclos))
      (make_EnvSxp_struct frame enclos).
Proof. reflexivity. Qed.

Lemma if_is_env_aborts : forall A S (e_ : SExpRec) (cont : _ -> _ -> result A),
  (forall header frame enclos,
    e_ <> make_NonVector_SExpRec header (make_EnvSxp_struct frame enclos)) ->
  aborting_result (let%env a_, a_env := e_ using S in cont a_ a_env).
Proof. introv D. destruct_SExpRec_deep_full e_; (reflexivity || false~ D). Qed.

Lemma if_is_env_abort : forall A S (e_ : SExpRec) (cont : _ -> _ -> result A),
  (forall header frame enclos,
    e_ <> make_NonVector_SExpRec header (make_EnvSxp_struct frame enclos)) ->
  impossible_result (let%env a_, a_env := e_ using S in cont a_ a_env).
Proof. introv D. destruct_SExpRec_deep_full e_; (reflexivity || false~ D). Qed.

Lemma if_is_clo_pass : forall A S header formals body env (cont : _ -> _ -> result A),
  let%clo a_, a_clo :=
    make_NonVector_SExpRec header (make_CloSxp_struct formals body env) using S in
    cont a_ a_clo
  = cont (make_NonVector_SExpRec header (make_CloSxp_struct formals body env))
      (make_CloSxp_struct formals body env).
Proof. reflexivity. Qed.

Lemma if_is_clo_aborts : forall A S (e_ : SExpRec) (cont : _ -> _ -> result A),
  (forall header formals body env,
    e_ <> make_NonVector_SExpRec header (make_CloSxp_struct formals body env)) ->
  aborting_result (let%clo a_, a_clo := e_ using S in cont a_ a_clo).
Proof. introv D. destruct_SExpRec_deep_full e_; (reflexivity || false~ D). Qed.

Lemma if_is_clo_abort : forall A S (e_ : SExpRec) (cont : _ -> _ -> result A),
  (forall header formals body env,
    e_ <> make_NonVector_SExpRec header (make_CloSxp_struct formals body env)) ->
  impossible_result (let%clo a_, a_clo := e_ using S in cont a_ a_clo).
Proof. introv D. destruct_SExpRec_deep_full e_; (reflexivity || false~ D). Qed.

Lemma if_is_prom_pass : forall A S header value expr env (cont : _ -> _ -> result A),
  let%prom a_, a_prom :=
    make_NonVector_SExpRec header (make_PromSxp_struct value expr env) using S in
    cont a_ a_prom
  = cont (make_NonVector_SExpRec header (make_PromSxp_struct value expr env))
      (make_PromSxp_struct value expr env).
Proof. reflexivity. Qed.

Lemma if_is_prom_aborts : forall A S (e_ : SExpRec) (cont : _ -> _ -> result A),
  (forall header value expr env,
    e_ <> make_NonVector_SExpRec header (make_PromSxp_struct value expr env)) ->
  aborting_result (let%prom a_, a_prom := e_ using S in cont a_ a_prom).
Proof. introv D. destruct_SExpRec_deep_full e_; (reflexivity || false~ D). Qed.

Lemma if_is_prom_abort : forall A S (e_ : SExpRec) (cont : _ -> _ -> result A),
  (forall header value expr env,
    e_ <> make_NonVector_SExpRec header (make_PromSxp_struct value expr env)) ->
  impossible_result (let%prom a_, a_prom := e_ using S in cont a_ a_prom).
Proof. introv D. destruct_SExpRec_deep_full e_; (reflexivity || false~ D). Qed.

(* TODO: From [read_as_prim]. Although these probably won’t get any
  useful lemmae without the paths of Path.v because of reading operations. *)

(* TODO: [let_Vector*], [read_nth_cell_Vector*] *)

(* TODO: map%* using the paths. *)

(* TODO: All the monads of Loops.v. *)


(** ** Tactics **)

Ltac get_pass_lemma t :=
  match get_head t with
  | add_stack => constr:(add_stack_pass)
  | if_success => constr:(if_success_pass)
  | if_defined => constr:(if_defined_pass)
  | if_is_prim => constr:(if_is_prim_pass)
  | if_is_sym => constr:(if_is_sym_pass)
  | if_is_list => constr:(if_is_list_pass)
  | if_is_env => constr:(if_is_env_pass)
  | if_is_clo => constr:(if_is_clo_pass)
  | if_is_prom => constr:(if_is_prom_pass)
  end.

Ltac get_aborts_lemma t :=
  match get_head t with
  | add_stack => constr:(add_stack_aborts)
  | if_success => constr:(if_success_aborts)
  | if_defined => constr:(if_defined_aborts)
  | if_is_prim => constr:(if_is_prim_aborts)
  | if_is_sym => constr:(if_is_sym_aborts)
  | if_is_list => constr:(if_is_list_aborts)
  | if_is_env => constr:(if_is_env_aborts)
  | if_is_clo => constr:(if_is_clo_aborts)
  | if_is_prom => constr:(if_is_prom_aborts)
  end.

Ltac get_abort_lemma t :=
  match get_head t with
  | if_success => constr:(if_success_abort)
  | if_defined => constr:(if_defined_abort)
  | if_is_prim => constr:(if_is_prim_abort)
  | if_is_sym => constr:(if_is_sym_abort)
  | if_is_list => constr:(if_is_list_abort)
  | if_is_env => constr:(if_is_env_abort)
  | if_is_clo => constr:(if_is_clo_abort)
  | if_is_prom => constr:(if_is_prom_abort)
  end.

Ltac unfolds_get_impossible :=
  try unfolds get_impossible_stack_state;
  try unfolds get_impossible_stack_stack;
  try unfolds get_impossible_stack_message.

(** To speed up computations, we directly fail if a result is not
  already fully computed. **)
Ltac result_computed r :=
  match get_head r with
  | result_success => idtac
  | result_longjump => idtac
  | result_error_stack => idtac
  | result_impossible_stack => idtac
  | result_not_implemented_stack => idtac
  | result_bottom => idtac
  end.

Ltac try_solving_premises :=
  try solve [
    intros;
    first [
        reflexivity
      | discriminate
      | autos~ ] ].

Ltac munfold_with_subresult t r :=
  result_computed r;
  first [
      let P := get_pass_lemma t in
      rewrite P; try_solving_premises
    | let A := get_abort_lemma t in
      first [
          rewrite A; try_solving_premises
        | rewrite rewrite_impossible_result with (r := t);
          [| apply A; try_solving_premises ];
          unfolds_get_impossible
        | let H := fresh "Habort" in
          asserts H: (aborting_result r);
          [ first [
                reflexivity
              | let AT := get_aborts_lemma t in
                apply AT; try_solving_premises ]
          | rewrite A with H ] ] ].

Ltac munfold_without_subresult t :=
  first [
      let P := get_pass_lemma t in
      rewrite P; try_solving_premises
    | let A := get_abort_lemma t in
      first [
          rewrite A; try_solving_premises
        | rewrite rewrite_impossible_result with (r := t);
          [| apply A; try_solving_premises ];
          unfolds_get_impossible ] ].

Ltac munfold :=
  match goal with
  | |- context [ add_stack ?fname ?r ] =>
    munfold_with_subresult (add_stack fname r) r
  | |- context [ if_success ?r ?cont ] =>
    munfold_with_subresult (if_success r cont) r
  | |- context [ if_defined ?S ?o ?cont ] =>
    munfold_without_subresult (if_defined S o cont)
  | |- context [ result_skip ?S ] =>
    unfolds result_skip
  | |- context [ if_then_else_success ?b ?c1 ?c2 ] =>
    unfolds if_then_else_success
  | |- context [ if_then_success ?b ?c ?cont ] =>
    unfolds if_then_success
  | |- context [ if_option_defined ?c ?cont1 ?cont2 ] =>
    unfolds if_option_defined
  | |- context [ if_is_prim ?S ?e_ ?cont ] =>
    munfold_without_subresult (if_is_prim S e_ cont)
  end.

Ltac munfolds :=
  repeat (munfold; repeat let_simpl).

