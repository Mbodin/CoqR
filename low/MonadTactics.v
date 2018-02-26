(** MonadTactics.
  Provides tactics to easily manipulate the monads defined in Monads.v and Loops.v. **)

Set Implicit Arguments.
Require Import TLC.LibTactics.
Require Export Monads Loops Rfeatures.


(** * Some useful definitions **)

(** ** Aborting results **)

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

Lemma impossible_result_aborting_result : forall A (r : result A),
  impossible_result r ->
  aborting_result r.
Proof. introv I. destruct r; (reflexivity || false~ I). Qed.


(** ** Generic result property **)

Definition result_prop A P_success P_error P_longjump (r : result A) :=
  match r with
  | result_success S0 r => P_success S0 r
  | result_longjump S0 n c => P_longjump S0 n c
  | result_error_stack S0 st msg => P_error S0
  | result_impossible_stack S0 st msg => False
  | result_not_implemented_stack st msg => True
  | result_bottom S0 => True
  end.

Lemma result_prop_weaken : forall A (r : result A)
    (P1_success P2_success : _ -> _ -> Prop)
    (P1_error P2_error : _ -> Prop)
    (P1_longjump P2_longjump : _ -> _ -> _ -> Prop),
  (forall S r, P1_success S r -> P2_success S r) ->
  (forall S, P1_error S -> P2_error S) ->
  (forall S n c, P1_longjump S n c -> P2_longjump S n c) ->
  result_prop P1_success P1_error P1_longjump r ->
  result_prop P2_success P2_error P2_longjump r.
Proof. introv I1 I2 I3. destruct r; simpl; autos~. Qed.


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

Lemma convert_type_monad_reflexive : forall A (r : result A) H,
  convert_type_monad r H = r.
Proof. introv. destruct r; (reflexivity || inverts~ H). Qed.

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

(** *** Function definitions **)

Lemma add_stack_pass : forall A fname S (a : A),
  add%stack fname in (result_success S a) = result_success S a.
Proof. reflexivity. Qed.

Lemma add_stack_aborts : forall A fname (r : result A),
  aborting_result r ->
  aborting_result (add%stack fname in r).
Proof. introv H. destruct r; (reflexivity || inverts~ H). Qed.

Lemma add_stack_simplify : forall A fname r S (a : A),
  r = result_success S a ->
  add%stack fname in r = result_success S a.
Proof. introv E. substs~. Qed.

Lemma add_stack_result : forall A P_success P_error P_longjump fname (r : result A),
  result_prop P_success P_error P_longjump r ->
  result_prop P_success P_error P_longjump (add%stack fname in r).
Proof. introv E. destruct~ r. Qed.


(** *** [let]-monads **)

Lemma if_success_pass : forall A B S a (cont : state -> A -> result B),
  let%success a := result_success S a using S in cont S a
  = 'let a := a in cont S a.
Proof. reflexivity. Qed.

Lemma if_success_abort : forall A B r (cont : state -> A -> result B) H,
  let%success a := r using S in cont S a = convert_type_monad r H.
Proof. introv. destruct r; (reflexivity || inverts~ H). Qed.

Lemma if_success_aborts : forall A B r (cont : state -> A -> result B),
  aborting_result r ->
  aborting_result (let%success a := r using S in cont S a).
Proof. introv H. destruct r; (reflexivity || inverts~ H). Qed.

Lemma if_success_result : forall A B r (cont : state -> A -> result B)
    (P_success P'_success : _ -> _ -> Prop) P_error P_longjump,
  (forall S a, P_success S a ->
    result_prop P'_success P_error P_longjump (cont S a)) ->
  result_prop P_success P_error P_longjump r ->
  result_prop P'_success P_error P_longjump (let%success a := r using S in cont S a).
Proof. introv I P. destruct* r. Qed.

Lemma if_defined_msg_pass : forall A B S a msg (cont : A -> result B),
  let%defined a := Some a with msg using S in cont a
  = 'let a := a in cont a.
Proof. reflexivity. Qed.

Definition if_defined_msg_abort : forall A B S msg (cont : A -> result B),
    impossible_result (let%defined a := None with msg using S in cont a).
Proof. reflexivity. Qed.

Lemma if_defined_msg_aborts : forall A B S msg (cont : A -> result B),
  aborting_result (let%defined a := None with msg using S in cont a).
Proof. introv. applys~ impossible_result_aborting_result if_defined_msg_abort. Qed.

Lemma if_defined_pass : forall A B S a (cont : A -> result B),
  let%defined a := Some a using S in cont a
  = 'let a := a in cont a.
Proof. introv. apply~ if_defined_msg_pass. Qed.

Definition if_defined_abort : forall A B S (cont : A -> result B),
    impossible_result (let%defined a := None using S in cont a).
Proof. introv. apply~ if_defined_msg_abort. Qed.

Lemma if_defined_aborts : forall A B S (cont : A -> result B),
  aborting_result (let%defined a := None using S in cont a).
Proof. introv. applys~ impossible_result_aborting_result if_defined_abort. Qed.


(** *** Basic Language Elements **)

Lemma if_is_prim_pass : forall A S header offset (cont : _ -> _ -> result A),
  let%prim a_, a_prim :=
    make_NonVector_SExpRec header (make_PrimSxp_struct offset) using S in
    cont a_ a_prim
  = cont (make_NonVector_SExpRec header (make_PrimSxp_struct offset))
      (make_PrimSxp_struct offset).
Proof. reflexivity. Qed.

Lemma if_is_prim_abort : forall A S (e_ : SExpRec) (cont : _ -> _ -> result A),
  (forall header offset,
    e_ <> make_NonVector_SExpRec header (make_PrimSxp_struct offset)) ->
  impossible_result (let%prim a_, a_prim := e_ using S in cont a_ a_prim).
Proof. introv D. destruct_SExpRec_deep_full e_; (reflexivity || false~ D). Qed.

Lemma if_is_prim_aborts : forall A S (e_ : SExpRec) (cont : _ -> _ -> result A),
  (forall header offset,
    e_ <> make_NonVector_SExpRec header (make_PrimSxp_struct offset)) ->
  aborting_result (let%prim a_, a_prim := e_ using S in cont a_ a_prim).
Proof. introv D. applys~ impossible_result_aborting_result if_is_prim_abort. Qed.

Lemma if_is_sym_pass : forall A S header pname value internal (cont : _ -> _ -> result A),
  let%sym a_, a_sym :=
    make_NonVector_SExpRec header (make_SymSxp_struct pname value internal) using S in
    cont a_ a_sym
  = cont (make_NonVector_SExpRec header (make_SymSxp_struct pname value internal))
      (make_SymSxp_struct pname value internal).
Proof. reflexivity. Qed.

Lemma if_is_sym_abort : forall A S (e_ : SExpRec) (cont : _ -> _ -> result A),
  (forall header pname value internal,
    e_ <> make_NonVector_SExpRec header (make_SymSxp_struct pname value internal)) ->
  impossible_result (let%sym a_, a_sym := e_ using S in cont a_ a_sym).
Proof. introv D. destruct_SExpRec_deep_full e_; (reflexivity || false~ D). Qed.

Lemma if_is_sym_aborts : forall A S (e_ : SExpRec) (cont : _ -> _ -> result A),
  (forall header pname value internal,
    e_ <> make_NonVector_SExpRec header (make_SymSxp_struct pname value internal)) ->
  aborting_result (let%sym a_, a_sym := e_ using S in cont a_ a_sym).
Proof. introv D. applys~ impossible_result_aborting_result if_is_sym_abort. Qed.

Lemma if_is_list_pass : forall A S header car cdr tag (cont : _ -> _ -> result A),
  let%list a_, a_list :=
    make_NonVector_SExpRec header (make_ListSxp_struct car cdr tag) using S in
    cont a_ a_list
  = cont (make_NonVector_SExpRec header (make_ListSxp_struct car cdr tag))
      (make_ListSxp_struct car cdr tag).
Proof. reflexivity. Qed.

Lemma if_is_list_abort : forall A S (e_ : SExpRec) (cont : _ -> _ -> result A),
  (forall header car cdr tag,
    e_ <> make_NonVector_SExpRec header (make_ListSxp_struct car cdr tag)) ->
  impossible_result (let%list a_, a_list := e_ using S in cont a_ a_list).
Proof. introv D. destruct_SExpRec_deep_full e_; (reflexivity || false~ D). Qed.

Lemma if_is_list_aborts : forall A S (e_ : SExpRec) (cont : _ -> _ -> result A),
  (forall header car cdr tag,
    e_ <> make_NonVector_SExpRec header (make_ListSxp_struct car cdr tag)) ->
  aborting_result (let%list a_, a_list := e_ using S in cont a_ a_list).
Proof. introv D. applys~ impossible_result_aborting_result if_is_list_abort. Qed.

Lemma if_is_env_pass : forall A S header frame enclos (cont : _ -> _ -> result A),
  let%env a_, a_env :=
    make_NonVector_SExpRec header (make_EnvSxp_struct frame enclos) using S in
    cont a_ a_env
  = cont (make_NonVector_SExpRec header (make_EnvSxp_struct frame enclos))
      (make_EnvSxp_struct frame enclos).
Proof. reflexivity. Qed.

Lemma if_is_env_abort : forall A S (e_ : SExpRec) (cont : _ -> _ -> result A),
  (forall header frame enclos,
    e_ <> make_NonVector_SExpRec header (make_EnvSxp_struct frame enclos)) ->
  impossible_result (let%env a_, a_env := e_ using S in cont a_ a_env).
Proof. introv D. destruct_SExpRec_deep_full e_; (reflexivity || false~ D). Qed.

Lemma if_is_env_aborts : forall A S (e_ : SExpRec) (cont : _ -> _ -> result A),
  (forall header frame enclos,
    e_ <> make_NonVector_SExpRec header (make_EnvSxp_struct frame enclos)) ->
  aborting_result (let%env a_, a_env := e_ using S in cont a_ a_env).
Proof. introv D. applys~ impossible_result_aborting_result if_is_env_abort. Qed.

Lemma if_is_clo_pass : forall A S header formals body env (cont : _ -> _ -> result A),
  let%clo a_, a_clo :=
    make_NonVector_SExpRec header (make_CloSxp_struct formals body env) using S in
    cont a_ a_clo
  = cont (make_NonVector_SExpRec header (make_CloSxp_struct formals body env))
      (make_CloSxp_struct formals body env).
Proof. reflexivity. Qed.

Lemma if_is_clo_abort : forall A S (e_ : SExpRec) (cont : _ -> _ -> result A),
  (forall header formals body env,
    e_ <> make_NonVector_SExpRec header (make_CloSxp_struct formals body env)) ->
  impossible_result (let%clo a_, a_clo := e_ using S in cont a_ a_clo).
Proof. introv D. destruct_SExpRec_deep_full e_; (reflexivity || false~ D). Qed.

Lemma if_is_clo_aborts : forall A S (e_ : SExpRec) (cont : _ -> _ -> result A),
  (forall header formals body env,
    e_ <> make_NonVector_SExpRec header (make_CloSxp_struct formals body env)) ->
  aborting_result (let%clo a_, a_clo := e_ using S in cont a_ a_clo).
Proof. introv D. applys~ impossible_result_aborting_result if_is_clo_abort. Qed.

Lemma if_is_prom_pass : forall A S header value expr env (cont : _ -> _ -> result A),
  let%prom a_, a_prom :=
    make_NonVector_SExpRec header (make_PromSxp_struct value expr env) using S in
    cont a_ a_prom
  = cont (make_NonVector_SExpRec header (make_PromSxp_struct value expr env))
      (make_PromSxp_struct value expr env).
Proof. reflexivity. Qed.

Lemma if_is_prom_abort : forall A S (e_ : SExpRec) (cont : _ -> _ -> result A),
  (forall header value expr env,
    e_ <> make_NonVector_SExpRec header (make_PromSxp_struct value expr env)) ->
  impossible_result (let%prom a_, a_prom := e_ using S in cont a_ a_prom).
Proof. introv D. destruct_SExpRec_deep_full e_; (reflexivity || false~ D). Qed.

Lemma if_is_prom_aborts : forall A S (e_ : SExpRec) (cont : _ -> _ -> result A),
  (forall header value expr env,
    e_ <> make_NonVector_SExpRec header (make_PromSxp_struct value expr env)) ->
  aborting_result (let%prom a_, a_prom := e_ using S in cont a_ a_prom).
Proof. introv D. applys~ impossible_result_aborting_result if_is_prom_abort. Qed.


(** ** Vectors **)

Lemma read_cell_Vector_SExpRec_pass : forall A B `{Inhab A} S
    (v : Vector_SExpRec A) i (cont : _ -> result B),
  i < ArrayList.length v ->
  read%cell c := v at i using S in cont c
  = cont (ArrayList.read v i).
Proof.
  introv I. unfolds. eapply ArrayList.read_option_Some in I.
  rewrite I. rewrite if_defined_msg_pass. reflexivity.
Qed.

Lemma read_cell_Vector_SExpRec_abort : forall A B S
    (v : Vector_SExpRec A) i (cont : _ -> result B),
  i >= ArrayList.length v ->
  impossible_result (read%cell c := v at i using S in cont c).
Proof.
  introv I. unfolds read_cell_Vector_SExpRec.
  eapply ArrayList.read_option_None in I. rewrite I.
  apply~ if_defined_msg_abort.
Qed.

Lemma read_cell_Vector_SExpRec_aborts : forall A B S
    (v : Vector_SExpRec A) i (cont : _ -> result B),
  i >= ArrayList.length v ->
  aborting_result (read%cell c := v at i using S in cont c).
Proof. introv D. applys~ impossible_result_aborting_result read_cell_Vector_SExpRec_abort. Qed.

Lemma update_Vector_SExpRec_cell_pass : forall A (v : Vector_SExpRec A) n c,
  n < ArrayList.length v ->
  update_Vector_SExpRec_cell v n c
  = Some (update_Vector_SExpRec v (ArrayList.write v n c)).
Proof. introv I. unfolds. cases_if as C; autos~. fold_bool. rew_refl in C. false*. Qed.

Lemma update_Vector_SExpRec_cell_abort : forall A (v : Vector_SExpRec A) n c,
  n >= ArrayList.length v ->
  update_Vector_SExpRec_cell v n c = None.
Proof. introv I. unfolds. cases_if as C; autos~. fold_bool. rew_refl in C. false. math. Qed.


Lemma let_VectorChar_pass : forall A S e_ (cont : _ -> _ -> result A),
  let%VectorChar e_vector := SExpRec_VectorChar e_ using S in cont S e_vector
  = cont S e_.
Proof. reflexivity. Qed.

Lemma let_VectorChar_abort : forall A S e_ (cont : _ -> _ -> result A),
  (forall v_, e_ <> SExpRec_VectorChar v_) ->
  impossible_result (let%VectorChar e_vector := e_ using S in cont S e_vector).
Proof. introv D. destruct_SExpRec e_; (reflexivity || false~ D). Qed.

Lemma let_VectorChar_aborts : forall A S e_ (cont : _ -> _ -> result A),
  (forall v_, e_ <> SExpRec_VectorChar v_) ->
  aborting_result (let%VectorChar e_vector := e_ using S in cont S e_vector).
Proof. introv D. applys~ impossible_result_aborting_result let_VectorChar_abort. Qed.

Lemma let_VectorLogical_pass : forall A S e_ (cont : _ -> _ -> result A),
  let%VectorLogical e_vector := SExpRec_VectorLogical e_ using S in cont S e_vector
  = cont S e_.
Proof. reflexivity. Qed.

Lemma let_VectorLogical_abort : forall A S e_ (cont : _ -> _ -> result A),
  (forall v_, e_ <> SExpRec_VectorLogical v_) ->
  impossible_result (let%VectorLogical e_vector := e_ using S in cont S e_vector).
Proof. introv D. destruct_SExpRec e_; (reflexivity || false~ D). Qed.

Lemma let_VectorLogical_aborts : forall A S e_ (cont : _ -> _ -> result A),
  (forall v_, e_ <> SExpRec_VectorLogical v_) ->
  aborting_result (let%VectorLogical e_vector := e_ using S in cont S e_vector).
Proof. introv D. applys~ impossible_result_aborting_result let_VectorLogical_abort. Qed.

Lemma let_VectorInteger_pass : forall A S e_ (cont : _ -> _ -> result A),
  let%VectorInteger e_vector := SExpRec_VectorInteger e_ using S in cont S e_vector
  = cont S e_.
Proof. reflexivity. Qed.

Lemma let_VectorInteger_abort : forall A S e_ (cont : _ -> _ -> result A),
  (forall v_, e_ <> SExpRec_VectorInteger v_) ->
  impossible_result (let%VectorInteger e_vector := e_ using S in cont S e_vector).
Proof. introv D. destruct_SExpRec e_; (reflexivity || false~ D). Qed.

Lemma let_VectorInteger_aborts : forall A S e_ (cont : _ -> _ -> result A),
  (forall v_, e_ <> SExpRec_VectorInteger v_) ->
  aborting_result (let%VectorInteger e_vector := e_ using S in cont S e_vector).
Proof. introv D. applys~ impossible_result_aborting_result let_VectorInteger_abort. Qed.

Lemma let_VectorReal_pass : forall A S e_ (cont : _ -> _ -> result A),
  let%VectorReal e_vector := SExpRec_VectorReal e_ using S in cont S e_vector
  = cont S e_.
Proof. reflexivity. Qed.

Lemma let_VectorReal_abort : forall A S e_ (cont : _ -> _ -> result A),
  (forall v_, e_ <> SExpRec_VectorReal v_) ->
  impossible_result (let%VectorReal e_vector := e_ using S in cont S e_vector).
Proof. introv D. destruct_SExpRec e_; (reflexivity || false~ D). Qed.

Lemma let_VectorReal_aborts : forall A S e_ (cont : _ -> _ -> result A),
  (forall v_, e_ <> SExpRec_VectorReal v_) ->
  aborting_result (let%VectorReal e_vector := e_ using S in cont S e_vector).
Proof. introv D. applys~ impossible_result_aborting_result let_VectorReal_abort. Qed.

Lemma let_VectorComplex_pass : forall A S e_ (cont : _ -> _ -> result A),
  let%VectorComplex e_vector := SExpRec_VectorComplex e_ using S in cont S e_vector
  = cont S e_.
Proof. reflexivity. Qed.

Lemma let_VectorComplex_abort : forall A S e_ (cont : _ -> _ -> result A),
  (forall v_, e_ <> SExpRec_VectorComplex v_) ->
  impossible_result (let%VectorComplex e_vector := e_ using S in cont S e_vector).
Proof. introv D. destruct_SExpRec e_; (reflexivity || false~ D). Qed.

Lemma let_VectorComplex_aborts : forall A S e_ (cont : _ -> _ -> result A),
  (forall v_, e_ <> SExpRec_VectorComplex v_) ->
  aborting_result (let%VectorComplex e_vector := e_ using S in cont S e_vector).
Proof. introv D. applys~ impossible_result_aborting_result let_VectorComplex_abort. Qed.

Lemma let_VectorPointer_pass : forall A S e_ (cont : _ -> _ -> result A),
  let%VectorPointer e_vector := SExpRec_VectorPointer e_ using S in cont S e_vector
  = cont S e_.
Proof. reflexivity. Qed.

Lemma let_VectorPointer_abort : forall A S e_ (cont : _ -> _ -> result A),
  (forall v_, e_ <> SExpRec_VectorPointer v_) ->
  impossible_result (let%VectorPointer e_vector := e_ using S in cont S e_vector).
Proof. introv D. destruct_SExpRec e_; (reflexivity || false~ D). Qed.

Lemma let_VectorPointer_aborts : forall A S e_ (cont : _ -> _ -> result A),
  (forall v_, e_ <> SExpRec_VectorPointer v_) ->
  aborting_result (let%VectorPointer e_vector := e_ using S in cont S e_vector).
Proof. introv D. applys~ impossible_result_aborting_result let_VectorPointer_abort. Qed.


(** *** Loops **)

Lemma while_unfold : forall A S (a : A) expr stat runs,
  while_loop runs S a expr stat
  = if%success expr S a using S then
      let%success a := stat S a using S in
      runs_while_loop runs S a expr stat
    else
      result_success S a.
Proof. introv. reflexivity. Qed.

Lemma while_expr_abort : forall A S (e : A) expr stat runs H,
  do%let a := e while expr do stat using S, runs = convert_type_monad expr H.
Proof. introv. apply~ if_success_abort. Qed.

Lemma while_expr_aborts : forall A S (e : A) expr stat runs,
  aborting_result expr ->
  aborting_result (do%let a := e while expr do stat using S, runs).
Proof. introv H. apply~ if_success_aborts. Qed.

Lemma fold_left_listSxp_gen_nil : forall runs globals A S (a : A) iterate,
  fold_left_listSxp_gen runs globals S (global_mapping globals R_NilValue) a iterate
  = result_success S a.
Proof. introv. unfolds. unfolds while_loop. rewrite decide_def. cases_if~. Qed.

Definition runs_fold_left_listSxp_gen runs globals A S l (a : A)
    (iterate : state -> A -> SEXP -> SExpRec -> ListSxp_struct -> result A) : result A :=
  let%success (l, a) :=
    runs_while_loop runs S (l, a)
      (fun S la => let (l, a) := la in result_success S (decide (l <> global_mapping globals R_NilValue)))
      (fun S la =>
        let (l, a) := la in
        read%list l_, l_list := l using S in
        let%success a := iterate S a l l_ l_list using S in
        result_success S (list_cdrval l_list, a)) using S in
  result_success S a.

Lemma runs_fold_left_listSxp_gen_eq : forall n globals,
  runs_fold_left_listSxp_gen (runs (1 + n) globals) = fold_left_listSxp_gen (runs n globals).
Proof. introv. reflexivity. Qed.

Lemma fold_left_listSxp_gen_cons : forall runs globals A S l (a : A) iterate,
  l <> global_mapping globals R_NilValue ->
  fold_left_listSxp_gen runs globals S l a iterate
  = read%list l_, l_list := l using S in
    let%success a := iterate S a l l_ l_list using S in
    runs_fold_left_listSxp_gen runs globals S (list_cdrval l_list) a iterate.
Proof.
  introv D. unfolds. unfolds while_loop. rewrite decide_def. cases_if~.
  simpl. unfolds read_as_list. destruct (read_SExp S l) as [l_|]; try reflexivity.
  simpl. destruct_SExpRec_deep_full l_; try reflexivity.
  repeat rewrite if_is_list_pass. simpl. destruct~ iterate.
Qed.

Lemma fold_left_listSxp_nil : forall runs globals A S (a : A) iterate,
  fold_left_listSxp runs globals S (global_mapping globals R_NilValue) a iterate
  = result_success S a.
Proof. introv. apply~ fold_left_listSxp_gen_nil. Qed.

Definition runs_fold_left_listSxp runs globals A S l (a : A) iterate :=
  runs_fold_left_listSxp_gen runs globals S l a (fun S a _ _ l_list =>
    iterate S a (list_carval l_list) (list_tagval l_list)).

Lemma runs_fold_left_listSxp_eq : forall n globals,
  runs_fold_left_listSxp (runs (1 + n) globals) = fold_left_listSxp (runs n globals).
Proof. introv. unfolds. rewrite~ runs_fold_left_listSxp_gen_eq. Qed.

Lemma fold_left_listSxp_cons : forall runs globals A S l (a : A) iterate,
  l <> global_mapping globals R_NilValue ->
  fold_left_listSxp runs globals S l a iterate
  = read%list l_car, l_cdr, l_tag := l using S in
    let%success a := iterate S a l_car l_tag using S in
    runs_fold_left_listSxp runs globals S l_cdr a iterate.
Proof. introv D. unfolds. rewrite~ fold_left_listSxp_gen_cons. Qed.

Lemma match_rresult_pass : forall A B C S r (cont : _ -> A -> result (normal_return B C)),
  let%return a := result_rsuccess S r using S in cont S a = cont S r.
Proof. introv. reflexivity. Qed.

Lemma match_rresult_pass_return : forall A B C S r (cont : _ -> C -> result (normal_return B A)),
  let%return a := result_rreturn S r using S in cont S a = result_rreturn S r.
Proof. introv. reflexivity. Qed.

Lemma match_rresult_abort : forall A B C r (cont : _ -> A -> result (normal_return B C)) H,
  let%return a := r using S in cont S a = convert_type_monad r H.
Proof. introv. destruct r; (reflexivity || inverts~ H). Qed.

Lemma match_rresult_aborts : forall A B C r (cont : state -> A -> result (normal_return B C)),
  aborting_result r ->
  aborting_result (let%return a := r using S in cont S a).
Proof. introv H. destruct r; (reflexivity || inverts~ H). Qed.

Lemma exit_rresult_pass : forall A B S r (cont : _ -> A -> result B),
  let%exit a := result_rsuccess S r using S in cont S a = cont S r.
Proof. introv. reflexivity. Qed.

Lemma exit_rresult_pass_return : forall A B S r (cont : _ -> A -> result B),
  let%exit a := result_rreturn S r using S in cont S a = result_success S r.
Proof. introv. reflexivity. Qed.

Lemma exit_rresult_abort : forall A B r (cont : _ -> A -> result B) H,
  let%exit a := r using S in cont S a = convert_type_monad r H.
Proof. introv. destruct r; (reflexivity || inverts~ H). Qed.

Lemma exit_rresult_aborts : forall A B r (cont : state -> A -> result B),
  aborting_result r ->
  aborting_result (let%exit a := r using S in cont S a).
Proof. introv H. destruct r; (reflexivity || inverts~ H). Qed.

Lemma continue_and_condition_pass : forall A B S (r : A) expr,
  continue_and_condition S (normal_result (B := B) r) expr = expr S r.
Proof. introv. reflexivity. Qed.

Lemma continue_and_condition_pass_return : forall A B S (r : B) expr,
  continue_and_condition S (return_result (A := A) r) expr = result_success S false.
Proof. introv. reflexivity. Qed.

Lemma get_success_pass : forall A B S (r : A) expr,
  get_success S (normal_result (B := B) r) expr = expr S r.
Proof. introv. reflexivity. Qed.

Lemma get_success_pass_return : forall A B S (r : B) expr,
  get_success S (return_result (A := A) r) expr = result_rreturn S r.
Proof. introv. reflexivity. Qed.


(** *** Long Jumps **)

Lemma set_longjump_simplify : forall A runs S mask cjmpbuf f (a : A),
  f S mask = result_success S a ->
  set_longjump runs S mask cjmpbuf f = result_success S a.
Proof. introv E. unfolds. rewrite~ E. Qed.

Lemma set_longjump_result : forall A runs S mask cjmpbuf (f : _ -> _ -> result A)
    P_success P_error P_longjump,
  (forall S S' mask',
    f S mask = result_longjump S' cjmpbuf mask' ->
    result_prop P_success P_error P_longjump (runs_set_longjump runs S' mask' cjmpbuf f)) ->
  (forall S n mask',
    f S mask = result_longjump S cjmpbuf mask' ->
    n <> cjmpbuf ->
    P_longjump S n mask') ->
  result_prop P_success P_error P_longjump (f S mask) ->
  result_prop P_success P_error P_longjump (set_longjump runs S mask cjmpbuf f).
Proof.
  introv I1 I2 R. unfolds set_longjump. destruct (f S mask) eqn: E; autos~.
  cases_if as C; autos~. fold_bool. rew_refl in C. substs. applys~ I1 E.
Qed.


(** *** Finite Loops **)

Lemma for_list_nil : forall A B S (a : A) body,
  for_list S a (nil : list B) body = result_success S a.
Proof. introv. reflexivity. Qed.

Lemma for_list_fold_left_abort : forall A B (a : result A) (l : list B) body H,
  fold_left (fun i r =>
    let%success a := r using S in
    body S a i) a l = convert_type_monad a H.
Proof.
  introv. induction l.
  - rewrite~ convert_type_monad_reflexive.
  - simpl. rewrite if_success_abort with (H := H). rewrite~ convert_type_monad_reflexive.
    rewrite IHl. rewrite~ convert_type_monad_reflexive.
Qed.

Lemma for_list_cons : forall A B S (a : A) (b : B) l body,
  for_list S a (b :: l) body
  = let%success r := body S a b using S in for_list S r l body.
Proof.
  introv. unfolds. simpl. destruct (body S a b) eqn:E; try reflexivity;
    asserts Ab: (aborting_result (body S a b)); rewrite E in *; try reflexivity;
    rewrite for_list_fold_left_abort with (H := Ab); reflexivity.
Qed.

Lemma for_list_last : forall A B S (a : A) (b : B) l body,
  for_list S a (l & b) body
  = let%success r := for_list S a l body using S in body S r b.
Proof. introv. unfolds. rew_list~. Qed.

Lemma for_list_concat : forall A B S (a : A) (l1 l2 : list B) body,
  for_list S a (l1 ++ l2) body
  = let%success r := for_list S a l1 body using S in for_list S r l2 body.
Proof.
  introv. unfolds. rew_list~. set (F := fold_left _ _ l1). destruct F eqn: E; try reflexivity;
    asserts Ab: (aborting_result F); rewrite E in *; try reflexivity;
    rewrite for_list_fold_left_abort with (H := Ab); reflexivity.
Qed.

Lemma for_loop_ends : forall A S (a : A) start last body,
  last < start ->
  for_loop S a start last body = result_success S a.
Proof. introv I. unfolds. cases_if as C; autos~. fold_bool. rew_refl in C. false C. math. Qed.

Lemma for_loop_forwards : forall A S (a : A) start last body,
  last >= start ->
  for_loop S a start last body
  = let%success a := body S a start using S in for_loop S a (1 + start) last body.
Proof.
  introv I. unfolds. cases_if as C.
  - fold_bool. rew_refl in C. false. math.
  - clear C. cases_if as C; fold_bool; rew_refl in C.
    + asserts: (last = start); [ math | substs ].
      asserts_rewrite ((1 + Z.to_nat start - start = 1)%nat).
      * rewrite Nat2Z.id. math.
      * simpl. rewrite~ for_list_cons.
    + asserts: (1 + Z.to_nat last - start > 1)%nat.
      * rewrite Nat2Z.id. math.
      * destruct (1 + Z.to_nat last - start)%nat as [|n] eqn: E; try (false; math).
        simpl. rewrite~ for_list_cons. fequals. extens. introv.
        asserts_rewrite~ (Z.to_nat last - start = n)%nat. math.
Qed.

Lemma for_loop_backwards : forall A S (a : A) start last body,
  last >= start ->
  for_loop S a start last body
  = let%success a := for_loop S a start (last - 1) body using S in body S a last.
Proof.
  introv I. unfolds. cases_if as C.
  - fold_bool. rew_refl in C. false. math.
  - clear C. cases_if as C; fold_bool; rew_refl in C.
    + asserts: (last = start); [ math | substs ].
      asserts_rewrite ((1 + Z.to_nat start - start = 1)%nat).
      * rewrite Nat2Z.id. math.
      * simpl. rewrite~ for_list_cons. destruct~ body.
    + asserts_rewrite (seq start (1 + Z.to_nat last - start) = seq start (1 + Z.to_nat (last - 1) - start) & last).
      * asserts_rewrite ((1 + Z.to_nat (last - 1) - start) = 1 + (1 + Z.to_nat last - start))%nat.
        -- skip. (* TODO *)
        -- skip. (* TODO: Lemma about seq. *)
      * rewrite~ for_list_last.
Qed.

Lemma for_loop_split : forall A S (a : A) start last k body,
  start <= k ->
  k <= last ->
  for_loop S a start last body
  = let%success r := for_loop S a start k body using S in for_loop S a k last body.
Proof.
Admitted. (* TODO *)

(* FIXME: Something for for_array? *)


(** ** Tactics **)

Ltac get_pass_lemma t :=
  match get_head t with
  | add_stack => add_stack_pass
  | if_success => if_success_pass
  | if_defined_msg => if_defined_msg_pass
  | if_defined => if_defined_pass
  | if_is_prim => if_is_prim_pass
  | if_is_sym => if_is_sym_pass
  | if_is_list => if_is_list_pass
  | if_is_env => if_is_env_pass
  | if_is_clo => if_is_clo_pass
  | if_is_prom => if_is_prom_pass
  | read_cell_Vector_SExpRec => read_cell_Vector_SExpRec_pass
  | update_Vector_SExpRec_cell => update_Vector_SExpRec_cell_pass
  | let_VectorChar => let_VectorChar_pass
  | let_VectorLogical => let_VectorLogical_pass
  | let_VectorInteger => let_VectorInteger_pass
  | let_VectorReal => let_VectorReal_pass
  | let_VectorComplex => let_VectorComplex_pass
  | let_VectorPointer => let_VectorPointer_pass
  | fold_left_listSxp_gen => constr:(>> fold_left_listSxp_gen_nil fold_left_listSxp_gen_cons)
  | fold_left_listSxp => constr:(>> fold_left_listSxp_nil fold_left_listSxp_cons)
  | match_rresult => constr:(>> match_rresult_pass match_rresult_pass_return)
  | exit_rresult => constr:(>> exit_rresult_pass exit_rresult_pass_return)
  | continue_and_condition => constr:(>> continue_and_condition_pass continue_and_condition_pass_return)
  | get_success => constr:(>> get_success_pass get_success_pass_return)
  | for_list => constr:(>> for_list_nil for_list_cons for_list_last)
  end.

Ltac get_abort_lemma t :=
  match get_head t with
  | if_success => if_success_abort
  | if_defined_msg => if_defined_msg_abort
  | if_defined => if_defined_abort
  | if_is_prim => if_is_prim_abort
  | if_is_sym => if_is_sym_abort
  | if_is_list => if_is_list_abort
  | if_is_env => if_is_env_abort
  | if_is_clo => if_is_clo_abort
  | if_is_prom => if_is_prom_abort
  | read_cell_Vector_SExpRec => read_cell_Vector_SExpRec_abort
  | update_Vector_SExpRec_cell => update_Vector_SExpRec_cell_abort
  | let_VectorChar => let_VectorChar_abort
  | let_VectorLogical => let_VectorLogical_abort
  | let_VectorInteger => let_VectorInteger_abort
  | let_VectorReal => let_VectorReal_abort
  | let_VectorComplex => let_VectorComplex_abort
  | let_VectorPointer => let_VectorPointer_abort
  | while_loop => while_expr_abort
  | match_rresult => match_rresult_abort
  | exit_rresult => exit_rresult_abort
  end.

Ltac get_aborts_lemma t :=
  match get_head t with
  | add_stack => add_stack_aborts
  | if_success => if_success_aborts
  | if_defined_msg => if_defined_msg_aborts
  | if_defined => if_defined_aborts
  | if_is_prim => if_is_prim_aborts
  | if_is_sym => if_is_sym_aborts
  | if_is_list => if_is_list_aborts
  | if_is_env => if_is_env_aborts
  | if_is_clo => if_is_clo_aborts
  | if_is_prom => if_is_prom_aborts
  | read_cell_Vector_SExpRec => read_cell_Vector_SExpRec_aborts
  | let_VectorChar => let_VectorChar_aborts
  | let_VectorLogical => let_VectorLogical_aborts
  | let_VectorInteger => let_VectorInteger_aborts
  | let_VectorReal => let_VectorReal_aborts
  | let_VectorComplex => let_VectorComplex_aborts
  | let_VectorPointer => let_VectorPointer_aborts
  | while_loop => while_expr_aborts
  | match_rresult => match_rresult_aborts
  | exit_rresult => exit_rresult_aborts
  end.

Ltac get_simplify_lemma t :=
  match get_head t with
  | add_stack => constr:(>> add_stack_result add_stack_simplify)
  | if_success => if_success_result
  | while_loop => while_unfold
  | set_longjump => constr:(>> set_longjump_result set_longjump_simplify)
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

Ltac solve_premises :=
  solve [
    intros;
    first [
        reflexivity
      | discriminate
      | autos~
      | match goal with
        | |- _ < _ => math
        | |- _ > _ => math
        | |- _ <= _ => math
        | |- _ >= _ => math
        | |- (_ < _)%nat => math
        | |- (_ > _)%nat => math
        | |- (_ <= _)%nat => math
        | |- (_ >= _)%nat => math
        | |- (_ < _)%I => math
        | |- (_ > _)%I => math
        | |- (_ <= _)%I => math
        | |- (_ >= _)%I => math
        | |- context [ ArrayList.length ] => math
        end ] ].

Ltac unfold_monad_pass t :=
  let P := get_pass_lemma t in
  let L := list_boxer_of P in
  let rec try_all_lemmae L :=
    match L with
    | boxer ?S :: ?L' =>
      first [
          rewrite P; try solve_premises
        | try_all_lemmae L' ]
    end in
  try_all_lemmae L.

Ltac unfold_monad_simplify t :=
  let L := get_simplify_lemma t in
  let L := list_boxer_of L in
  let rec try_all_lemmae L :=
    match L with
    | boxer ?S :: ?L' =>
      first [
          solve [ (apply* S || rewrite* S); solve_premises ]
        | (apply S || rewrite S); try solve_premises
        | try_all_lemmae L' ]
    end in
  try_all_lemmae L.

Ltac unfold_monad_with_subresult t r :=
  first [
      result_computed r;
      first [
          unfold_monad_pass t
        | let A := get_abort_lemma t in
          first [
              rewrite A; try solve_premises
            | rewrite rewrite_impossible_result with (r := t);
              [| apply A; try solve_premises ];
              unfolds_get_impossible
            | let H := fresh "Habort" in
              asserts H: (aborting_result r);
              [ first [
                    reflexivity
                  | let AT := get_aborts_lemma t in
                    apply AT; try solve_premises ]
              | rewrite A with H ] ] ]
    | unfold_monad_simplify t ].

Ltac unfold_monad_without_subresult t :=
  first [
      unfold_monad_pass t
    | let A := get_abort_lemma t in
      first [
          rewrite A; try solve_premises
        | rewrite rewrite_impossible_result with (r := t);
          [| apply A; try solve_premises ];
          unfolds_get_impossible ]
    | unfold_monad_simplify t ].

Ltac deal_with_bottom :=
  first [
      reflexivity
    | autos* ].

Ltac make_runs_deeper r :=
  let rew n :=
    first [
        asserts_rewrite (S n = 1 + n)%nat in *; [ reflexivity |]
      | asserts_rewrite (S n = 1 + n) in *; [ reflexivity |] ] in
  match r with
  | runs (1 + ?n) ?globals => idtac
  | runs (S ?n) ?globals => rew n
  | runs ?n ?globals =>
    let n' := fresh n in
    destruct n as [|n'];
    [ deal_with_bottom | rew n']
  end.

Ltac unfold_runs :=
  match goal with
  | |- context [ runs_while_loop ?runs ?S ?a ?expr ?stat ] =>
    make_runs_deeper runs
  | |- context [ runs_set_longjump ?runs ?S ?t ?n ?f ] =>
    make_runs_deeper runs
  | |- context [ runs_eval ?runs ?S ?e ?rho ] =>
    make_runs_deeper runs
  | |- context [ runs_inherits ?runs ?S ?e ?str ] =>
    make_runs_deeper runs
  | |- context [ runs_getAttrib ?runs ?S ?e ?a ] =>
    make_runs_deeper runs
  | |- context [ runs_setAttrib ?runs ?S ?e ?a ?v ] =>
    make_runs_deeper runs
  | |- context [ runs_R_cycle_detected ?runs ?S ?e ?r ] =>
    make_runs_deeper runs
  | |- context [ runs_duplicate1 ?runs ?S ?e ?deep ] =>
    make_runs_deeper runs
  | |- context [ runs_stripAttrib ?runs ?S ?e ?a ] =>
    make_runs_deeper runs
  | |- context [ runs_evalseq ?runs ?S ?e ?rho ?local ?loc ] =>
    make_runs_deeper runs
  | |- context [ runs_R_isMissing ?runs ?S ?e ?rho ] =>
    make_runs_deeper runs
  | |- context [ runs_AnswerType ?runs ?S ?e ?re ?us ?da ?ca ] =>
    make_runs_deeper runs
  | |- context [ runs_ListAnswer ?runs ?S ?e ?re ?bi ?da ] =>
    make_runs_deeper runs
  | |- context [ runs_StringAnswer ?runs ?S ?e ?bi ?da ] =>
    make_runs_deeper runs
  | |- context [ runs_LogicalAnswer ?runs ?S ?e ?bi ?da ] =>
    make_runs_deeper runs
  | |- context [ runs_IntegerAnswer ?runs ?S ?e ?bi ?da ] =>
    make_runs_deeper runs
  | |- context [ runs_RealAnswer ?runs ?S ?e ?bi ?da ] =>
    make_runs_deeper runs
  | |- context [ runs_ComplexAnswer ?runs ?S ?e ?bi ?da ] =>
    make_runs_deeper runs
  | |- context [ runs_RawAnswer ?runs ?S ?e ?bi ?da ] =>
    make_runs_deeper runs
  | |- context [ runs_R_FunTab ?runs ] =>
    make_runs_deeper runs
  end.

Ltac unfold_definitions :=
  match goal with
  | |- context [ result_skip ?S ] =>
    unfolds result_skip
  | |- context [ if_then_else_success ?b ?c1 ?c2 ] =>
    unfolds if_then_else_success
  | |- context [ if_then_success ?b ?c ?cont ] =>
    unfolds if_then_success
  | |- context [ if_option_defined ?c ?cont1 ?cont2 ] =>
    unfolds if_option_defined
  | |- context [ read_as_prim ?S ?e ?cont ] =>
    unfolds read_as_prim
  | |- context [ read_as_sym ?S ?e ?cont ] =>
    unfolds read_as_sym
  | |- context [ read_as_list ?S ?e ?cont ] =>
    unfolds read_as_list
  | |- context [ read_as_list_all ?S ?e ?cont ] =>
    unfolds read_as_list_all
  | |- context [ read_as_list_components ?S ?e ?cont ] =>
    unfolds read_as_list_components
  | |- context [ read_as_env ?S ?e ?cont ] =>
    unfolds read_as_env
  | |- context [ read_as_clo ?S ?e ?cont ] =>
    unfolds read_as_clo
  | |- context [ read_as_prom ?S ?e ?cont ] =>
    unfolds read_as_prom
  | |- context [ read_as_VectorChar ?S ?e ?cont ] =>
    unfolds read_as_VectorChar
  | |- context [ read_nth_cell_VectorChar ?S ?e_ ?n ?cont ] =>
    unfolds read_nth_cell_VectorChar
  | |- context [ read_nth_cell_Char ?S ?e ?n ?cont ] =>
    unfolds read_nth_cell_VectorChar
  | |- context [ write_VectorChar ?S ?e ?v ?cont ] =>
    unfolds write_VectorChar
  | |- context [ write_nth_cell_VectorChar ?S ?e ?n ?c ?cont ] =>
    unfolds write_nth_cell_VectorChar
  | |- context [ read_as_VectorLogical ?S ?e ?cont ] =>
    unfolds read_as_VectorLogical
  | |- context [ read_nth_cell_VectorLogical ?S ?e_ ?n ?cont ] =>
    unfolds read_nth_cell_VectorLogical
  | |- context [ read_nth_cell_Logical ?S ?e ?n ?cont ] =>
    unfolds read_nth_cell_VectorLogical
  | |- context [ write_VectorLogical ?S ?e ?v ?cont ] =>
    unfolds write_VectorLogical
  | |- context [ write_nth_cell_VectorLogical ?S ?e ?n ?c ?cont ] =>
    unfolds write_nth_cell_VectorLogical
  | |- context [ read_as_VectorInteger ?S ?e ?cont ] =>
    unfolds read_as_VectorInteger
  | |- context [ read_nth_cell_VectorInteger ?S ?e_ ?n ?cont ] =>
    unfolds read_nth_cell_VectorInteger
  | |- context [ read_nth_cell_Integer ?S ?e ?n ?cont ] =>
    unfolds read_nth_cell_VectorInteger
  | |- context [ write_VectorInteger ?S ?e ?v ?cont ] =>
    unfolds write_VectorInteger
  | |- context [ write_nth_cell_VectorInteger ?S ?e ?n ?c ?cont ] =>
    unfolds write_nth_cell_VectorInteger
  | |- context [ read_as_VectorReal ?S ?e ?cont ] =>
    unfolds read_as_VectorReal
  | |- context [ read_nth_cell_VectorReal ?S ?e_ ?n ?cont ] =>
    unfolds read_nth_cell_VectorReal
  | |- context [ read_nth_cell_Real ?S ?e ?n ?cont ] =>
    unfolds read_nth_cell_VectorReal
  | |- context [ write_VectorReal ?S ?e ?v ?cont ] =>
    unfolds write_VectorReal
  | |- context [ write_nth_cell_VectorReal ?S ?e ?n ?c ?cont ] =>
    unfolds write_nth_cell_VectorReal
  | |- context [ read_as_VectorComplex ?S ?e ?cont ] =>
    unfolds read_as_VectorComplex
  | |- context [ read_nth_cell_VectorComplex ?S ?e_ ?n ?cont ] =>
    unfolds read_nth_cell_VectorComplex
  | |- context [ read_nth_cell_Complex ?S ?e ?n ?cont ] =>
    unfolds read_nth_cell_VectorComplex
  | |- context [ write_VectorComplex ?S ?e ?v ?cont ] =>
    unfolds write_VectorComplex
  | |- context [ write_nth_cell_VectorComplex ?S ?e ?n ?c ?cont ] =>
    unfolds write_nth_cell_VectorComplex
  | |- context [ read_as_VectorPointer ?S ?e ?cont ] =>
    unfolds read_as_VectorPointer
  | |- context [ read_nth_cell_VectorPointer ?S ?e_ ?n ?cont ] =>
    unfolds read_nth_cell_VectorPointer
  | |- context [ read_nth_cell_Pointer ?S ?e ?n ?cont ] =>
    unfolds read_nth_cell_VectorPointer
  | |- context [ write_VectorPointer ?S ?e ?v ?cont ] =>
    unfolds write_VectorPointer
  | |- context [ write_nth_cell_VectorPointer ?S ?e ?n ?c ?cont ] =>
    unfolds write_nth_cell_VectorPointer
  | |- context [ map_pointer ?S ?map ?p ?cont ] =>
    unfolds map_pointer
  | |- context [ map_list ?S ?f ?p ?cont ] =>
    unfolds map_list
  | |- context [ set_car ?S ?car ?p ?f ] =>
    unfolds set_car
  | |- context [ set_cdr ?S ?cdr ?p ?f ] =>
    unfolds set_cdr
  | |- context [ set_tag ?S ?tag ?p ?f ] =>
    unfolds set_tag
  | |- context [ result_rskip ?S ] =>
    unfolds result_rskip
  | _ => unfold_runs
  end.

Ltac unfold_monad :=
  match goal with
  | |- context [ add_stack ?fname ?r ] =>
    unfold_monad_with_subresult (add_stack fname r) r
  | |- context [ if_success ?r ?cont ] =>
    unfold_monad_with_subresult (if_success r cont) r
  | |- context [ if_defined_msg ?msg ?S ?o ?cont ] =>
    unfold_monad_without_subresult (if_defined_msg msg S o cont)
  | |- context [ if_defined ?S ?o ?cont ] =>
    unfold_monad_without_subresult (if_defined S o cont)
  | |- context [ if_is_prim ?S ?e_ ?cont ] =>
    unfold_monad_without_subresult (if_is_prim S e_ cont)
  | |- context [ if_is_sym ?S ?e_ ?cont ] =>
    unfold_monad_without_subresult (if_is_sym S e_ cont)
  | |- context [ if_is_list ?S ?e_ ?cont ] =>
    unfold_monad_without_subresult (if_is_list S e_ cont)
  | |- context [ if_is_env ?S ?e_ ?cont ] =>
    unfold_monad_without_subresult (if_is_env S e_ cont)
  | |- context [ if_is_clo ?S ?e_ ?cont ] =>
    unfold_monad_without_subresult (if_is_clo S e_ cont)
  | |- context [ if_is_prom ?S ?e_ ?cont ] =>
    unfold_monad_without_subresult (if_is_prom S e_ cont)
  | |- context [ read_cell_Vector_SExpRec ?S ?v ?n ?cont ] =>
    unfold_monad_without_subresult (read_cell_Vector_SExpRec S v n cont)
  | |- context [ update_Vector_SExpRec_cell ?v ?n ?c ] =>
    unfold_monad_without_subresult (update_Vector_SExpRec_cell v n c)
  | |- context [ let_VectorChar ?S ?e_ ?cont ] =>
    unfold_monad_without_subresult (let_VectorChar S e_ cont)
  | |- context [ let_VectorLogical ?S ?e_ ?cont ] =>
    unfold_monad_without_subresult (let_VectorLogical S e_ cont)
  | |- context [ let_VectorInteger ?S ?e_ ?cont ] =>
    unfold_monad_without_subresult (let_VectorInteger S e_ cont)
  | |- context [ let_VectorReal ?S ?e_ ?cont ] =>
    unfold_monad_without_subresult (let_VectorReal S e_ cont)
  | |- context [ let_VectorComplex ?S ?e_ ?cont ] =>
    unfold_monad_without_subresult (let_VectorComplex S e_ cont)
  | |- context [ let_VectorPointer ?S ?e_ ?cont ] =>
    unfold_monad_without_subresult (let_VectorPointer S e_ cont)
  | |- context [ while_loop ?runs ?S ?a ?expr ?stat ] =>
    make_runs_deeper runs;
    unfold_monad_without_subresult (while_loop runs S a expr stat)
  | |- context [ runs_fold_left_listSxp_gen ?runs ] =>
    make_runs_deeper runs;
    rewrite~ runs_fold_left_listSxp_gen_eq
  | |- context [ fold_left_listSxp_gen ?runs ?globals ?S ?l ?a ?iterate ] =>
    unfold_monad_without_subresult (fold_left_listSxp_gen runs globals S l a iterate)
  | |- context [ runs_fold_left_listSxp ?runs ] =>
    make_runs_deeper runs;
    rewrite~ runs_fold_left_listSxp_eq
  | |- context [ fold_left_listSxp ?runs ?globals ?S ?l ?a ?iterate ] =>
    unfold_monad_without_subresult (fold_left_listSxp runs globals S l a iterate)
  | |- context [ match_rresult ?r ?cont ] =>
    unfold_monad_with_subresult (match_rresult r cont) r
  | |- context [ exit_rresult ?r ?cont ] =>
    unfold_monad_with_subresult (exit_rresult r cont) r
  | |- context [ continue_and_condition ?S ?r ?cont ] =>
    unfold_monad_without_subresult (continue_and_condition S r cont)
  | |- context [ get_success ?S ?r ?cont ] =>
    unfold_monad_without_subresult (get_success S r cont)
  | _ => unfold_definitions
  end.

Ltac simplifyR :=
  repeat (unfold_monad; repeat let_simpl).

Ltac cutR P :=
  match goal with
  | |- result_prop ?P_success ?P_error ?P_longjump (if_success ?r ?cont) =>
    first [
        eapply if_success_result with (P_success := P)
      | eapply if_success_result with (P_success := fun S _ => P S) ]
  | |- result_prop ?P_success ?P_error ?P_longjump (set_longjump ?runs ?S ?mask ?cjmpbuf ?f) =>
    first [
        eapply set_longjump_result with (P_longjump := P)
      | eapply set_longjump_result with (P_longjump := fun S _ _ => P S) ]
  end.

