(** Invariants.
  Contains the proofs of some invariants respected by the functions
  defined in Rcore, Rinit, and Rfeatures. **)

Set Implicit Arguments.
Require Import TLC.LibBag.
Require Export Rinit Rfeatures Path.

Open Scope list_scope. (* FIXME: How to disable some notations of LibBag? *)


(** * Predicates to speak about the memory **)

(** ** A pointer is valid **)

Definition bound_such_that (S : state) P p :=
  exists p_, read_SExp S p = Some p_ /\ P p_.

Definition bound S := bound_such_that S (fun _ => True).

Lemma bound_such_that_weaken : forall S (P1 P2 : _ -> Prop) p,
  (forall p_, P1 p_ -> P2 p_) ->
  bound_such_that S P1 p ->
  bound_such_that S P2 p.
Proof. introv I (p_&E&H). exists* p_. Qed.


(** ** Typed pointers **)

Definition may_have_types S l :=
  bound_such_that S (fun p_ => type p_ \in l).

Lemma may_have_types_bound : forall S p l,
  may_have_types S l p ->
  bound S p.
Proof. introv. apply* bound_such_that_weaken. Qed.

Lemma may_have_types_nil : forall S p,
  ~ may_have_types S nil p.
Proof. introv (p_&E&M). applys~ BagInEmpty_list M. Qed.

Lemma may_have_types_merge : forall S p l1 l2,
  may_have_types S l1 p ->
  may_have_types S l2 p ->
  may_have_types S (l1 \n l2) p.
Proof.
  introv (p1_&E1&M1) (p2_&E2&M2).
  rewrite E1 in E2. inverts E2. exists p2_. splits~.
  rewrite~ BagInter_list.
Qed.

Lemma may_have_types_weaken : forall S p l1 l2,
  may_have_types S l1 p ->
  l1 \c l2 ->
  may_have_types S l2 p.
Proof. introv T I. applys~ bound_such_that_weaken T. introv M. applys~ BagInIncl M I. Qed.


(** ** List pointers **)

Definition list_type_head P S l_t l_car l_tag (p_ : SExpRec) :=
  exists header car cdr tag,
    p_ = make_NonVector_SExpRec header (make_ListSxp_struct car cdr tag)
    /\ type p_ \in l_t
    /\ may_have_types S l_car car
    /\ P S l_t l_car l_tag cdr
    /\ may_have_types S l_tag tag.

Definition list_type_step P (S : state) l_t l_car l_tag :=
  bound_such_that S (list_type_head P S l_t l_car l_tag).

Inductive list_type (S : state) : list SExpType -> list SExpType -> list SExpType -> SEXP -> Prop :=
  | list_type_nil : forall p l_t l_car l_tag,
    may_have_types S ([NilSxp]) p ->
    list_type S l_t l_car l_tag p
  | list_type_cons : forall p l_t l_car l_tag,
    list_type_step list_type S l_t l_car l_tag p ->
    list_type S l_t l_car l_tag p
  .

Definition list_head := list_type_head list_type.

Fixpoint list_type_ind' S
    (P : list SExpType -> list SExpType -> list SExpType -> SEXP -> Prop)
    (f_nil : forall p l_t l_car l_tag,
       may_have_types S ([NilSxp]) p ->
       P l_t l_car l_tag p)
    (f_cons : forall p l_t l_car l_tag p_ header car cdr tag,
       read_SExp S p = Some p_ ->
       p_ = make_NonVector_SExpRec header (make_ListSxp_struct car cdr tag) ->
       type p_ \in l_t ->
       may_have_types S l_car car ->
       list_type S l_t l_car l_tag cdr ->
       may_have_types S l_tag tag ->
       P l_t l_car l_tag cdr ->
       P l_t l_car l_tag p)
    l_t l_car l_tag p (HL : list_type S l_t l_car l_tag p) : P l_t l_car l_tag p.
  refine (
    match HL in list_type _ l_t l_car l_tag p return P l_t l_car l_tag p with
    | @list_type_nil _ p l_t l_car l_tag N =>
      f_nil p l_t l_car l_tag N
    | @list_type_cons _ p l_t l_car l_tag N => _
    end).
  destruct N as (p_&E&h&car&cdr&tag&M&H&A&L&T).
  refine (f_cons p l_t l_car l_tag _ _ _ _ _ E M H A L T _).
  applys~ list_type_ind' f_nil f_cons.
Defined.

Lemma list_type_may_have_types : forall S p l_t l_car l_tag,
  list_type S l_t l_car l_tag p ->
  may_have_types S (l_t \u [NilSxp]) p.
Proof.
  introv I. destruct~ I as [? ? ? ? I|? ? ? ? (p_&E&h&car&cdr&tag&M&H&A&L&T)].
  - applys may_have_types_weaken I. apply~ BagUnionIncl_right.
  - exists p_. splits~. applys~ BagInIncl H. apply~ BagUnionIncl_left.
Qed.

Lemma list_type_merge : forall S p l1_t l2_t l1_car l2_car l1_tag l2_tag,
  list_type S l1_t l1_car l1_tag p ->
  list_type S l2_t l2_car l2_tag p ->
  list_type S (l1_t \n l2_t) (l1_car \n l2_car) (l1_tag \n l2_tag) p.
Proof.
  introv T1 T2. gen l2_t l2_car l2_tag.
  induction T1 as [? ? ? ? I1|? ? ? ? p1_ h1 car1 cdr1 tag1 E1 M1 H1 A1 L1 T1 IH]
    using list_type_ind'; introv T.
  - apply~ list_type_nil.
  - inverts T as T.
    + apply~ list_type_nil.
    + inverts T as (E2&h2&car2&cdr2&tag2&M2&H2&A2&L2&T2).
      rewrite E2 in E1. inversion E1 as [E1']. rewrite E1' in *.
      rewrite M1 in M2. inverts M2.
      apply list_type_cons. exists p1_. splits~. exists h2 car2 cdr2 tag2. splits~.
      * apply BagInter_list. splits~.
      * applys~ may_have_types_merge A1 A2.
      * applys~ may_have_types_merge T1 T2.
Qed.

Lemma list_type_weaken : forall S p l1_t l2_t l1_car l2_car l1_tag l2_tag,
  l1_t \c l2_t ->
  l1_car \c l2_car ->
  l1_tag \c l2_tag ->
  list_type S l1_t l1_car l1_tag p ->
  list_type S l2_t l2_car l2_tag p.
Proof.
  introv I1 I2 I3 T. gen l2_t l2_car l2_tag.
  induction T as [? ? ? ? I1|? ? ? ? p_ h car cdr tag E M H A L T IH]
    using list_type_ind'; introv Incl1 Incl2 Incl3.
  - apply~ list_type_nil.
  - apply list_type_cons. exists p_. splits~. exists h car cdr tag. splits~.
    + applys~ BagInIncl H Incl1.
    + applys~ may_have_types_weaken A Incl2.
    + applys~ may_have_types_weaken T Incl3.
Qed.


(** * Invariants about the state. **)

Record safe_SExpRec S (e_ : SExpRec) := make_safe_SExpRec {
    SExpType_corresponds_to_data_NilSxp :
      type e_ = NilSxp ->
      exists header car cdr tag,
        e_ = make_NonVector_SExpRec header (make_ListSxp_struct car cdr tag)
        /\ may_have_types S ([NilSxp]) car
        /\ may_have_types S ([NilSxp]) cdr
        /\ may_have_types S ([NilSxp]) tag ;
    SExpType_corresponds_to_data_SymSxp :
      type e_ = SymSxp ->
      exists header pname value internal,
        e_ = make_NonVector_SExpRec header (make_SymSxp_struct pname value internal)
        /\ may_have_types S ([CharSxp]) pname
        (*/\ may_have_types S ([(*TODO*)]) value
        /\ may_have_types S ([(*TODO*) internal])*) ;
    SExpType_corresponds_to_data_ListSxp :
      type e_ = ListSxp ->
      list_head S ([ListSxp]) all_storable_SExpTypes ([NilSxp ; CharSxp]) e_ ;
    SExpType_corresponds_to_data_CloSxp :
      type e_ = CloSxp ->
      exists header formals body env,
        e_ = make_NonVector_SExpRec header (make_CloSxp_struct formals body env)
        /\ list_type S ([ListSxp]) all_storable_SExpTypes(*TODO*) ([NilSxp ; CharSxp]) formals
        (*/\ may_have_types S ([(*TODO*)]) body*)
        /\ may_have_types S ([EnvSxp]) env ;
    SExpType_corresponds_to_data_EnvSxp :
      type e_ = EnvSxp ->
      exists header frame enclos,
        e_ = make_NonVector_SExpRec header (make_EnvSxp_struct frame enclos)
        /\ list_type S ([ListSxp]) all_storable_SExpTypes(*TODO*) ([NilSxp ; CharSxp]) frame
        /\ may_have_types S ([EnvSxp]) enclos ;
    SExpType_corresponds_to_data_SpecialSxp :
      type e_ = SpecialSxp ->
      exists header offset,
        e_ = make_NonVector_SExpRec header (make_PrimSxp_struct offset) ;
    SExpType_corresponds_to_data_BuiltinSxp :
      type e_ = BuiltinSxp ->
      exists header offset,
        e_ = make_NonVector_SExpRec header (make_PrimSxp_struct offset) ;
    SExpType_corresponds_to_data_CharSxp :
      type e_ = CharSxp ->
      exists header array,
        e_ = SExpRec_VectorChar (make_Vector_SExpRec header
               (make_VecSxp_struct (ArrayList.length array) array)) ;
    SExpType_corresponds_to_data_LglSxp :
      type e_ = LglSxp ->
      exists header array,
        e_ = SExpRec_VectorLogical (make_Vector_SExpRec header
               (make_VecSxp_struct (ArrayList.length array) array)) ;
    SExpType_corresponds_to_data_IntSxp :
      type e_ = IntSxp ->
      exists header array,
        e_ = SExpRec_VectorInteger (make_Vector_SExpRec header
               (make_VecSxp_struct (ArrayList.length array) array)) ;
    SExpType_corresponds_to_data_RealSxp :
      type e_ = RealSxp ->
      exists header array,
        e_ = SExpRec_VectorReal (make_Vector_SExpRec header
               (make_VecSxp_struct (ArrayList.length array) array)) ;
    SExpType_corresponds_to_data_CplxSxp :
      type e_ = CplxSxp ->
      exists header array,
        e_ = SExpRec_VectorComplex (make_Vector_SExpRec header
               (make_VecSxp_struct (ArrayList.length array) array)) ;
    SExpType_corresponds_to_data_StrSxp :
      type e_ = StrSxp ->
      exists header array,
        e_ = SExpRec_VectorPointer (make_Vector_SExpRec header
               (make_VecSxp_struct (ArrayList.length array) array))
        /\ forall a,
          Mem a (ArrayList.to_list array) ->
          may_have_types S ([CharSxp]) a ;
    SExpType_corresponds_to_data_DotSxp :
      type e_ = DotSxp ->
      list_head S ([ListSxp ; DotSxp]) all_storable_SExpTypes ([NilSxp]) e_ ;
    SExpType_not_AnySxp :
      type e_ <> AnySxp ;
    SExpType_corresponds_to_data_VecSxp :
      type e_ = VecSxp ->
      exists header array,
        e_ = SExpRec_VectorPointer (make_Vector_SExpRec header
               (make_VecSxp_struct (ArrayList.length array) array))
        (*/\ forall a,
          Mem a (ArrayList.to_list array) ->
          may_have_types S ([(*TODO*)]) a*) ;
    SExpType_corresponds_to_data_ExprSxp :
      type e_ = ExprSxp ->
      exists header array,
        e_ = SExpRec_VectorPointer (make_Vector_SExpRec header
               (make_VecSxp_struct (ArrayList.length array) array))
        (*/\ forall a,
          Mem a (ArrayList.to_list array) ->
          may_have_types S ([(*TODO*)]) a*) ;
    (** The following four types have not been implemented. **)
    SExpType_corresponds_to_data_BcodeSxp :
      type e_ = BcodeSxp -> True ;
    SExpType_corresponds_to_data_ExtptrSxp :
      type e_ = ExtptrSxp -> True ;
    SExpType_corresponds_to_data_RawSxp :
      type e_ = RawSxp -> True ;
    SExpType_corresponds_to_data_S4Sxp :
      type e_ = S4Sxp -> True ;
    (** The following two types are only used in the garbagecollector,
      which has not been formalised. **)
    SExpType_not_NewSxp :
      type e_ <> NewSxp ;
    SExpType_not_FreeSxp :
      type e_ <> FreeSxp ;
    (** The following type is not possible in C in an object, as it
      would need more bytes than actually present.  It is rewriten in
      practise into CloSxp if someone tries to put it into an
      object. **)
    SExpType_not_FunSxp :
      type e_ <> FunSxp
  }.

Inductive null_pointer_exceptions_entry : entry_point -> Prop :=
  | null_pointer_exceptions_context_promargs :
    null_pointer_exceptions_entry
      (Econtext (context_path_entry Pstate_context) Scontext_promargs)
  | null_pointer_exceptions_context_callfun :
    null_pointer_exceptions_entry
      (Econtext (context_path_entry Pstate_context) Scontext_callfun)
  | null_pointer_exceptions_context_sysparent :
    null_pointer_exceptions_entry
      (Econtext (context_path_entry Pstate_context) Scontext_sysparent)
  | null_pointer_exceptions_context_call :
    null_pointer_exceptions_entry
      (Econtext (context_path_entry Pstate_context) Scontext_call)
  | null_pointer_exceptions_context_cloenv :
    null_pointer_exceptions_entry
      (Econtext (context_path_entry Pstate_context) Scontext_cloenv)
  | null_pointer_exceptions_context_conexit :
    null_pointer_exceptions_entry
      (Econtext (context_path_entry Pstate_context) Scontext_conexit)
  | null_pointer_exceptions_context_returnValue : forall cp,
    null_pointer_exceptions_entry (Econtext cp Scontext_returnValue)
  .

Inductive null_pointer_exceptions_suffix : list path_step -> Prop :=
  | null_pointer_symbol_value :
    null_pointer_exceptions_suffix ([SNonVectorSym Ssym_value])
  (* FIXME: BindData_ans_ptr *)
  (* FIXME: BindData_ans_names *)
  .

Record safe_pointer S p := make_safe_pointer {
    pointer_bound : bound S p ;
    no_null_pointer_along_path : forall path,
      ~ null_pointer_exceptions_suffix path ->
      move_along_path_from path S p <> Some NULL ;
    safe_bindings_along_path : forall p e,
      move_along_path p S = Some e ->
      e <> NULL ->
      bound S e ;
    safe_SExpRec_along_path : forall p e e_,
      move_along_path p S = Some e ->
      read_SExp S e = Some e_ ->
      safe_SExpRec S e_
  }.

Record safe_state S := make_safe_state {
    no_null_pointer_entry_point : forall e,
      ~ null_pointer_exceptions_entry e ->
      move_along_entry_point e S <> Some NULL ;
    safe_entry_points : forall e p,
      move_along_entry_point e S = Some p ->
      p <> NULL ->
      safe_pointer S p ;
    only_one_nil : forall p1 p2,
      may_have_types S ([NilSxp]) p1 ->
      may_have_types S ([NilSxp]) p2 ->
      p1 = p2
  }.

Definition safe_result_param A P_success P_error P_longjump (r : result A) :=
  match r with
  | result_success S0 r => P_success S0 r
  | result_longjump S0 n c => P_longjump S0 n c
  | result_error_stack S0 st msg => P_error S0
  | result_impossible_stack S0 st msg => False
  | result_not_implemented_stack st msg => True
  | result_bottom S0 => True
  end.


(** * Tactics **)

(** ** Simplifying tactics **)

(** *** Simplifying lists **)

Ltac compute_is_in x l :=
  match l with
  | nil => constr:(false)
  | x :: _ => constr:(true)
  | _ :: ?l =>
    let r := compute_is_in x l in r
  end.

Ltac compute_list_inter l1 l2 :=
  match l2 with
  | nil => l2
  | ?a :: ?l =>
    let isi := compute_is_in a l1 in
    let r := compute_list_inter l1 l in
    match isi with
    | true => constr:(a :: r)
    | false => r
    end
  end.

(** The following tactic computes any occurence of [l1 \n l2] in the goal. **)
Ltac simpl_list_inter :=
  let solve_eq :=
    clear; simpl;
    repeat
      (rewrite filter_cons;
       let C := fresh "C" in
       cases_if as C; fold_bool; rew_refl in C; tryfalse~;
       fequals; clear C) in
  repeat match goal with
  | |- context [ ?l1 \n ?l2 ] =>
    let l := compute_list_inter l1 l2 in
    asserts_rewrite (l1 \n l2 = l); [solve_eq|]
  | H : context [ ?l1 \n ?l2 ] |- _ =>
    let l := compute_list_inter l1 l2 in
    asserts_rewrite (l1 \n l2 = l) in H; [solve_eq|]
  end.


(** *** Simplifying the context **)

Ltac simplify_context :=
  match goal with
  | H1 : may_have_types ?S1 ?l1 ?p1,
    H2 : may_have_types ?S2 ?l2 ?p2 |- _ =>
    let H3 := fresh H1 H2 in
    lets H3: may_have_types_merge (rm H1) (rm H2);
    rename H3 into H1
  | H1 : list_type ?S1 ?p1 ?l1_t ?l1_car ?l1_tag,
    H2 : list_type ?S2 ?p2 ?l2_t ?l2_car ?l2_tag |- _ =>
    let H3 := fresh H1 H2 in
    lets H3: list_type_merge (rm H1) (rm H2);
    rename H3 into H1
  end; simpl_list_inter.




(* TODO *)

(* I think that it would be easy to use tactics to check that [setup_Rmainloop]
  is indeed of the form [result_success S globals] or something like that. *)

(** It would be nice to prove that the read-eval-print-loop can not
  return a [result_impossible]. **)

(** If runs returns a result, then adding fuel does not change it. **)

