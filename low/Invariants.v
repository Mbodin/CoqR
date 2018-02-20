(** Invariants.
  Contains the proofs of some invariants respected by the functions
  defined in Rcore, Rinit, and Rfeatures. **)

Set Implicit Arguments.
Require Import TLC.LibBag.
Require Export Rinit Rfeatures Path.


(** * Predicates to speak about the memory **)

(** ** A pointer is valid **)

Definition bound (S : state) p := exists p_, read_SExp S p = Some p_.

(** ** A pointer is associated a given type **)

Definition may_have_type (S : state) p l :=
  exists p_, read_SExp S p = Some p_ /\ type p_ \in l.

Lemma may_have_type_bound : forall S p l,
  may_have_type S p l ->
  bound S p.
Proof. introv (p_&E&?). exists* p_. Qed.

Lemma may_have_type_nil : forall S p,
  ~ may_have_type S p nil.
Proof. introv (p_&E&M). applys~ BagInEmpty_list M. Qed.

Lemma may_have_type_merge : forall S p l1 l2,
  may_have_type S p l1 ->
  may_have_type S p l2 ->
  may_have_type S p (l1 \n l2).
Proof.
  introv (p1_&E1&M1) (p2_&E2&M2).
  rewrite E1 in E2. inverts E2. exists p2_. splits~.
  rewrite~ BagInter_list.
Qed.

(** ** List pointers **)

Inductive list_type (S : state) p l_t l_car l_tag : Prop := make_list_type {
  list_type_intro : exists p_ header car cdr tag,
    read_SExp S p = Some p_
    /\ p_ = make_NonVector_SExpRec header (make_ListSxp_struct car cdr tag)
    /\ type p_ \in l_t
    /\ may_have_type S car l_car
    /\ list_type S cdr l_t l_car l_tag
    /\ may_have_type S tag l_tag
  }.

Lemma list_type_may_have_type : forall S p l_t l_car l_tag,
  list_type S p l_t l_car l_tag ->
  may_have_type S p l_t.
Proof. introv [(p_&?&?&?&?&?&?&?&?&?&?)]. exists* p_. Qed.

Lemma list_type_merge : forall S p l1_t l2_t l1_car l2_car l1_tag l2_tag,
  list_type S p l1_t l1_car l1_tag ->
  list_type S p l2_t l2_car l2_tag ->
  list_type S p (l1_t \n l2_t) (l1_car \n l2_car) (l1_tag \n l2_tag).
Proof.
  introv T1 T2. gen l2_t l2_car l2_tag.
  induction T1 as [(p1_&h1&car1&cdr1&tag1&E1&M1&H1&A1&L1&T1)].
  introv [(p2_&h2&car2&cdr2&tag2&E2&M2&H2&A2&L2&T2)].
  constructors. exists p1_ h1 car1 cdr1 tag1.
  rewrite E1 in E2. inversion E2 as [E3]. rewrite E3 in *.
  rewrite M2 in M1. inverts M1. splits~.
  - rewrite~ BagInter_list.
  - apply~ may_have_type_merge.
  - 
  - apply~ may_have_type_merge.
Qed.


(** * Invariants about the state. **)

(* Inductive null_pointer_exceptions : path -> Prop := . *)

Record safe_SExpRec S (e_ : SExpRec) := make_safe_SExpRec {
    SExpType_corresponds_to_data_NilSxp :
      type e_ = NilSxp ->
      exists header car cdr tag,
        e_ = make_NonVector_SExpRec header (make_ListSxp_struct car cdr tag)
        /\ may_have_type S car [NilSxp]
        /\ may_have_type S cdr [NilSxp]
        /\ may_have_type S tag [NilSxp] ;
    SExpType_corresponds_to_data_SymSxp :
      type e_ = SymSxp ->
      exists header pname value internal,
        e_ = make_NonVector_SExpRec header (make_SymSxp_struct pname value internal)
        /\ may_have_type S pname [CharSxp]
        (*/\ may_have_type S value [(*TODO*)]
        /\ may_have_type S internal [(*TODO*)]*) ;
    SExpType_corresponds_to_data_ListSxp :
      type e_ = ListSxp ->
      exists header car cdr tag,
        e_ = make_NonVector_SExpRec header (make_ListSxp_struct car cdr tag)
        /\ may_have_type S cdr [ListSxp]
        /\ may_have_type S tag [NilSxp ; CharSxp] ;
    SExpType_corresponds_to_data_CloSxp :
      type e_ = CloSxp ->
      exists header formals body env,
        e_ = make_NonVector_SExpRec header (make_CloSxp_struct formals body env)
        /\ may_have_type S formals [NilSxp ; ListSxp]
        (*/\ may_have_type S body [(*TODO*)]*)
        /\ may_have_type S env [EnvSxp] ;
    SExpType_corresponds_to_data_EnvSxp :
      type e_ = EnvSxp ->
      exists header frame enclos,
        e_ = make_NonVector_SExpRec header (make_EnvSxp_struct frame enclos)
        /\ may_have_type S frame [NilSxp ; ListSxp]
        /\ may_have_type S enclos [EnvSxp] ;
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
          may_have_type S a [CharSxp] ;
    SExpType_corresponds_to_data_DotSxp :
      type e_ = DotSxp ->
      exists header car cdr tag,
        e_ = make_NonVector_SExpRec header (make_ListSxp_struct car cdr tag)
        (*/\ may_have_type S car [(*TODO*)]*)
        /\ may_have_type S cdr [ListSxp]
        /\ may_have_type S tag [NilSxp] ;
    SExpType_not_AnySxp :
      type e_ <> AnySxp ;
    SExpType_corresponds_to_data_VecSxp :
      type e_ = VecSxp ->
      exists header array,
        e_ = SExpRec_VectorPointer (make_Vector_SExpRec header
               (make_VecSxp_struct (ArrayList.length array) array))
        (*/\ forall a,
          Mem a (ArrayList.to_list array) ->
          may_have_type S a [(*TODO*)]*) ;
    SExpType_corresponds_to_data_ExprSxp :
      type e_ = ExprSxp ->
      exists header array,
        e_ = SExpRec_VectorPointer (make_Vector_SExpRec header
               (make_VecSxp_struct (ArrayList.length array) array))
        (*/\ forall a,
          Mem a (ArrayList.to_list array) ->
          may_have_type S a [(*TODO*)]*) ;
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

Record safe_pointer S p := make_safe_pointer {
    pointer_bound : bound S p ;
    no_null_pointer_along_path : forall path,
      (* ~ null_pointer_exceptions ?? -> *)
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
    safe_entry_points : forall e p,
      move_along_entry_point e S = Some p ->
      safe_pointer S p
  }.


(** * Tactics **)

(** ** Simplifying tactics **)

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

(* TODO *)

(* I think that it would be easy to use tactics to check that [setup_Rmainloop]
  is indeed of the form [result_success S globals] or something like that. *)

(** It would be nice to prove that the read-eval-print-loop can not
  return a [result_impossible]. **)

(** If runs returns a result, then adding fuel does not change it. **)

