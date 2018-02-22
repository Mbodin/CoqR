(** Invariants.
  States some invariants of R’s heap, as well as tactics to manipulate it. **)

Set Implicit Arguments.
Require Import TLC.LibBag.
Require Export Rinit Rfeatures Path MonadTactics.

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

Lemma may_have_types_cons : forall S t l p,
  may_have_types S (t :: l) p <->
  may_have_types S ([t]) p \/ may_have_types S l p.
Proof.
  introv. iff I.
  - lets (p_&E&M): (rm I). apply BagIn_cons in M. lets [M'|M']: (rm M).
    + left. exists p_. splits~. apply~ BagInSingle_list.
    + right. exists* p_.
  - lets [(p_&E&M)|(p_&E&M)]: (rm I); exists p_; splits~; apply* BagIn_cons.
    left. apply~ BagInSingle_list.
Qed.

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
  - applys~ may_have_types_weaken I. apply~ BagUnionIncl_right.
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

(** ** Invariants **)

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


(** ** Transitions between states **)

Definition conserve_old_binding S S' := forall p,
  bound S p ->
  bound_such_that S (fun e_ =>
    bound_such_that S' (fun e'_ => e_ = e'_) p) p.


(** ** Useful Lemmae **)

Lemma alloc_SExp_conserve_old_binding : forall S S' e e_,
  alloc_SExp S e_ = (S', e) ->
  conserve_old_binding S S'.
Proof.
  introv A (p_&E&_). exists p_. splits~. exists p_. splits~.
  eapply alloc_read_SExp_neq in A.
  - rewrite~ A.
  - introv D. substs. erewrite alloc_read_SExp_fresh in E; autos*. inverts* E.
Qed.


(** ** Lemmae to be used by tactics **)

Lemma read_bound : forall (S : state) p p_,
  read_SExp S p = Some p_ ->
  bound S p.
Proof. introv E. exists* p_. Qed.

Lemma bound_read : forall (S : state) p,
  bound S p ->
  exists p_, read_SExp S p = Some p_.
Proof. introv (p_&E&_). exists* p_. Qed.

Lemma only_one_nil_SExprRec : forall S p1 p2 e1 e2 e1_ e2_,
  safe_state S ->
  move_along_path p1 S = Some e1 ->
  move_along_path p2 S = Some e2 ->
  read_SExp S e1 = Some e1_ ->
  read_SExp S e2 = Some e2_ ->
  type e1_ = NilSxp ->
  type e2_ = NilSxp ->
  e1 = e2.
Proof.
  introv Safe M1 M2 R1 R2 T1 T2.
  applys~ only_one_nil Safe; eexists; splits*; apply~ BagInSingle_list.
Qed.

Lemma conserve_old_binding_read : forall S S' p p_,
  conserve_old_binding S S' ->
  read_SExp S p = Some p_ ->
  read_SExp S' p = Some p_.
Proof.
  introv C E. lets (p1_&E1&(p2_&E2&E3)): C p.
  - apply* read_bound.
  - rewrite E in E1. inverts E1. substs~.
Qed.

Lemma conserve_old_binding_bound : forall S S' p,
  conserve_old_binding S S' ->
  bound S p ->
  bound S' p.
Proof.
  introv C (p_&E&_). lets (p1_&E1&(p2_&E2&E3)): C p.
  - apply* read_bound.
  - rewrite E in E1. inverts E1. substs. exists~ p2_.
Qed.

Lemma conserve_old_binding_may_have_types : forall S S' l p,
  conserve_old_binding S S' ->
  may_have_types S l p ->
  may_have_types S' l p.
Proof.
  introv C (p_&E&T). lets (p1_&E1&(p2_&E2&E3)): C p.
  - apply* read_bound.
  - rewrite E in E1. inverts E1. substs. exists~ p2_.
Qed.

Lemma conserve_old_binding_list_type : forall S S' l_t l_car l_tag p,
  conserve_old_binding S S' ->
  list_type S l_t l_car l_tag p ->
  list_type S' l_t l_car l_tag p.
Proof.
  introv C L. induction L as [? ? ? ? I|? ? ? ? p_ h car cdr tag E M H A L T IH]
    using list_type_ind'.
  - apply list_type_nil. applys~ conserve_old_binding_may_have_types C.
  - apply list_type_cons. exists p_. splits~.
    + applys~ conserve_old_binding_read C.
    + exists h car cdr tag. splits~; applys~ conserve_old_binding_may_have_types C.
Qed.


(** * General tactics **)

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

Ltac syntactically_the_same x y :=
  match x with
  | y => idtac
  end.

Ltac simplify_context :=
  match goal with
  | T : may_have_types ?S nil ?p |- _ =>
    false; applys~ may_have_types_nil T
  | T1 : may_have_types ?S ?l1 ?p,
    T2 : may_have_types ?S ?l2 ?p |- _ =>
    let T3 := fresh T1 T2 in
    lets T3: may_have_types_merge (rm T1) (rm T2);
    rename T3 into T1
  | T1 : list_type ?S ?l1_t ?l1_car ?l1_tag ?p,
    T2 : list_type ?S ?l2_t ?l2_car ?l2_tag ?p |- _ =>
    let T3 := fresh T1 T2 in
    lets T3: list_type_merge (rm T1) (rm T2);
    rename T3 into T1
  end; simpl_list_inter.


(** *** Automatic rewriting **)

(** As this file defines a lot of tactics defining new names, it is
  best to avoid explicitely having to use these new hypotheses by
  their names.  The following tactic tries to automatically rewrites
  what it can. **)

Ltac selfrewrite :=
  repeat match goal with
  | H : _ = _ |- _ => rewrite~ H
  end.


(** *** Case analysis on lists **)

Ltac explode_list T :=
  match type of T with
  | ?x \in nil =>
    false; applys~ BagInEmpty_list T
  | ?x \in [?y] =>
    let T' := fresh T in
    asserts T': (x = y); [applys~ BagInSingle_list T|];
    clear T; rename T' into T
  | ?x \in (?y :: ?l) =>
    apply BagIn_cons in T;
    let T' := fresh T in
    lets [T'|T']: (rm T); rename T' into T;
    [|explode_list T]
  | may_have_types ?S nil ?x =>
    false; applys~ may_have_types_nil T
  | may_have_types ?S (?t :: ?l) ?x =>
    apply may_have_types_cons in T;
    let T' := fresh T in
    lets [T'|T']: (rm T); rename T' into T;
    [|explode_list T]
  | Mem ?x nil =>
    rewrite Mem_nil_eq in T; false~ T
  | Mem ?x (?y :: ?l) =>
    rewrite Mem_cons_eq in T;
    let T' := fresh T in
    lets [T'|T']: (rm T); rename T' into T;
    [|explode_list T]
  | mem ?x nil =>
    rewrite mem_nil in T; false~ T
  | mem ?x (?y :: ?l) =>
    rewrite mem_cons in T;
    rew_refl in T;
    let T' := fresh T in
    lets [T'|T']: (rm T); rename T' into T;
    [|explode_list T]
  end.


(** *** Clearing trivial hypotheses **)

Ltac clear_trivial :=
  repeat match goal with
  | T : True |- _ => clear T
  | E : ?x = ?x |- _ => clear E
  | H1 : ?P, H2 : ?P |- _ => clear H2
  | I : ?x \in [?y] |- _ => explode_list I
  end.


(** ** Unfolding tactics **)

(** *** Dealing with [read_SExp] **)

Ltac rewrite_read_SExp :=
  match goal with
  | |- context [ read_SExp (state_memory ?S) ?e ] =>
    let bound_such_that_prop T :=
      let e_ := fresh e "_" in
      let Ee_ := fresh "E" e_ in
      let Pe_ := fresh T e_ in
      lets (e_&Ee_&Pe_): (rm T);
      try rewrite Ee_ in * in
    match goal with
    | E : read_SExp S e = _ |- _ => rewrite E
    | T : may_have_types S ?l e |- _ => bound_such_that_prop T
    | L : list_type_step S ?l e |- _ => bound_such_that_prop L
    | B : bound_such_that S ?P e |- _ => bound_such_that_prop B
    | B : bound S e |- _ => bound_such_that_prop B
    end
  end; clear_trivial.

(** Tries to prove a new equality of the form [write_SExp S p p_]. **)
Ltac define_write_SExp S p p_ :=
  match goal with
  | E : write_SExp S p p_ = Some ?S' |- _ => try rewrite E in *
  | _ =>
    let S' := fresh S in
    let ES' := fresh "E" S' in
    destruct (write_SExp S p p_) as [|S'] eqn:ES';
    [ solve [
          false;
          match goal with
          | A : alloc_SExp _ _ = (S, p) |- _ =>
            applys~ alloc_write_SExp_not_None A ES'
          | E : read_SExp S p = Some _ |- _ =>
            let R := fresh "R" in
            forwards~ R: write_read_SExp_None (rm ES');
            rewrite R in E; inverts~ E
          end
        | autos~; simpl; autos* ]
    | try rewrite ES'; try assumption ]
  end.


(** ** Tactics taking advantage of the invariants **)

(** *** Getting the invariant **)

Ltac get_safe_state S :=
  match goal with
  | H : safe_state S |- _ => H
  | H : result_prop ?P_success _ _ (result_success S _) |- _ =>
    let I := fresh "Impl" in
    asserts I: (forall S r, P_success S r -> safe_state S);
    [solve [autos*]|];
    let R := fresh "Safe" in
    lets~ R: (rm I) H;
    R
  | H : result_prop _ ?P_error _ (result_error S _) |- _ =>
    let I := fresh "Impl" in
    asserts I: (forall S, P_error S -> safe_state S);
    [solve [autos*]|];
    let R := fresh "Safe" in
    lets~ R: (rm I) H;
    R
  | H : result_prop _ _ ?P_longjump (result_longjump S _ _) |- _ =>
    let I := fresh "Impl" in
    asserts I: (forall S n c, P_longjump S n c -> safe_state S);
    [solve [autos*]|];
    let R := fresh "Safe" in
    lets~ R: (rm I) H;
    R
  end.

Goal forall S, result_prop (fun S i => safe_state S /\ i > 0) (fun _ => False) (fun _ _ _ => False) (result_success S 1) -> False.
  introv I.
  asserts I': (forall S r, (fun S i => safe_state S /\ i > 0) S r -> safe_state S).
  autos*.
  lets R: (rm I') I.
  let r := get_safe_state S in set (X := r).

Ltac get_safe_pointer S p :=
  match goal with
  | H : safe_pointer S p |- _ => H
  | _ =>
    let H := get_safe_state S in
    let R := fresh "Safe" in
    lets~ R: safe_entry_points H;
    R
  end.

Ltac get_safe_SExpRec S e_ :=
  match goal with
  | H : safe_SExpRec S e_ |- _ => H
  | P : read_SExp S ?e = Some e_ |- _ =>
    let H := get_safe_pointer S e in
    let R := fresh "Safe" in
    lets~ R: safe_SExpRec_along_path H P;
    R
  end.


(** *** Simplifying the context **)

Ltac simplify_context_using_invariant :=
  repeat match goal with
  | T1 : may_have_types ?S ([NilSxp]) ?p1,
    T2 : may_have_types ?S ([NilSxp]) ?p2 |- _ =>
    let Safe := get_safe_state S in
    let E := fresh "E" in
    lets E: only_one_nil Safe T1 (rm T2);
    try rewrite E in *; clear_trivial
  | R1 : read_SExp ?S ?p1 = Some ?p1_,
    R2 : read_SExp ?S ?p2 = Some ?p2_,
    T1 : type (get_SxpInfo ?p1_) = NilSxp,
    T2 : type (get_SxpInfo ?p2_) = NilSxp |- _ =>
    let Safe := get_safe_state S in
    let E := fresh "E" in
    lets~ E: only_one_nil_SExprRec Safe R1 R2 T1 T2;
    try rewrite E in *;
    let E_ := fresh "E_" in
    asserts E_: (p1_ = p2_); [rewrite R1 in R2; inverts~ R2|];
    try rewrite E_ in *;
    clear_trivial
  | _ => simplify_context
  end.


(** ** Proving that different locations are different **)

(** We carry an hypothesis of the form [No_duplicates [p1; …; pn]]
  aiming to differentiate as many pointers [SEXP] as possible. **)

(** Generates a proof of [Nth n p l] if possible. **)
Ltac find_Nth_No_duplicates p l :=
  match l with
  | p :: ?l' => constr:(Nth_here l' p)
  | ?x :: ?l' =>
    let N := find_Nth_No_duplicates p l' in
    constr:(Nth_next x N)
  end.

Ltac prove_locations_different :=
  match goal with
  | |- ?p1 <> ?p2 =>
    match goal with
    | D : No_duplicates ?l |- _ =>
      solve [
        let N1 := find_Nth_No_duplicates p1 l in
        let N2 := find_Nth_No_duplicates p2 l in
        let E := fresh "E" in
        forwards E: No_duplicates_Nth D N1 N2;
        false~ E ]
    | A : alloc_SExp ?S _ = (?S', p1),
      R : read_SExp ?S p2 = Some _ |- _ =>
      applys~ alloc_read_SExp_diff A R
    | A : alloc_SExp ?S _ = (?S', p2),
      R : read_SExp ?S p1 = Some _ |- _ =>
      let E := fresh "E" in
      introv E; symmetry in E;
      applys~ alloc_read_SExp_diff A R E
    end
  end.

Ltac prepare_No_duplicates_hypothesis :=
  match goal with
  | D : @No_duplicates SEXP _ |- _ => idtac
  | _ =>
    let D := fresh "D" in
    forwards D: (No_duplicates_nil SEXP)
  end.

Ltac prepare_proofs_that_locations_are_different :=
  prepare_No_duplicates_hypothesis;
  repeat match goal with
  | D : No_duplicates ?l,
    A : alloc_SExp ?S ?p_ = (?S', ?p) |- _ =>
    let D' := fresh D in
    forwards D': No_duplicates_cons p D;
    [ abstract (
        let M := fresh "M" in
        introv M;
        explode_list M;
        prove_locations_different)
    | clear D; rename D' into D ]
  end.


(** ** Transitions between states **)

Ltac transition_conserve S S' :=
  prepare_proofs_that_locations_are_different;
  let C :=
    match goal with
    | C : conserve_old_binding S S' |- _ => C
    | E : alloc_SExp S ?p_ = (S', ?p) |- _ =>
      let C := fresh "C" in
      lets~ C: alloc_SExp_conserve_old_binding E;
      C
    end in
  first [
      syntactically_the_same S S'
    | repeat match goal with
      | E : read_SExp S ?p = Some ?p_ |- _ =>
        let E' := fresh E in
        lets E': conserve_old_binding_read C (rm E);
        rename E' into E
      | A : alloc_SExp _ ?p_ = (S, ?p) |- _ =>
        let E := fresh "E" in
        lets E: alloc_read_SExp_eq (rm A)
      | E : bound S ?p |- _ =>
        let E' := fresh E in
        lets E': conserve_old_binding_bound C (rm E);
        rename E' into E
      | E : may_have_types S ?l ?p |- _ =>
        let E' := fresh E in
        lets E': conserve_old_binding_may_have_types C (rm E);
        rename E' into E
      | E : list_type S ?l_t ?l_car ?l_tag ?p |- _ =>
        let E' := fresh E in
        lets E': conserve_old_binding_list_type C (rm E);
        rename E' into E
      end ].

Ltac transition_write_SExp S S' :=
  prepare_proofs_that_locations_are_different;
  let W :=
    match goal with
    | W : write_SExp S ?p ?p_ = Some S' |- _ => W
    | E : Some S' = write_SExp S ?p ?p_ |- _ =>
      let W := fresh E in
      lets W: E; symmetry in W; try clear E;
      W
    end in
  let R := fresh "E" in
  lets~ R: read_write_SExp_eq W;
  repeat match goal with
  | E : read_SExp S ?p = Some ?p_ |- _ =>
    match type of R with
    | read_SExp S' p = _ => clear E
    | read_SExp S' _ = _ =>
      let E' := fresh E in
      lets E': read_write_SExp_neq R E;
      [ prove_locations_different | clear E ]
    end
  | A : alloc_SExp _ ?p_ = (S, ?p) |- _ => TODO
  | E : bound S ?p |- _ => idtac "TODO"
  | E : may_have_types S ?l ?p |- _ => idtac "TODO"
  | E : list_type S ?l_t ?l_car ?l_tag ?p |- _ => idtac "TODO"
  end.


(** * Lemmae **)

(** ** TYPEOF **)

Lemma TYPEOF_result : forall S x t,
  may_have_types S ([t]) x ->
  TYPEOF S x = result_success S t.
Proof. introv T. unfolds. rewrite_read_SExp. simplifyR. selfrewrite. Qed.


(** * Specific tactics **)

Ltac get_result_lemma t :=
  match get_head t with
  | TYPEOF => TYPEOF_result
  end.

Ltac solve_incl :=
  solve [
      apply~ BagUnionIncl_left
    | apply~ BagUnionIncl_right
    | apply~ BagInterIncl_left
    | apply~ BagInterIncl_right
    | apply* BagInIncl_make ].

Ltac solve_premises_lemmae :=
  autos~;
  match goal with
  | |- bound ?S ?p =>
    solve [
        apply~ may_have_types_bound
      | apply* bound_such_that_weaken
      | apply~ read_bound; solve_premises_lemmae ]
  | |- bound_such_that ?S ?p =>
    solve [
        apply* bound_such_that_weaken ]
  | |- may_have_types ?S ?l ?p =>
    solve [
        apply~ list_type_may_have_types; solve_premises_lemmae
      | apply~ may_have_types_weaken; solve_incl ]
  | |- list_type ?S ?l_t ?l_car ?l_tag ?p =>
    solve [
        apply~ list_type_nil ]
  | |- _ => solve_premises
  end.

Ltac apply_result_lemma t :=
  let L := get_result_lemma t in
  rewrite L; simplify_context_using_invariant; try solve_premises_lemmae.

Ltac computeR_step :=
  simplifyR;
  rewrite_read_SExp;
  match goal with
  | |- context [ read_SExp ?S ?x ] =>
    rewrite_read_SExp
  | |- context [ write_SExp ?S ?p ?p_ ] =>
    define_write_SExp S p p_;
    match goal with
    | E : write_SExp S p p_ = Some ?S' |- _ =>
      repeat rewrite E;
      transition_write_SExp S S'
    end
  | |- context [ alloc_SExp ?S ?p_ ] =>
    let p := fresh "p" in
    let S' := fresh S in
    let E := fresh "E" S' in
    destruct (alloc_SExp S p_) as [S' p] eqn: E;
    transition_conserve S S'
  | |- context [ TYPEOF ?S ?e ] =>
    apply_result_lemma (TYPEOF S e)
  end;
  clear_trivial.

Ltac computeR :=
  repeat computeR_step.

