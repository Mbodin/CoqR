(** RinternalsAux.
 * Auxiliary definitions for the data structures defined in Rinternals. **)

Set Implicit Arguments.
Require Export Rinternals Shared.


(** The C language performs a lot of pointer deferentiation. As a
 * convention, we write [p_] for the object referenced by the pointer [p]
 * (that is, [p_] stands for [*p] in C), and [p_f] for its field [f]—for
 * instance [p_sym] for its [symSxp_struct] part—, that is [p->f] in C. **)


(** * About the [nbits] Structure **)

Definition nth_bit {m : nat} (n : nat) : nbits m -> n < m -> bool.
  introv a I. gen m. induction n as [|n]; introv a I; destruct m; try math.
  - exact (fst a).
  - applys IHn (snd a). math.
Defined.
Arguments nth_bit {m} n.

(* A tactic to fill out the [n < m] part.
 * The call to nth_bit should be on the form [nth_bit n a ltac:nbits_ok]. *)
Ltac nbits_ok := repeat constructors.

Lemma rewrite_nth_bit : forall n m (a : nbits m) (I I' : n < m),
  nth_bit n a I = nth_bit n a I'.
Proof.
  induction n; introv; destruct m; try solve [ false; math ].
  - reflexivity.
  - simpl. erewrite IHn. reflexivity.
Qed.

Lemma rewrite_S_nth_bit : forall n m (a : nbits (S m)) (I : S n < S m) (I' : n < m),
  nth_bit (S n) a I = nth_bit n (snd a) I'.
Proof. introv. erewrite rewrite_nth_bit with (n := n). simpl. reflexivity. Qed.

Definition write_nbit {m : nat} (n : nat) : nbits m -> n < m -> bool -> nbits m.
  introv a I b. gen m. induction n as [|n]; introv a I; destruct m; try math.
  - exact (b, snd a).
  - refine (fst a, IHn _ (snd a) _). math.
Defined.
Arguments write_nbit {m} n.

Lemma rewrite_write_nbit : forall n m (a : nbits m) (I I' : n < m) b,
  write_nbit n a I b = write_nbit n a I' b.
Proof.
  induction n; introv; destruct m; try solve [ false; math ].
  - reflexivity.
  - simpl. erewrite IHn. reflexivity.
Qed.

Lemma rewrite_S_write_nbit : forall n m (a : nbits (S m)) (I : S n < S m) (I' : n < m) b,
  write_nbit (S n) a I b = (fst a, write_nbit n (snd a) I' b).
Proof. introv. erewrite rewrite_write_nbit with (n := n). simpl. reflexivity. Qed.

Lemma write_nth_bit : forall n m (I : n < m) (a : nbits m) b,
  nth_bit n (write_nbit n a I b) I = b.
Proof.
  induction n; introv; destruct m; try solve [ false; math ].
  - reflexivity.
  - asserts I': (n < m). math.
    rewrite rewrite_S_nth_bit with (I' := I'). rewrite rewrite_S_write_nbit with (I' := I').
    simpl. rewrite~ IHn.
Qed.

Fixpoint nbits_init (n : nat) : nbits n :=
  match n with
  | 0 => tt
  | S n => (false, nbits_init n)
  end.

Lemma nbits_init_read : forall n m (I : n < m),
  nth_bit n (nbits_init m) I = false.
Proof.
  induction n; introv; destruct m; try solve [ false; math ].
  - reflexivity.
  - asserts I': (n < m). math.
    rewrite rewrite_S_nth_bit with (I' := I'). rewrite~ IHn.
Qed.

Definition nbits_to_list {n} (a : nbits n) : list bool.
  induction n.
  - exact nil.
  - exact (fst a :: IHn (snd a)).
Defined.

Lemma nbits_to_list_length : forall n (a : nbits n),
  length (nbits_to_list a) = n.
Proof.
  induction n; introv.
  - reflexivity.
  - simpl. rew_list. rewrite~ IHn.
Qed.

Lemma nbits_to_list_nth : forall n (a : nbits n) d m I,
  nth_def d m (nbits_to_list a) = nth_bit m a I.
Proof.
  induction n; introv.
  - false. math.
  - destruct m as [|m].
    + reflexivity.
    + simpl. erewrite~ IHn.
Qed.

Fixpoint list_to_nbits (l : list bool) : nbits (length l) :=
  match l return nbits (length l) with
  | nil => tt
  | b :: l => (b, list_to_nbits l)
  end.

Lemma list_to_nbits_to_list : forall l,
  nbits_to_list (list_to_nbits l) = l.
Proof.
  introv. induction l.
  - reflexivity.
  - simpl. fequals~.
Qed.

Definition nbits_to_nat {n} (a : nbits n) : nat.
  induction n.
  - exact 0.
  - exact ((if fst a then 1 else 0) + 2 * IHn (snd a)).
Defined.
(** Important note: the first bit in this representation has the lower weight. **)

Lemma rewrite_nbits_to_nat : forall n (a : nbits (S n)),
  nbits_to_nat a = ((if fst a then 1 else 0) + 2 * nbits_to_nat (snd a)).
Proof. reflexivity. Qed.

Definition nat_to_nbits {n} m : m < 2 ^ n -> nbits n.
  introv I'. asserts I: (m < 2 ^ n)%nat. math.
  clear I'. gen m. induction n; introv I.
  - exact tt.
  - refine (decide (m mod 2 = 1), IHn (m / 2) _).
    apply~ Nat.div_lt_upper_bound.
Defined.
Arguments nat_to_nbits {n} m.

Lemma rewrite_nat_to_nbits : forall n m I I',
  nat_to_nbits m I = (nat_to_nbits m I' : nbits n).
Proof.
  induction n; introv.
  - reflexivity.
  - unfolds. fequals.
Qed.

Lemma rewrite_nat_to_nbits_cons : forall n m I I',
  nat_to_nbits m I = ((decide (m mod 2 = 1), nat_to_nbits (m / 2) I') : nbits (S n)).
Proof. introv. unfold nat_to_nbits. simpl. repeat fequals. Qed.

Lemma nat_to_nbits_to_nat : forall n m I,
  nbits_to_nat (nat_to_nbits m I : nbits n) = m.
Proof.
  introv. gen m. induction n; introv.
  - simpls. math.
  - asserts I1: (m / 2 < 2 ^ n)%nat. apply~ Nat.div_lt_upper_bound. simpl in I. math.
    asserts I2: (m / 2 < 2 ^ n). math.
    rewrite rewrite_nat_to_nbits_cons with (I' := I2). rewrite rewrite_nbits_to_nat.
    unfold snd, fst. rewrite IHn.
    rewrite Nat.div_mod with (y := 2); [|math]. rewrite Nat.add_comm. fequals.
    clear. forwards I: Nat.mod_upper_bound m 2. math.
    destruct (m mod 2); cases_if as M; fold_bool; rew_refl in M; try math.
Qed.


(** * Accessors and Smart Constructors **)

Definition get_NonVector e_ :=
  match e_ with
  | SExpRec_NonVector e_ => Some e_
  | _ => None
  end.

Definition get_VectorChar e_ :=
  match e_ with
  | SExpRec_VectorChar e_ => Some e_
  | _ => None
  end.

Definition get_VectorLogical e_ :=
  match e_ with
  | SExpRec_VectorLogical e_ => Some e_
  | _ => None
  end.

Definition get_VectorInteger e_ :=
  match e_ with
  | SExpRec_VectorInteger e_ => Some e_
  | _ => None
  end.

Definition get_VectorComplex e_ :=
  match e_ with
  | SExpRec_VectorComplex e_ => Some e_
  | _ => None
  end.

Definition get_VectorReal e_ :=
  match e_ with
  | SExpRec_VectorReal e_ => Some e_
  | _ => None
  end.

Definition get_VectorPointers e_ :=
  match e_ with
  | SExpRec_VectorPointers e_ => Some e_
  | _ => None
  end.


Definition get_SxpInfo e_ :=
  match e_ return SxpInfo with
  | SExpRec_NonVector e_ => e_
  | SExpRec_VectorChar e_ => e_
  | SExpRec_VectorLogical e_ => e_
  | SExpRec_VectorInteger e_ => e_
  | SExpRec_VectorComplex e_ => e_
  | SExpRec_VectorReal e_ => e_
  | SExpRec_VectorPointers e_ => e_
  end.
Coercion get_SxpInfo : SExpRec >-> SxpInfo.


Definition get_primSxp e_ :=
  match e_ with
  | primSxp e_prim => Some e_prim
  | _ => None
  end.

Definition get_symSxp e_ :=
  match e_ with
  | symSxp e_sym => Some e_sym
  | _ => None
  end.

Definition get_listSxp e_ :=
  match e_ with
  | listSxp e_list => Some e_list
  | _ => None
  end.

Definition get_envSxp e_ :=
  match e_ with
  | envSxp e_env => Some e_env
  | _ => None
  end.

Definition get_cloSxp e_ :=
  match e_ with
  | cloSxp e_clo => Some e_clo
  | _ => None
  end.

Definition get_promSxp e_ :=
  match e_ with
  | promSxp e_prom => Some e_prom
  | _ => None
  end.


Definition set_named_sxpinfo n i_info :=
  make_SxpInfo (type i_info) (obj i_info) n (gp i_info)
    (**mark i_info**) (**debug i_info**) (**trace i_info**) (**spare i_info**) (**gcgen i_info**).

Definition map_sxpinfo_NonVector_SExpRec f e_ :=
  make_NonVector_SExpRec
    (let h := NonVector_SExpRec_header e_ in
     make_SExpRecHeader
       (f (sxpinfo h))
       (attrib h)
       (**gengc_prev_node h**)
       (**gengc_next_node h**))
    (NonVector_SExpRec_data e_).

Definition map_sxpinfo_Vector_SExpRec T f (e_ : Vector_SExpRec T) :=
  make_Vector_SExpRec
    (let h := Vector_SExpRec_header e_ in
     make_SExpRecHeader
       (f (sxpinfo h))
       (attrib h)
       (**gengc_prev_node h**)
       (**gengc_next_node h**))
    (Vector_SExpRec_vecsxp e_).

Definition map_sxpinfo f e_ :=
  match e_ with
  | SExpRec_NonVector e_ =>
    SExpRec_NonVector (map_sxpinfo_NonVector_SExpRec f e_)
  | SExpRec_VectorChar e_ =>
    SExpRec_VectorChar (map_sxpinfo_Vector_SExpRec f e_)
  | SExpRec_VectorLogical e_ =>
    SExpRec_VectorLogical (map_sxpinfo_Vector_SExpRec f e_)
  | SExpRec_VectorInteger e_ =>
    SExpRec_VectorInteger (map_sxpinfo_Vector_SExpRec f e_)
  | SExpRec_VectorComplex e_ =>
    SExpRec_VectorComplex (map_sxpinfo_Vector_SExpRec f e_)
  | SExpRec_VectorReal e_ =>
    SExpRec_VectorReal (map_sxpinfo_Vector_SExpRec f e_)
  | SExpRec_VectorPointers e_ =>
    SExpRec_VectorPointers (map_sxpinfo_Vector_SExpRec f e_)
  end.

Definition set_named n :=
  map_sxpinfo (set_named_sxpinfo n).

Definition set_named_plural :=
  set_named named_plural.

Definition set_type_sxpinfo t i_info :=
  make_SxpInfo t (obj i_info) (named i_info) (gp i_info)
    (**mark i_info**) (**debug i_info**) (**trace i_info**) (**spare i_info**) (**gcgen i_info**).

Definition set_type t :=
  map_sxpinfo (set_type_sxpinfo t).

Definition set_car_list car l_list :=
  make_ListSxp_struct car (list_cdrval l_list) (list_tagval l_list).


(** A smart constructor for SxpInfo **)
Definition build_SxpInfo type : SxpInfo :=
  make_SxpInfo type false named_temporary (nbits_init _).

(** The pointers [gengc_prev_node] and [gengc_next_node] are only used
 * by the garbage collector of R. We do not need them here as memory
 * allocation is not targetted by this formalisation. We thus offer the
 * following smart constructor for the type [SExpRecHeader]. **)
Definition build_SExpRecHeader type attrib : SExpRecHeader :=
  make_SExpRecHeader (build_SxpInfo type) attrib (**None**) (**None**).

(* This object seems to be just NULL.
(** The Nil object TODO **)
Definition Nil_SExpRec :=
  make_NonVector_SExpRec
    (make_SExpRecHeader NilSxp None)
    ?.
*)

(** Smart constructors for each R data type. **)

Definition make_SExpRec_sym attrib pname value internal :=
  SExpRec_NonVector
    (make_NonVector_SExpRec (build_SExpRecHeader SymSxp attrib)
      (make_SymSxp_struct pname value internal)).

Definition make_SExpRec_list attrib car cdr tag :=
  SExpRec_NonVector
    (make_NonVector_SExpRec (build_SExpRecHeader ListSxp attrib)
      (make_ListSxp_struct car cdr tag)).

Definition make_SExpRec_clo attrib formals body env :=
  SExpRec_NonVector
    (make_NonVector_SExpRec (build_SExpRecHeader CloSxp attrib)
      (make_CloSxp_struct formals body env)).

Definition make_SExpRec_env attrib frame enclos (** hashtab **) :=
  SExpRec_NonVector
    (make_NonVector_SExpRec (build_SExpRecHeader EnvSxp attrib)
      (make_EnvSxp_struct frame enclos)).

Definition make_SExpRec_prom attrib value expr env :=
  SExpRec_NonVector
    (make_NonVector_SExpRec (build_SExpRecHeader CloSxp attrib)
      (make_CloSxp_struct value expr env)).

Definition make_SExpRec_lang attrib function argumentList :=
  SExpRec_NonVector
    (make_NonVector_SExpRec (build_SExpRecHeader LangSxp attrib)
      (make_ListSxp_struct function argumentList None)).

Definition make_SExpRec_prim attrib prim :=
  SExpRec_NonVector
    (make_NonVector_SExpRec (build_SExpRecHeader
        match prim with
        | primitive_construction_primitive _ => BuiltinSxp
        | primitive_construction_internal _ => SpecialSxp
        end attrib)
      (make_PrimSxp_struct prim)).

Definition make_SExpRec_char attrib array :=
  SExpRec_VectorChar
    (make_Vector_SExpRec
      (build_SExpRecHeader CharSxp attrib)
      (make_VecSxp_struct (length array) array)).

Definition make_SExpRec_lgl attrib array :=
  SExpRec_VectorLogical
    (make_Vector_SExpRec
      (build_SExpRecHeader LglSxp attrib)
      (make_VecSxp_struct (length array) array)).

Definition make_SExpRec_int attrib array :=
  SExpRec_VectorInteger
    (make_Vector_SExpRec
      (build_SExpRecHeader IntSxp attrib)
      (make_VecSxp_struct (length array) array)).

Definition make_SExpRec_real attrib array :=
  SExpRec_VectorReal
    (make_Vector_SExpRec
      (build_SExpRecHeader RealSxp attrib)
      (make_VecSxp_struct (length array) array)).

Definition make_SExpRec_cpl attrib array :=
  SExpRec_VectorComplex
    (make_Vector_SExpRec
      (build_SExpRecHeader CplxSxp attrib)
      (make_VecSxp_struct (length array) array)).

Definition make_SExpRec_str attrib array :=
  SExpRec_VectorPointers
    (make_Vector_SExpRec
      (build_SExpRecHeader StrSxp attrib)
      (make_VecSxp_struct (length array) array)).

Definition make_SExpRec_vec attrib array :=
  SExpRec_VectorPointers
    (make_Vector_SExpRec
      (build_SExpRecHeader VecSxp attrib)
      (make_VecSxp_struct (length array) array)).

Definition make_SExpRec_expr attrib array :=
  SExpRec_VectorPointers
    (make_Vector_SExpRec
      (build_SExpRecHeader ExprSxp attrib)
      (make_VecSxp_struct (length array) array)).


(** * Instances **)

Instance SExpType_Comparable : Comparable SExpType.
  prove_comparable_simple_inductive.
Defined.

Instance SExpRec_Inhab : Inhab SExpRec.
  apply prove_Inhab.
  refine (make_NonVector_SExpRec
            (make_SExpRecHeader (make_SxpInfo NilSxp false named_plural (nbits_init _)) None)
            (make_ListSxp_struct None None None)). (* May not be the best choice. *)
Defined.


