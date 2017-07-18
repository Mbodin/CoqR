(** Rinternals.
* The types of this file exactly correspond to the types defined in the file Rinternals.h,
* which can be found in (for instance) https://github.com/wch/r-source/blob/trunk/src/include/Rinternals.h **)

(** * Types **)

(** SEXPTYPE **)
Inductive SExpType :=
  | NilSxp
  | SymSxp
  | ListSxp
  | CloSxp
  | EnvSxp
  | PromSxp
  | LangSxp
  | SpecialSxp
  | BuiltinSxp
  | CharSxp
  | LglSxp
  | IntSxp
  | RealSxp
  | CplxSxp
  | StrSxp
  | DotSxp
  | AnySxp
  | VecSxp
  | ExprSxp
  | BcodeSxp
  | ExtptrSxp
  | WeakrefSxp
  | RawSxp
  | S4Sxp
  | NewSxp
  | FreeSxp
  | FunSxp
  .

(** The field “named” of “sxpinfo_struct” can take three values.
* (see the file R-ints.pdf, Section 1.1.2 for more details.) **)
Inductive named_field :=
  | named_temporary (** 0 in R **)
  | named_unique (** 1 in R; bound to at most one variable **)
  | named_plural (** 2 in R; the object may be bound to more than one variable **)
  .

(** sxpinfo_struct **)
Record SxpInfo := make_SxpInfo {
    type : SExpType ;
    obj : bool ;
    named : named_field;
    (* gp : (* 16 bits of general purpose, we do not model them. *) ; *)
    mark : bool ;
    debug : bool ;
    trace : bool ;
    spare : bool ;
    gcgen : bool ;
    (* ugccls : (*3 bits for the garbage collector, we do not model them. *) *)
  }.

(** A type to represent C-style pointers. **)
Definition defined_pointer := nat.

(** SEXP, *SEXPREC **)
(** We chose to represent points as an option type. [None] means NULL,
  and [Some p] yields that the pointer [p] points to something. **)
Definition SExpRec_pointer := option defined_pointer.

Definition R_UnboundValue : SExpRec_pointer := None.

(** One symbol for each primitive, that is, built-in functions in call-by-value. **)
Inductive primitive :=
  .

(** One symbol for each internal, that is, internals directly manipulating the promises. **)
Inductive internal :=
  .

Inductive primitive_construction :=
  | primitive_construction_primitive : primitive -> primitive_construction
  | primitive_construction_internal : internal -> primitive_construction
  .
Coercion primitive_construction_primitive : primitive >-> primitive_construction.
Coercion primitive_construction_internal : internal >-> primitive_construction.

(** primsxp_struct **)
Record PrimSxp_struct := make_PrimSxp_struct {
    prim_primitive : primitive_construction
  }.

(** symsxp_struct **)
Record SymSxp_struct := make_SymSxp_struct {
    sym_pname : SExpRec_pointer ;
    sym_value : SExpRec_pointer ;
    sym_internal : SExpRec_pointer
  }.

(** listsxp_struct **)
Record ListSxp_struct := make_ListSxp_struct {
    list_carval : SExpRec_pointer ;
    list_cdrval : SExpRec_pointer ;
    list_tagval : SExpRec_pointer
  }.

(** envsxp_struct **)
Record EnvSxp_struct := make_EnvSxp_struct {
    env_frame : SExpRec_pointer ;
    env_enclos : SExpRec_pointer ;
    env_hashtab : SExpRec_pointer
  }.

(** closxp_struct **)
Record CloSxp_struct := make_CloSxp_struct {
    clo_formals : SExpRec_pointer ;
    clo_body : SExpRec_pointer ;
    clo_env : SExpRec_pointer
  }.

(** promsxp_struct **)
Record PromSxp_struct := make_PromSxp_struct {
    prom_value : SExpRec_pointer ; (** The pointer is set to R_UnboundValue when unused, but . **)
    prom_expr : SExpRec_pointer ;
    prom_env : SExpRec_pointer
  }.

Inductive SExpRec_union :=
  | primSxp : PrimSxp_struct -> SExpRec_union
  | symSxp : SymSxp_struct -> SExpRec_union
  | listSxp : ListSxp_struct -> SExpRec_union
  | envSxp : EnvSxp_struct -> SExpRec_union
  | cloSxp : CloSxp_struct -> SExpRec_union
  | promSxp : PromSxp_struct -> SExpRec_union
  .

(** SEXPREC_HEADER **)
Record SExpRecHeader := make_SExpRecHeader {
    sxpinfo :> SxpInfo ;
    attrib : SExpRec_pointer ;
    gengc_next_node : SExpRec_pointer ;
    gengc_prev_node : SExpRec_pointer
  }.

(** SEXPREC **)
Record SExpRec := make_SExpRec {
    SExpRec_header :> SExpRecHeader ;
    SExpRec_data :> SExpRec_union (* node data *)
  }.

(* Seems to be unused in R source code.
(** vecsxp_struct **)
Record VecSxp_struct := {
    VecSxp_length : nat ;
    VecSxp_truelength : nat
  }.

(** VECTOR_SEXPREC **)
Record Vector_SExpRec := {
    Vector_SExpRec_header :> SExpRecHeader ;
    Vector_SExpRec_vecsxp :> VecSxp_struct
  }.
*)


(** * Accessors **)

Definition get_primSxp e :=
  match e with
  | primSxp p => Some p
  | _ => None
  end.

Definition get_listSxp e :=
  match e with
  | listSxp l => Some l
  | _ => None
  end.

Definition get_envSxp e :=
  match e with
  | envSxp e => Some e
  | _ => None
  end.

Definition get_cloSxp e :=
  match e with
  | cloSxp c => Some c
  | _ => None
  end.

Definition get_promSxp e :=
  match e with
  | promSxp p => Some p
  | _ => None
  end.

Definition set_named_sxpinfo i n :=
  make_SxpInfo (type i) (obj i) n (mark i) (debug i) (trace i) (spare i) (gcgen i).

Definition set_named_to e n :=
  make_SExpRec
    (let h := SExpRec_header e in
     make_SExpRecHeader
       (set_named_sxpinfo (sxpinfo h) n)
       (attrib h)
       (gengc_prev_node h)
       (gengc_next_node h))
    (SExpRec_data e).

Definition set_named e :=
  set_named_to e named_plural.

