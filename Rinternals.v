(** Rinternals.v
* The types of this file exactly correspond to the types defined in the file Rinternals.h,
* which can be found in (for instance) https://github.com/wch/r-source/blob/trunk/src/include/Rinternals.h. **)

(** Following my experience from JSCert, this file has been defined to be as close as possible to the internals of R as possible. **)

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
  | named_unique (** No other SExp shares this object. **)
  | named_being_assigned (** Two versions of the object exists for the duration of the current computation. **)
  | named_must_be_duplicated (** The object must be duplicated before changed. **)
  .

(** sxpinfo_struct **)
Record SxpInfo := {
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

(** SEXP, *SEXPREC **)
Definition SExpRec_pointer := nat.

(** vecsxp_struct **)
Record VecSxp_struct := {
    VecSxp_length : nat ;
    VecSxp_truelength : nat
  }.

(** primsxp_struct **)
Record PrimSxp_struct := {
    prim_offset : nat
  }.

(** symsxp_struct **)
Record SymSxp_struct := {
    sym_pname : SExpRec_pointer ;
    sym_value : SExpRec_pointer ;
    sym_internal : SExpRec_pointer
  }.

(** listsxp_struct **)
Record ListSxp_struct := {
    list_carval : SExpRec_pointer ;
    list_cdrval : SExpRec_pointer ;
    list_tagval : SExpRec_pointer
  }.

(** envsxp_struct **)
Record EnvSxp_struct := {
    env_frame : SExpRec_pointer ;
    env_enclos : SExpRec_pointer ;
    env_hashtab : SExpRec_pointer
  }.

(** closxp_struct **)
Record CloSxp_struct := {
    clo_formals : SExpRec_pointer ;
    clo_body : SExpRec_pointer ;
    clo_env : SExpRec_pointer
  }.

(** promsxp_struct **)
Record PromSxp_struct := {
    prom_value : SExpRec_pointer ;
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
Record SExpRecHeader := {
    sxpinfo : SxpInfo ;
    attrib : SExpRec_pointer ;
    gengc_next_node : SExpRec_pointer ;
    gengc_prev_node : SExpRec_pointer
  }.

(** SEXPREC **)
Record SExpRec := {
    SExpRec_header :> SExpRecHeader ;
    SExpRec_data :> SExpRec_union (* node data *)
  }.

(** VECTOR_SEXPREC **)
Record Vector_SExpRec := {
    Vector_SExpRec_header :> SExpRecHeader ;
    Vector_SExpRec_vecsxp :> VecSxp_struct
  }.

