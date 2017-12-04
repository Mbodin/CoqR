(** Rinternals.
  The types of this file exactly correspond to the types defined
  in the R source file src/include/internals.h **)

Set Implicit Arguments.

Require Export Array NBits TLC.LibString TLC.LibInt.
Require Flocq.Appli.Fappli_IEEE Flocq.Appli.Fappli_IEEE_bits.


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
  | FunSxp (** Note that in some place in the R source code, this last type is used as [CloSxp]. See Definition [SExpType_restrict] in RinternalsAux for more details. **)
  .

(** The field [named] of [sxpinfo_struct] can take these three values. **)
Inductive named_field :=
  | named_temporary (** 0 in R **)
  | named_unique (** 1 in R; bound to at most one variable **)
  | named_plural (** 2 in R; the object may be bound to more than one variable **)
  .

(** sxpinfo_struct **)
Record SxpInfo := make_SxpInfo {
    type : SExpType ;
    scalar : bool ;
    obj : bool ;
    alt : bool ;
    gp : nbits 16 ;
    (* mark : bool ; *)
    (* debug : bool ; *)
    (* trace : bool ; *)
    (* spare : bool ; *)
    (* gcgen : bool ; *)
    (* gccls : nbits 3 *)
    named : named_field
  }.

(** A type to represent C-style pointers. **)
Definition defined_pointer := nat.

(** SEXP, *SEXPREC **)
(** We chose to represent pointers as an option type.
  [None] means NULL (it is very rarely used in the R source code).
  [Some p] yields that the pointer [p] points to something. **)
Definition SExpRec_pointer := option defined_pointer.

Definition NULL : SExpRec_pointer := None.

Definition R_UnboundValue : SExpRec_pointer := NULL.

(** primsxp_struct **)
Record PrimSxp_struct := make_PrimSxp_struct {
    prim_offset : nat
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
    env_enclos : SExpRec_pointer
    (** env_hashtab : SExpRec_pointer **)
  }.

(** closxp_struct **)
Record CloSxp_struct := make_CloSxp_struct {
    clo_formals : SExpRec_pointer ;
    clo_body : SExpRec_pointer ;
    clo_env : SExpRec_pointer
  }.

(** promsxp_struct **)
Record PromSxp_struct := make_PromSxp_struct {
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
Coercion primSxp : PrimSxp_struct >-> SExpRec_union.
Coercion symSxp : SymSxp_struct >-> SExpRec_union.
Coercion listSxp : ListSxp_struct >-> SExpRec_union.
Coercion envSxp : EnvSxp_struct >-> SExpRec_union.
Coercion cloSxp : CloSxp_struct >-> SExpRec_union.
Coercion promSxp : PromSxp_struct >-> SExpRec_union.

(** SEXPREC_HEADER **)
Record SExpRecHeader := make_SExpRecHeader {
    sxpinfo :> SxpInfo ;
    attrib : SExpRec_pointer
    (* gengc_next_node : SExpRec_pointer ; *)
    (* gengc_prev_node : SExpRec_pointer *)
  }.

(** SEXPREC **)
Record NonVector_SExpRec := make_NonVector_SExpRec {
    NonVector_SExpRec_header :> SExpRecHeader ;
    NonVector_SExpRec_data :> SExpRec_union (* node data *)
  }.

(** vecsxp_struct **)
Record VecSxp_struct (A : Type) := make_VecSxp_struct {
    VecSxp_length : nat ;
    (* VecSxp_truelength : nat ; *)
    VecSxp_data :> ArrayList.array A
  }.

(** VECTOR_SEXPREC, VECSEXP **)
Record Vector_SExpRec (A : Type) := make_Vector_SExpRec {
    Vector_SExpRec_header :> SExpRecHeader ;
    Vector_SExpRec_vecsxp :> VecSxp_struct A
  }.

Definition character := Ascii.ascii.

Definition double : Type := Fappli_IEEE.full_float.

Record Rcomplex := make_Rcomplex {
    Rcomplex_r : double ;
    Rcomplex_i : double
  }.

(** Whilst in C, a pointer can point to any of the two
 structures SEXPREC and VECTOR_SEXPREC above, this is
 not the case in Coq. We thus provide this inductive. **)
Inductive SExpRec :=
  | SExpRec_NonVector : NonVector_SExpRec -> SExpRec
  | SExpRec_VectorChar : Vector_SExpRec character -> SExpRec
  | SExpRec_VectorLogical : Vector_SExpRec int (** This type be surprising, but do not forget that R have three-valued booleans, and use integers to represent them. **) -> SExpRec (* FIXME: As for the field [named], we may want to declare a special type for this. *)
  | SExpRec_VectorInteger : Vector_SExpRec int -> SExpRec
  (* | SExpRec_VectorRaw : Vector_SExpRec Rbyte -> SExpRec *)
  | SExpRec_VectorComplex : Vector_SExpRec Rcomplex -> SExpRec
  | SExpRec_VectorReal : Vector_SExpRec double -> SExpRec
  | SExpRec_VectorPointer : Vector_SExpRec SExpRec_pointer -> SExpRec
  .
Coercion SExpRec_NonVector : NonVector_SExpRec >-> SExpRec.

