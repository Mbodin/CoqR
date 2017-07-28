(** Rinternals.
 * The types of this file exactly correspond to the types defined
 * in the R source file src/include/internals.h **)

Set Implicit Arguments.

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
  | FunSxp (** Note that in some place in the R source code, this last type is used as CloSxp, as only five digits are usually used to store the type, and they assigned this type the number 99: 99 mod 2^5 = 3. **)
  .

(** The field [named] of [sxpinfo_struct] can take these three values. **)
Inductive named_field :=
  | named_temporary (** 0 in R **)
  | named_unique (** 1 in R; bound to at most one variable **)
  | named_plural (** 2 in R; the object may be bound to more than one variable **)
  .

Fixpoint nbits (n : nat) : Type :=
  match n with
  | 0 => unit
  | S n => bool * nbits n
  end.

(** sxpinfo_struct **)
Record SxpInfo := make_SxpInfo {
    type : SExpType ;
    obj : bool ;
    named : named_field ;
    gp : nbits 16
    (** mark : bool ; **)
    (** debug : bool ; **)
    (** trace : bool ; **)
    (** spare : bool ; **)
    (** gcgen : bool ; **)
    (** gccls : nbits 3 **)
  }.

(** A type to represent C-style pointers. **)
Definition defined_pointer := nat.

(** SEXP, *SEXPREC **)
(** We chose to represent pointers as an option type. [None] means
 * R_UnboundValue (NULL is very rarely used in the R source code),
 * [Some p] yielding that the pointer [p] points to something. **)
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
    (** gengc_next_node : SExpRec_pointer ; **)
    (** gengc_prev_node : SExpRec_pointer **)
  }.

(** SEXPREC **)
Record NonVector_SExpRec := make_NonVector_SExpRec {
    NonVector_SExpRec_header :> SExpRecHeader ;
    NonVector_SExpRec_data :> SExpRec_union (* node data *)
  }.

(** vecsxp_struct **)
Record VecSxp_struct (A : Type) := make_VecSxp_struct {
    VecSxp_length : nat ;
    (** VecSxp_truelength : nat ; **)
    (** As stated in the R-ints documentation, such a structure is
     * followed by an array. We represent this as a list in Coq. **)
    VecSxp_data : list A
  }.

(** VECTOR_SEXPREC **)
Record Vector_SExpRec (A : Type) := make_Vector_SExpRec {
    Vector_SExpRec_header :> SExpRecHeader ;
    Vector_SExpRec_vecsxp :> VecSxp_struct A
  }.

(** Whilst in C, a pointer can point to any of the two
 * structures SEXPREC and VECTOR_SEXPREC above, this is
 * not the case in Coq. We thus provide this inductive. **)
Inductive SExpRec :=
  | SExpRec_NonVector : NonVector_SExpRec -> SExpRec
  | SExpRec_VectorChar : Vector_SExpRec char -> SExpRec
  | SExpRec_VectorLogical : Vector_SExpRec int (** This type be surprising, but do not forget that R have three-valued booleans, and use integers to represent them. **) -> SExpRec (* FIXME: As for the field [named], we may want to declare a special type for this. *)
  | SExpRec_VectorInteger : Vector_SExpRec int -> SExpRec
  (** | SExpRec_VectorRaw : Vector_SExpRec Rbyte -> SExpRec **)
  | SExpRec_VectorComplex : Vector_SExpRec RComplex -> SExpRec
  | SExpRec_VectorReal : Vector_SExpRec double -> SExpRec
  | SExpRec_VectorPointers : Vector_SExpRec SExpRec_pointer -> SExpRec
  .
Coercion SExpRec_NonVector : NonVector_SExpRec >-> SExpRec.

