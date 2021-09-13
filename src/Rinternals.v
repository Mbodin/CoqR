(** Rinternals.
  The types of this file exactly correspond to the types defined
  in the R source file src/include/internals.h **)

(* Copyright © 2018 Martin Bodin

  This program is free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301 USA *)

Set Implicit Arguments.

From Lib Require Export Array NBits.
From TLC Require Export LibString LibInt.
From Coq Require Import Double.


(** * General Types **)

Definition double := Double.double.

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
  | FunSxp (** Note that in some place in the R source code, this last type [FunSxp]
             is used as [CloSxp]. See Definition [SExpType_restrict] in RinternalsAux
             for more details. **).

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

Definition SEXP := SExpRec_pointer.

Definition NULL : SEXP := None.

Definition R_UnboundValue : SEXP := NULL.

(** primsxp_struct **)
Record PrimSxp_struct := make_PrimSxp_struct {
    prim_offset : nat
  }.

(** symsxp_struct **)
Record SymSxp_struct := make_SymSxp_struct_direct {
    sym_pname : SEXP ;
    sym_value : SEXP ;
    sym_internal : SEXP
  }.

(** listsxp_struct **)
Record ListSxp_struct := make_ListSxp_struct_direct {
    list_carval : SEXP ;
    list_cdrval : SEXP ;
    list_tagval : SEXP
  }.

(** envsxp_struct **)
Record EnvSxp_struct := make_EnvSxp_struct_direct {
    env_frame : SEXP ;
    env_enclos : SEXP
    (** env_hashtab : SEXP **)
  }.

(** closxp_struct **)
Record CloSxp_struct := make_CloSxp_struct_direct {
    clo_formals : SEXP ;
    clo_body : SEXP ;
    clo_env : SEXP
  }.

(** promsxp_struct **)
Record PromSxp_struct := make_PromSxp_struct_direct {
    prom_value : SEXP ;
    prom_expr : SEXP ;
    prom_env : SEXP
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
Record SExpRecHeader := make_SExpRecHeader_direct {
    sxpinfo :> SxpInfo ;
    attrib : SEXP
    (* gengc_next_node : SEXP ; *)
    (* gengc_prev_node : SEXP *)
  }.

(** SEXPREC **)
Record NonVector_SExpRec := make_NonVector_SExpRec {
    NonVector_SExpRec_header :> SExpRecHeader ;
    NonVector_SExpRec_data :> SExpRec_union (* node data *)
  }.

(** vecsxp_struct **)
Record VecSxp_struct (A : Type) := make_VecSxp_struct {
    VecSxp_length : nat ;
    VecSxp_truelength : nat ;
    VecSxp_data :> ArrayList.array A
  }.

(** VECTOR_SEXPREC, VECSEXP **)
Record Vector_SExpRec (A : Type) := make_Vector_SExpRec {
    Vector_SExpRec_header :> SExpRecHeader ;
    Vector_SExpRec_vecsxp :> VecSxp_struct A
  }.

Definition character := Ascii.ascii.

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
  (** R uses integers to represent three-valued booleans. **)
  | SExpRec_VectorInteger : Vector_SExpRec int -> SExpRec
  (* | SExpRec_VectorRaw : Vector_SExpRec Rbyte -> SExpRec *)
  | SExpRec_VectorComplex : Vector_SExpRec Rcomplex -> SExpRec
  | SExpRec_VectorReal : Vector_SExpRec double -> SExpRec
  | SExpRec_VectorPointer : Vector_SExpRec SEXP -> SExpRec
  .
Coercion SExpRec_NonVector : NonVector_SExpRec >-> SExpRec.

