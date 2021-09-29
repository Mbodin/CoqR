(** RinternalsAux.
  Auxiliary definitions for the data structures defined in Rinternals,
  focussed on smart constructors and object-specific monadic binders. **)

(* Copyright © 2020 Martin Bodin

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
From Coq Require Import Ascii.
From CoqR Require Export RinternalsAux Monads.


(** * Smart Constructors **)

(** A smart constructor for [SxpInfo] **)

Definition build_SxpInfo_direct type scalar : SxpInfo :=
  make_SxpInfo (SExpType_restrict type)
    scalar false false nbits_init named_temporary.

Definition build_SxpInfo type (scalar : _bool) :=
  let%fetch scalar in
  contextual_ret (build_SxpInfo_direct type scalar).

Lemma build_SxpInfo_bool : forall type (scalar : bool),
  build_SxpInfo type scalar
  = contextual_ret (build_SxpInfo_direct type scalar).
Proof. reflexivity. Qed.

Definition make_SExpRecHeader info (attrib : _SEXP) :=
  let%fetch attrib in
  contextual_ret (make_SExpRecHeader_direct info attrib).

Lemma make_SExpRecHeader_SEXP : forall info (attrib : SEXP),
  make_SExpRecHeader info attrib
  = contextual_ret (make_SExpRecHeader_direct info attrib).
Proof. reflexivity. Qed.

(** The pointers [gengc_prev_node] and [gengc_next_node] are only used
  by the garbage collector of R. We do not need them here as memory
  allocation is not targetted by this formalisation. We thus offer the
  following smart constructor for the type [SExpRecHeader]. **)
Definition build_SExpRecHeader_direct type scalar attrib : SExpRecHeader :=
  make_SExpRecHeader_direct (build_SxpInfo_direct type scalar) attrib (*None*) (*None*).

Definition build_SExpRecHeader type scalar (attrib : _SEXP) :=
  let%contextual info := build_SxpInfo type scalar in
  make_SExpRecHeader info attrib.

Lemma build_SExpRecHeader_bool_SEXP : forall type (scalar : bool) (attrib : SEXP),
  build_SExpRecHeader type scalar attrib
  = contextual_ret (build_SExpRecHeader_direct type scalar attrib).
Proof. reflexivity. Qed.


(** Smart constructors for each R data type. **)

(** [SymSxp] **)

Definition make_SymSxp_struct (pname value internal : _SEXP) :=
  let%fetch pname in
  let%fetch value in
  let%fetch internal in
  contextual_ret (make_SymSxp_struct_direct pname value internal).

Definition make_SExpRec_sym_direct attrib pname value internal :=
  SExpRec_NonVector
    (make_NonVector_SExpRec (build_SExpRecHeader_direct SymSxp false attrib)
      (make_SymSxp_struct_direct pname value internal)).

Definition make_SExpRec_sym (attrib pname value internal : _SEXP) :=
  let%contextual header := build_SExpRecHeader SymSxp false attrib in
  let%contextual sym := make_SymSxp_struct pname value internal in
  contextual_ret (SExpRec_NonVector (make_NonVector_SExpRec header sym)).

Lemma make_SExpRec_sym_SEXP : forall attrib pname value internal : SEXP,
  make_SExpRec_sym attrib pname value internal
  = contextual_ret (make_SExpRec_sym_direct attrib pname value internal).
Proof. reflexivity. Qed.

(** [ListSxp] **)

Definition make_ListSxp_struct (car cdr tag : _SEXP) :=
  let%fetch car in
  let%fetch cdr in
  let%fetch tag in
  contextual_ret (make_ListSxp_struct_direct car cdr tag).

Definition make_SExpRec_list_direct attrib car cdr tag :=
  SExpRec_NonVector
    (make_NonVector_SExpRec (build_SExpRecHeader_direct ListSxp false attrib)
      (make_ListSxp_struct_direct car cdr tag)).

Definition make_SExpRec_list attrib car cdr tag :=
  let%contextual header := build_SExpRecHeader ListSxp false attrib in
  let%contextual l := make_ListSxp_struct car cdr tag in
  contextual_ret (SExpRec_NonVector (make_NonVector_SExpRec header l)).

Lemma make_SExpRec_list_SEXP : forall attrib car cdr tag : SEXP,
  make_SExpRec_list attrib car cdr tag
  = contextual_ret (make_SExpRec_list_direct attrib car cdr tag).
Proof. reflexivity. Qed.

(** [CloSxp] **)

Definition make_CloSxp_struct (formals body env : _SEXP) :=
  let%fetch formals in
  let%fetch body in
  let%fetch env in
  contextual_ret (make_CloSxp_struct_direct formals body env).

Definition make_SExpRec_clo_direct attrib formals body env :=
  SExpRec_NonVector
    (make_NonVector_SExpRec (build_SExpRecHeader_direct CloSxp false attrib)
      (make_CloSxp_struct_direct formals body env)).

Definition make_SExpRec_clo attrib formals body env :=
  let%contextual header := build_SExpRecHeader CloSxp false attrib in
  let%contextual clo := make_CloSxp_struct formals body env in
  contextual_ret (SExpRec_NonVector (make_NonVector_SExpRec header clo)).

Lemma make_SExpRec_clo_SEXP : forall attrib formals body env : SEXP,
  make_SExpRec_clo attrib formals body env
  = contextual_ret (make_SExpRec_clo_direct attrib formals body env).
Proof. reflexivity. Qed.

(** [EnvSxp] **)

Definition make_EnvSxp_struct (frame enclos (* hashtab *) : _SEXP) :=
  let%fetch frame in
  let%fetch enclos in
  contextual_ret (make_EnvSxp_struct_direct frame enclos).

Definition make_SExpRec_env_direct attrib frame enclos (* hashtab *) :=
  SExpRec_NonVector
    (make_NonVector_SExpRec (build_SExpRecHeader_direct EnvSxp false attrib)
      (make_EnvSxp_struct_direct frame enclos)).

Definition make_SExpRec_env attrib frame enclos (* hashtab *) :=
  let%contextual header := build_SExpRecHeader EnvSxp false attrib in
  let%contextual env := make_EnvSxp_struct frame enclos in
  contextual_ret (SExpRec_NonVector (make_NonVector_SExpRec header env)).

Lemma make_SExpRec_env_SEXP : forall attrib frame enclos : SEXP,
  make_SExpRec_env attrib frame enclos
  = contextual_ret (make_SExpRec_env_direct attrib frame enclos).
Proof. reflexivity. Qed.

(** [PromSxp] **)

Definition make_PromSxp_struct (value expr env : _SEXP) :=
  let%fetch value in
  let%fetch expr in
  let%fetch env in
  contextual_ret (make_PromSxp_struct_direct value expr env).

Definition make_SExpRec_prom_direct attrib value expr env :=
  SExpRec_NonVector
    (make_NonVector_SExpRec (build_SExpRecHeader_direct PromSxp false attrib)
      (make_PromSxp_struct_direct value expr env)).

Definition make_SExpRec_prom attrib value expr env :=
  let%contextual header := build_SExpRecHeader PromSxp false attrib in
  let%contextual prom := make_PromSxp_struct value expr env in
  contextual_ret (SExpRec_NonVector (make_NonVector_SExpRec header prom)).

Lemma make_SExpRec_prom_SEXP : forall attrib value expr env : SEXP,
  make_SExpRec_prom attrib value expr env
  = contextual_ret (make_SExpRec_prom_direct attrib value expr env).
Proof. reflexivity. Qed.

(** [LangSxp] **)

Definition make_SExpRec_lang attrib function argumentList :=
  let%contextual header := build_SExpRecHeader LangSxp false attrib in
  let%contextual lang := make_ListSxp_struct function argumentList R_NilValue in
  contextual_ret (SExpRec_NonVector (make_NonVector_SExpRec header lang)).

(** [PrimSxp] **)

Definition make_SExpRec_prim_direct attrib prim type :=
  (** [type] is either [BuiltinSxp] or [SpecialSxp].
    See function [mkPRIMSXP] in Rfeatures for more details. **)
  SExpRec_NonVector
    (make_NonVector_SExpRec (build_SExpRecHeader_direct type false attrib)
      (make_PrimSxp_struct prim)).

Definition make_SExpRec_prim attrib prim type :=
  let%contextual header := build_SExpRecHeader type false attrib in
  contextual_ret (SExpRec_NonVector (make_NonVector_SExpRec header (make_PrimSxp_struct prim))).

(** Vectors **)

Definition vector_header_direct T type attrib (array : ArrayList.array T) :=
  let len := ArrayList.length array in
  build_SExpRecHeader_direct type (decide (ArrayList.length array = 1%nat)) attrib.

Definition vector_header T type attrib (array : ArrayList.array T) :=
  let len := ArrayList.length array in
  build_SExpRecHeader type (decide (ArrayList.length array = 1%nat)) attrib.

Definition make_SExpRec_vector_direct T
    (SExpRec_Vector : Vector_SExpRec T -> SExpRec) type attrib array :=
  let len := ArrayList.length array in
  SExpRec_Vector
    (make_Vector_SExpRec (vector_header_direct type attrib array)
      (make_VecSxp_struct len len array)).

Definition make_SExpRec_vector T
    (SExpRec_Vector : Vector_SExpRec T -> SExpRec) type attrib array :=
  let len := ArrayList.length array in
  let%contextual header := vector_header type attrib array in
  contextual_ret (SExpRec_Vector
    (make_Vector_SExpRec header
      (make_VecSxp_struct len len array))).

Lemma make_SExpRec_vector_SEXP : forall T (SExpRec_Vector : Vector_SExpRec T -> SExpRec)
    type (attrib : SEXP) array,
  make_SExpRec_vector SExpRec_Vector type attrib array
  = contextual_ret (make_SExpRec_vector_direct SExpRec_Vector type attrib array).
Proof. reflexivity. Qed.

Definition make_SExpRec_char_direct :=
  make_SExpRec_vector_direct SExpRec_VectorChar CharSxp.

Definition make_SExpRec_char :=
  make_SExpRec_vector SExpRec_VectorChar CharSxp.

Definition make_SExpRec_lgl_direct :=
  make_SExpRec_vector_direct SExpRec_VectorLogical LglSxp.

Definition make_SExpRec_lgl :=
  make_SExpRec_vector SExpRec_VectorLogical LglSxp.

Definition make_SExpRec_int_direct :=
  make_SExpRec_vector_direct SExpRec_VectorInteger IntSxp.

Definition make_SExpRec_int :=
  make_SExpRec_vector SExpRec_VectorInteger IntSxp.

Definition make_SExpRec_real_direct :=
  make_SExpRec_vector_direct SExpRec_VectorReal RealSxp.

Definition make_SExpRec_real :=
  make_SExpRec_vector SExpRec_VectorReal RealSxp.

Definition make_SExpRec_cplx_direct :=
  make_SExpRec_vector_direct SExpRec_VectorComplex CplxSxp.

Definition make_SExpRec_cplx :=
  make_SExpRec_vector SExpRec_VectorComplex CplxSxp.

Definition make_SExpRec_str_direct :=
  make_SExpRec_vector_direct SExpRec_VectorPointer StrSxp.

Definition make_SExpRec_str :=
  make_SExpRec_vector SExpRec_VectorPointer StrSxp.

Definition make_SExpRec_vec_direct :=
  make_SExpRec_vector_direct SExpRec_VectorPointer VecSxp.

Definition make_SExpRec_vec :=
  make_SExpRec_vector SExpRec_VectorPointer VecSxp.

Definition make_SExpRec_expr_direct :=
  make_SExpRec_vector_direct SExpRec_VectorPointer ExprSxp.

Definition make_SExpRec_expr :=
  make_SExpRec_vector SExpRec_VectorPointer ExprSxp.


(** * Monadic Binders **)

(** ** Basic Language Elements **)

(** Each of the function of this section are of the form [if_is_*],
  where [*] represents a basic language element ([prim], [sym],
  [list], [env], [clo] and [prom]).  See the definition [SExpRec_union]
  of Rinternals for more information.

  This section also contains notations of the form [let%* a_, a_* := e_]
  to get the object [e_] to be read as a [*].  The [a_] identifier then
  represent to [NonVector] component of [e_]:  it is rarely used, but can
  be useful.  Of course, such statement will fail if given an object [e_]
  of the wrong kind. **)

Definition if_is_prim A (e_ : SExpRec) (cont : NonVector_SExpRec -> PrimSxp_struct -> result A) : result A :=
  let%defined e_ := get_NonVector e_ with "if_is_prim, vector test" in
  let%defined e_prim := get_primSxp e_ with "if_is_prim, prim test" in
  cont e_ e_prim.

Notation "'let%prim' a_ ',' a_prim ':=' e_ 'in' cont" :=
  (if_is_prim e_ (fun a_ a_prim => cont))
  (at level 50, left associativity) : monad_scope.


Definition if_is_sym A (e_ : SExpRec) (cont : NonVector_SExpRec -> SymSxp_struct -> result A) : result A :=
  let%defined e_ := get_NonVector e_ with "if_is_sym, vector test" in
  let%defined e_sym := get_symSxp e_ with "if_is_sym, sym test" in
  cont e_ e_sym.

Notation "'let%sym' a_ ',' a_sym ':=' e_ 'in' cont" :=
  (if_is_sym e_ (fun a_ a_sym => cont))
  (at level 50, left associativity) : monad_scope.


Definition if_is_list A (e_ : SExpRec) (cont : NonVector_SExpRec -> ListSxp_struct -> result A) : result A :=
  let%defined e_ := get_NonVector e_ with "if_is_list, vector test" in
  let%defined e_list := get_listSxp e_ with "if_is_list, list test" in
  cont e_ e_list.

Notation "'let%list' a_ ',' a_list ':=' e_ 'in' cont" :=
  (if_is_list e_ (fun a_ a_list => cont))
  (at level 50, left associativity) : monad_scope.


Definition if_is_env A (e_ : SExpRec) (cont : NonVector_SExpRec -> EnvSxp_struct -> result A) : result A :=
  let%defined e_ := get_NonVector e_ with "if_is_env, vector test" in
  let%defined e_env := get_envSxp e_ with "if_is_env, env test" in
  cont e_ e_env.

Notation "'let%env' a_ ',' a_env ':=' e_ 'in' cont" :=
  (if_is_env e_ (fun a_ a_env => cont))
  (at level 50, left associativity) : monad_scope.


Definition if_is_clo A (e_ : SExpRec) (cont : NonVector_SExpRec -> CloSxp_struct -> result A) : result A :=
  let%defined e_ := get_NonVector e_ with "if_is_clo, vector test" in
  let%defined e_clo := get_cloSxp e_ with "if_is_clo, clo test" in
  cont e_ e_clo.

Notation "'let%clo' a_ ',' a_clo ':=' e_ 'in' cont" :=
  (if_is_clo e_ (fun a_ a_clo => cont))
  (at level 50, left associativity) : monad_scope.


Definition if_is_prom A (e_ : SExpRec) (cont : NonVector_SExpRec -> PromSxp_struct -> result A) : result A :=
  let%defined e_ := get_NonVector e_ with "if_is_prom, vector test" in
  let%defined e_prom := get_promSxp e_ with "if_is_prom, prom test" in
  cont e_ e_prom.

Notation "'let%prom' a_ ',' a_prom ':=' e_ 'in' cont" :=
  (if_is_prom e_ (fun a_ a_prom => cont))
  (at level 50, left associativity) : monad_scope.


(** The functions [read_as_*], and their equivalent notation
  [read%* e_, e_* := e] combines [read%defined] and [let%*]. **)

Definition read_as_prim A (e : _SEXP) cont : result A :=
  let%fetch e in
  let%success%defined e_ := read_SExp e with "read_as_prim" in
  let%prim e_, e_prim := e_ in
  cont e_ e_prim.

Notation "'read%prim' e_ ',' e_prim ':=' e 'in' cont" :=
  (read_as_prim e (fun e_ e_prim => cont))
  (at level 50, left associativity) : monad_scope.


Definition read_as_sym A (e : _SEXP) cont : result A :=
  let%fetch e in
  let%success%defined e_ := read_SExp e with "read_as_sym" in
  let%sym e_, e_sym := e_ in
  cont e_ e_sym.

Notation "'read%sym' e_ ',' e_sym ':=' e 'in' cont" :=
  (read_as_sym e (fun e_ e_sym => cont))
  (at level 50, left associativity) : monad_scope.


Definition read_as_list A (e : _SEXP) cont : result A :=
  let%fetch e in
  let%success%defined e_ := read_SExp e with "read_as_list" in
  let%list e_, e_list := e_ in
  cont e_ e_list.

Notation "'read%list' e_ ',' e_list ':=' e 'in' cont" :=
  (read_as_list e (fun e_ e_list => cont))
  (at level 50, left associativity) : monad_scope.

(** As lists are a very frequent case of basic language element,
  we provide the two additional notations with resectively four
  and three binders (not to be mixed with the usual version with
  only two binders):  [read%list e_, e_car, e_cdr, e_tag := e]
  reads [e] as a [NonVector] (binded to [e_]), then as a list,
  and binds the car, cdr, and tag projections of the list into
  the corresponding binders.  The version with only three binders
  [read%list e_car, e_cdr, e_tag := e] only binds these last
  three. **)

Definition read_as_list_all A (e : _SEXP) cont : result A :=
  read%list e_, e_list := e in
  cont e_ (list_carval e_list) (list_cdrval e_list) (list_tagval e_list).

Notation "'read%list' e_ ',' e_car ',' e_cdr ',' e_tag ':=' e 'in' cont" :=
  (read_as_list_all e (fun e_ e_car e_cdr e_tag => cont))
    (at level 50, left associativity) : monad_scope.

Definition read_as_list_components A (e : _SEXP) cont : result A :=
  read%list _, e_car, e_cdr, e_tag := e in
  cont e_car e_cdr e_tag.

Notation "'read%list' e_car ',' e_cdr ',' e_tag ':=' e 'in' cont" :=
  (read_as_list_components e (fun e_car e_cdr e_tag => cont))
  (at level 50, left associativity) : monad_scope.


Definition read_as_env A (e : _SEXP) cont : result A :=
  let%fetch e in
  let%success%defined e_ := read_SExp e with "read_as_env" in
  let%env e_, e_env := e_ in
  cont e_ e_env.

Notation "'read%env' e_ ',' e_env ':=' e 'in' cont" :=
  (read_as_env e (fun e_ e_env => cont))
  (at level 50, left associativity) : monad_scope.


Definition read_as_clo A (e : _SEXP) cont : result A :=
  let%fetch e in
  let%success%defined e_ := read_SExp e with "read_as_clo" in
  let%clo e_, e_clo := e_ in
  cont e_ e_clo.

Notation "'read%clo' e_ ',' e_clo ':=' e 'in' cont" :=
  (read_as_clo e (fun e_ e_clo => cont))
  (at level 50, left associativity) : monad_scope.


Definition read_as_prom A (e : _SEXP) cont : result A :=
  let%fetch e in
  let%success%defined e_ := read_SExp e with "read_as_prom" in
  let%prom e_, e_prom := e_ in
  cont e_ e_prom.

Notation "'read%prom' e_ ',' e_prom ':=' e 'in' cont" :=
  (read_as_prom e (fun e_ e_prom => cont))
  (at level 50, left associativity) : monad_scope.


(** ** Vectors **)

(** Vectors are typically read by fetching one of its cell.  If [v_] is a vector
  (for instance taken from a [get_Vector*] function), then
  [read%cell c := v_ at n] reads the [n]th cell of the vector [v_], binding it
  to [c]. **)

Definition read_cell_Vector_SExpRec A B (v_ : Vector_SExpRec A) n cont : result B :=
  let%defined c := ArrayList.read_option v_ n with "read_cell_Vector_SExpRec" in
  cont c.

Notation "'read%cell' c ':=' v_ 'at' n 'in' cont" :=
  (read_cell_Vector_SExpRec v_ n (fun c => cont))
  (at level 50, left associativity) : monad_scope.

(** The following function is a variant of [read%cell], but with a default value. **)

Definition read_cell_default_Vector_SExpRec A B (v_ : Vector_SExpRec A) n a cont : result B :=
  let c := LibOption.unsome_default a (ArrayList.read_option v_ n) in
  cont c.

Notation "'read%cell' c ':=' v_ 'at' n 'with' default 'in' cont" :=
  (read_cell_default_Vector_SExpRec v_ n default (fun c => cont))
  (at level 50, left associativity) : monad_scope.


Definition update_Vector_SExpRec_cell A (v_ : Vector_SExpRec A) n c :=
  ifb n < ArrayList.length v_ then
    Some (update_Vector_SExpRec v_ (ArrayList.write v_ n c))
  else None.

(** The following functions check that the vector [e_] is a vector,
  and is of the right type ([Char], [Logical], [Integer], [Real],
  [Complex], or [Pointer], see the definition [SExpRec] of
  Rinternals for more information).  The notation is
  [let%Vector* e_vector := e_], where [*] is to be replaced by the
  expected type.

  Variants include [read%Vector* e_ := e] to read the pointer [e],
  then check that it is a vector [e_] of the expected type,
  [let%* c := e_ at n] to get its [n]th cell, [read%* c := e at n]
  to read its [n]th cell from a pointer [e], [write%Vector* e := v]
  to replace the vector pointer by [e] by the vector [v], and
  [write%* e at n := c] to update the [n]th cell of the vector
  pointed by [e] by the content [c].  In all cases, cell types are
  transparently given to Coq:  type errors over cells [c] are
  statically checked by Coq (whereas type errors over the type of
  the vector pointed by a pointer [e] is not, and thus protected
  by a [let%defined] monadic binder).  The most frequent patterns
  are [read%* c := e at n] and [write%* e at n := c]. **)

Definition let_VectorChar A e_ cont : result A :=
  let%defined e_vector := get_VectorChar e_ with "let_VectorChar" in
  cont e_vector.

Notation "'let%VectorChar' e_vector ':=' e_ 'in' cont" :=
  (let_VectorChar e_ (fun e_vector => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_as_VectorChar A (e : _SEXP) cont : result A :=
  let%fetch e in
  let%success%defined e_ := read_SExp e with "read_as_VectorChar" in
  let%VectorChar e_vector := e_ in
  cont e_vector.

Notation "'read%VectorChar' e_ ':=' e 'in' cont" :=
  (read_as_VectorChar e (fun e_ => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_nth_cell_VectorChar A e_ n cont : result A :=
  let%VectorChar e_ := e_ in
  read%cell c := e_ at n in
  cont c.

Notation "'let%Char' c ':=' e_ 'at' n 'in' cont" :=
  (read_nth_cell_VectorChar e_ n (fun c => cont))
  (at level 50, left associativity) : monad_scope.

(** The character case is a little special as C strings ends with a ['\0']
  character, but we chose not to follow this convention here.
  To avoid making the code too cumbersome, we thus add here the exception
  that when reading just after the array, we get the empty character ["000"%char]. **)

Definition read_nth_cell_Char A e n cont : result A :=
  read%VectorChar e_ := e in
  ifb n = VecSxp_length e_ then cont "000"%char
  else
    read%cell c := e_ at n in
    cont c.

Notation "'read%Char' c ':=' e 'at' n 'in' cont" :=
  (read_nth_cell_Char e n (fun c => cont))
  (at level 50, left associativity) : monad_scope.

Definition write_VectorChar A e v cont : result A :=
  read%VectorChar e_ := e in
  let e_ := update_Vector_SExpRec e_ v in
  write%defined e := SExpRec_VectorChar e_ in
  cont.

Notation "'write%VectorChar' e ':=' v 'in' cont" :=
  (write_VectorChar e v cont)
  (at level 50, left associativity) : monad_scope.

Definition write_nth_cell_VectorChar A e n c cont : result A :=
  read%VectorChar e_ := e in
  let%defined e_ := update_Vector_SExpRec_cell e_ n c with "write_nth_cell_VectorChar" in
  write%defined e := SExpRec_VectorChar e_ in
  cont.

Notation "'write%Char' e 'at' n ':=' c 'in' cont" :=
  (write_nth_cell_VectorChar e n c cont)
  (at level 50, left associativity) : monad_scope.


Definition let_VectorLogical A e_ cont : result A :=
  let%defined e_vector := get_VectorLogical e_ with "let_VectorLogical" in
  cont e_vector.

Notation "'let%VectorLogical' e_vector ':=' e_ 'in' cont" :=
  (let_VectorLogical e_ (fun e_vector => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_as_VectorLogical A (e : _SEXP) cont : result A :=
  let%fetch e in
  let%success%defined e_ := read_SExp e with "read_as_VectorLogical" in
  let%VectorLogical e_vector := e_ in
  cont e_vector.

Notation "'read%VectorLogical' e_ ':=' e 'in' cont" :=
  (read_as_VectorLogical e (fun e_ => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_nth_cell_VectorLogical A e_ n cont : result A :=
  let%VectorLogical e_ := e_ in
  read%cell c := e_ at n in
  cont c.

Notation "'let%Logical' c ':=' e_ 'at' n 'in' cont" :=
  (read_nth_cell_VectorLogical e_ n (fun c => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_nth_cell_Logical A e n cont : result A :=
  read%VectorLogical e_ := e in
  read%cell c := e_ at n in
  cont c.

Notation "'read%Logical' c ':=' e 'at' n 'in' cont" :=
  (read_nth_cell_Logical e n (fun c => cont))
  (at level 50, left associativity) : monad_scope.

Definition write_VectorLogical A e v cont : result A :=
  read%VectorLogical e_ := e in
  let e_ := update_Vector_SExpRec e_ v in
  write%defined e := SExpRec_VectorLogical e_ in
  cont.

Notation "'write%VectorLogical' e ':=' v 'in' cont" :=
  (write_VectorLogical e v cont)
  (at level 50, left associativity) : monad_scope.

Definition write_nth_cell_VectorLogical A e n c cont : result A :=
  read%VectorLogical e_ := e in
  let%defined e_ := update_Vector_SExpRec_cell e_ n c with "write_nth_cell_VectorLogical" in
  write%defined e := SExpRec_VectorLogical e_ in
  cont.

Notation "'write%Logical' e 'at' n ':=' c 'in' cont" :=
  (write_nth_cell_VectorLogical e n c cont)
  (at level 50, left associativity) : monad_scope.


Definition let_VectorInteger A e_ cont : result A :=
  let%defined e_vector := get_VectorInteger e_ with "let_VectorInteger" in
  cont e_vector.

Notation "'let%VectorInteger' e_vector ':=' e_ 'in' cont" :=
  (let_VectorInteger e_ (fun e_vector => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_as_VectorInteger A (e : _SEXP) cont : result A :=
  let%fetch e in
  let%success%defined e_ := read_SExp e with "read_as_VectorInteger" in
  let%VectorInteger e_vector := e_ in
  cont e_vector.

Notation "'read%VectorInteger' e_ ':=' e 'in' cont" :=
  (read_as_VectorInteger e (fun e_ => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_nth_cell_VectorInteger A e_ n cont : result A :=
  let%VectorInteger e_ := e_ in
  read%cell c := e_ at n in
  cont c.

Notation "'let%Integer' c ':=' e_ 'at' n 'in' cont" :=
  (read_nth_cell_VectorInteger e_ n (fun c => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_nth_cell_Integer A e n cont : result A :=
  read%VectorInteger e_ := e in
  read%cell c := e_ at n in
  cont c.

Notation "'read%Integer' c ':=' e 'at' n 'in' cont" :=
  (read_nth_cell_Integer e n (fun c => cont))
  (at level 50, left associativity) : monad_scope.

Definition write_VectorInteger A e v cont : result A :=
  read%VectorInteger e_ := e in
  let e_ := update_Vector_SExpRec e_ v in
  write%defined e := SExpRec_VectorInteger e_ in
  cont.

Notation "'write%VectorInteger' e ':=' v 'in' cont" :=
  (write_VectorInteger e v cont)
  (at level 50, left associativity) : monad_scope.

Definition write_nth_cell_VectorInteger A e n c cont : result A :=
  read%VectorInteger e_ := e in
  let%defined e_ := update_Vector_SExpRec_cell e_ n c with "write_nth_cell_VectorInteger" in
  write%defined e := SExpRec_VectorInteger e_ in
  cont.

Notation "'write%Integer' e 'at' n ':=' c 'in' cont" :=
  (write_nth_cell_VectorInteger e n c cont)
  (at level 50, left associativity) : monad_scope.


Definition let_VectorReal A e_ cont : result A :=
  let%defined e_vector := get_VectorReal e_ with "let_VectorReal" in
  cont e_vector.

Notation "'let%VectorReal' e_vector ':=' e_ 'in' cont" :=
  (let_VectorReal e_ (fun e_vector => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_as_VectorReal A (e : _SEXP) cont : result A :=
  let%fetch e in
  let%success%defined e_ := read_SExp e with "read_as_VectorReal" in
  let%VectorReal e_vector := e_ in
  cont e_vector.

Notation "'read%VectorReal' e_ ':=' e 'in' cont" :=
  (read_as_VectorReal e (fun e_ => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_nth_cell_VectorReal A e_ n cont : result A :=
  let%VectorReal e_ := e_ in
  read%cell c := e_ at n in
  cont c.

Notation "'let%Real' c ':=' e_ 'at' n 'in' cont" :=
  (read_nth_cell_VectorReal e_ n (fun c => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_nth_cell_Real A e n cont : result A :=
  read%VectorReal e_ := e in
  read%cell c := e_ at n in
  cont c.

Notation "'read%Real' c ':=' e 'at' n 'in' cont" :=
  (read_nth_cell_Real e n (fun c => cont))
  (at level 50, left associativity) : monad_scope.

Definition write_VectorReal A e v cont : result A :=
  read%VectorReal e_ := e in
  let e_ := update_Vector_SExpRec e_ v in
  write%defined e := SExpRec_VectorReal e_ in
  cont.

Notation "'write%VectorReal' e ':=' v 'in' cont" :=
  (write_VectorReal e v cont)
  (at level 50, left associativity) : monad_scope.

Definition write_nth_cell_VectorReal A e n c cont : result A :=
  read%VectorReal e_ := e in
  let%defined e_ := update_Vector_SExpRec_cell e_ n c with "write_nth_cell_VectorReal" in
  write%defined e := SExpRec_VectorReal e_ in
  cont.

Notation "'write%Real' e 'at' n ':=' c 'in' cont" :=
  (write_nth_cell_VectorReal e n c cont)
  (at level 50, left associativity) : monad_scope.


Definition let_VectorComplex A e_ cont : result A :=
  let%defined e_vector := get_VectorComplex e_ with "let_VectorComplex" in
  cont e_vector.

Notation "'let%VectorComplex' e_vector ':=' e_ 'in' cont" :=
  (let_VectorComplex e_ (fun e_vector => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_as_VectorComplex A (e : _SEXP) cont : result A :=
  let%fetch e in
  let%success%defined e_ := read_SExp e with "read_as_VectorComplex" in
  let%VectorComplex e_vector := e_ in
  cont e_vector.

Notation "'read%VectorComplex' e_ ':=' e 'in' cont" :=
  (read_as_VectorComplex e (fun e_ => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_nth_cell_VectorComplex A e_ n cont : result A :=
  let%VectorComplex e_ := e_ in
  read%cell c := e_ at n in
  cont c.

Notation "'let%Complex' c ':=' e_ 'at' n 'in' cont" :=
  (read_nth_cell_VectorComplex e_ n (fun c => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_nth_cell_Complex A e n cont : result A :=
  read%VectorComplex e_ := e in
  read%cell c := e_ at n in
  cont c.

Notation "'read%Complex' c ':=' e 'at' n 'in' cont" :=
  (read_nth_cell_Complex e n (fun c => cont))
  (at level 50, left associativity) : monad_scope.

Definition write_VectorComplex A e v cont : result A :=
  read%VectorComplex e_ := e in
  let e_ := update_Vector_SExpRec e_ v in
  write%defined e := SExpRec_VectorComplex e_ in
  cont.

Notation "'write%VectorComplex' e ':=' v 'in' cont" :=
  (write_VectorComplex e v cont)
  (at level 50, left associativity) : monad_scope.

Definition write_nth_cell_VectorComplex A e n c cont : result A :=
  read%VectorComplex e_ := e in
  let%defined e_ := update_Vector_SExpRec_cell e_ n c with "write_nth_cell_VectorComplex" in
  write%defined e := SExpRec_VectorComplex e_ in
  cont.

Notation "'write%Complex' e 'at' n ':=' c 'in' cont" :=
  (write_nth_cell_VectorComplex e n c cont)
  (at level 50, left associativity) : monad_scope.


Definition let_VectorPointer A e_ cont : result A :=
  let%defined e_vector := get_VectorPointer e_ with "let_VectorPointer" in
  cont e_vector.

Notation "'let%VectorPointer' e_vector ':=' e_ 'in' cont" :=
  (let_VectorPointer e_ (fun e_vector => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_as_VectorPointer A (e : _SEXP) cont : result A :=
  let%fetch e in
  let%success%defined e_ := read_SExp e with "read_as_VectorPointer" in
  let%VectorPointer e_vector := e_ in
  cont e_vector.

Notation "'read%VectorPointer' e_ ':=' e 'in' cont" :=
  (read_as_VectorPointer e (fun e_ => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_nth_cell_VectorPointer A e_ n cont : result A :=
  let%VectorPointer e_ := e_ in
  read%cell c := e_ at n in
  cont c.

Notation "'let%Pointer' c ':=' e_ 'at' n 'in' cont" :=
  (read_nth_cell_VectorPointer e_ n (fun c => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_nth_cell_Pointer A e n cont : result A :=
  read%VectorPointer e_ := e in
  read%cell c := e_ at n in
  cont c.

Notation "'read%Pointer' c ':=' e 'at' n 'in' cont" :=
  (read_nth_cell_Pointer e n (fun c => cont))
  (at level 50, left associativity) : monad_scope.

Definition write_VectorPointer A e v cont : result A :=
  read%VectorPointer e_ := e in
  let e_ := update_Vector_SExpRec e_ v in
  write%defined e := SExpRec_VectorPointer e_ in
  cont.

Notation "'write%VectorPointer' e ':=' v 'in' cont" :=
  (write_VectorPointer e v cont)
  (at level 50, left associativity) : monad_scope.

Definition write_nth_cell_VectorPointer A e n (c : _SEXP) cont : result A :=
  read%VectorPointer e_ := e in
  let%fetch c in
  let%defined e_ := update_Vector_SExpRec_cell e_ n c with "write_nth_cell_VectorPointer" in
  write%defined e := SExpRec_VectorPointer e_ in
  cont.

Notation "'write%Pointer' e 'at' n ':=' c 'in' cont" :=
  (write_nth_cell_VectorPointer e n c cont)
  (at level 50, left associativity) : monad_scope.


(** ** Lists **)

(** Updating a list. **)
Definition map_list A f (p : _SEXP) (cont : result A) : result A :=
  add%stack "map_list" in
  read%list p_, p_list := p in
  let%contextual data := f p_list in
  let p_ := {|
      NonVector_SExpRec_header := p_ ;
      NonVector_SExpRec_data := data
    |} in
  write%defined p := p_ in
  cont.

Notation "'map%list' p 'with' map 'in' cont" :=
  (map_list map p cont)
  (at level 50, left associativity) : monad_scope.

Definition set_car_list (car : _SEXP) l_list :=
  let%fetch car in
  contextual_ret (set_car_list_direct car l_list).

(** Updating the first element (car) of a list. **)
Definition set_car A car (p : _SEXP) (cont : result A) : result A :=
  add%stack "set_car" in
  map%list p with set_car_list car in cont.

Notation "'set%car' p ':=' car 'in' cont" :=
  (set_car car p cont)
  (at level 50, left associativity) : monad_scope.

Definition set_cdr_list (cdr : _SEXP) l_list :=
  let%fetch cdr in
  contextual_ret (set_cdr_list_direct cdr l_list).

(** Updating the tail (cdr) of a list. **)
Definition set_cdr A cdr (p : _SEXP) (cont : result A) : result A :=
  add%stack "set_cdr" in
  map%list p with set_cdr_list cdr in cont.

Notation "'set%cdr' p ':=' cdr 'in' cont" :=
  (set_cdr cdr p cont)
  (at level 50, left associativity) : monad_scope.

Definition set_tag_list (tag : _SEXP) l_list :=
  let%fetch tag in
  contextual_ret (set_tag_list_direct tag l_list).

(** Updating the tag of a list. **)
Definition set_tag A tag (p : _SEXP) (cont : result A) : result A :=
  add%stack "set_tag" in
  map%list p with set_tag_list tag in cont.

Notation "'set%tag' p ':=' tag 'in' cont" :=
  (set_tag tag p cont)
  (at level 50, left associativity) : monad_scope.


(** ** [map]-monadic-binders **)

Definition map_pointer_contextual (A : Type) (map : SExpRec -> contextual SExpRec)
    (p : _SEXP) (cont : result A) : result A :=
  add%stack "map_pointer_contextual" in
  let%fetch p in
  read%defined p_ := p in
  let%contextual p_ := map p_ in
  write%defined p := p_ in
  cont.

Notation "'map%pointer%contextual' p 'with' map 'in' cont" :=
  (map_pointer_contextual map p cont)
  (at level 50, left associativity) : monad_scope.

(** Mapping on-place the content of a pointer is a frequent scheme.
  Here is a monad binder for it. **)
Definition map_pointer (A : Type) (map : SExpRec -> SExpRec) p (cont : result A) : result A :=
  add%stack "map_pointer" in
  map%pointer%contextual p with fun p_ => contextual_ret (map p_) in
  cont.

Notation "'map%pointer' p 'with' map 'in' cont" :=
  (map_pointer map p cont)
  (at level 50, left associativity) : monad_scope.


(** The following two functions enable to respectively map and set
  the [gp] field of objects from a pointer. **)
Notation "'map%gp' p 'with' f 'in' cont" :=
  (map%pointer p with map_gp f in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'set%gp' p 'with' v 'in' cont" :=
  (map%pointer p with set_gp v in cont)
  (at level 50, left associativity) : monad_scope.

Definition set_attrib (a : _SEXP) e_ :=
  let%fetch a in
  contextual_ret (set_attrib_direct a e_).

(** The following function enables to set the [attrib] field of
  objects from a pointer. **)
Notation "'set%attrib' p ':=' a 'in' cont" :=
  (map%pointer%contextual p with set_attrib a in cont)
  (at level 50, left associativity) : monad_scope.

Definition set_obj (b : _bool) e_ :=
  let%fetch b in
  contextual_ret (set_obj_direct b e_).

(** The following function enables to set the [obj] field of
  objects from a pointer. **)
Notation "'set%obj' p ':=' o 'in' cont" :=
  (map%pointer%contextual p with set_obj o in cont)
  (at level 50, left associativity) : monad_scope.

(** The following function enables to set the [named] field of
  objects from a pointer. **)
Notation "'set%named' p ':=' n 'in' cont" :=
  (map%pointer p with set_named n in cont)
  (at level 50, left associativity) : monad_scope.

(** The following function enables to set the [type] field of
  objects from a pointer. **)
Notation "'set%type' p ':=' t 'in' cont" :=
  (map%pointer p with set_type t in cont)
  (at level 50, left associativity) : monad_scope.
