(** RLoops.
  This file provides looping monads to easily manipulate R objects. **)

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
Require Export Monads Globals.

(** * Global structure of the interpreter **)

(** A structure to deal with infinite execution (which is not allowed in Coq), inspired from JSCert.
	Each of its field correspond to a function that may loop.
	Note the presence of [R_FunTab], which contains functions that may loop. **)
Record runs_type : Type := runs_type_intro {
    runs_while_loop : forall A, A -> (A -> result bool) -> (A -> result A) -> result A ;
    runs_set_longjump : forall A, context_type -> nat -> (context_type -> result A) -> result A ;
    runs_eval : SEXP -> SEXP -> result SEXP ;
    runs_getAttrib : SEXP -> SEXP -> result SEXP ;
    runs_setAttrib : SEXP -> SEXP -> SEXP -> result SEXP ;
    runs_R_cycle_detected : SEXP -> SEXP -> result bool ;
    runs_duplicate1 : SEXP -> bool -> result SEXP ;
    runs_stripAttrib : SEXP -> SEXP -> result SEXP ;
    runs_evalseq : SEXP -> SEXP -> bool -> SEXP -> result SEXP ;
    runs_R_isMissing : SEXP -> SEXP -> result bool ;
    runs_AnswerType : SEXP -> bool -> bool -> BindData -> SEXP -> result BindData ;
    runs_ListAnswer : SEXP -> bool -> BindData -> SEXP -> result BindData ;
    runs_StringAnswer : SEXP -> BindData -> SEXP -> result BindData ;
    runs_LogicalAnswer : SEXP -> BindData -> SEXP -> result BindData ;
    runs_IntegerAnswer : SEXP -> BindData -> SEXP -> result BindData ;
    runs_RealAnswer : SEXP -> BindData -> SEXP -> result BindData ;
    runs_ComplexAnswer : SEXP -> BindData -> SEXP -> result BindData ;
    runs_RawAnswer : SEXP -> BindData -> SEXP -> result BindData ;
    runs_substitute : SEXP -> SEXP -> result SEXP ;
    runs_substituteList : SEXP -> SEXP -> result SEXP ;
    runs_R_FunTab : option funtab
  }.

(** The following function reads the [runs_R_FunTab] projection as a result. **)
Definition get_R_FunTab runs :=
  add%stack "get_R_FunTab" in
  match runs_R_FunTab runs with
  | None => result_bottom
  | Some t => result_success t
  end.

(** An accessor for the [runs_R_FunTab] projection. **)
Definition read_R_FunTab runs n :=
  add%stack "read_R_FunTab" in
  let%success t := get_R_FunTab runs in
  ifb n >= ArrayList.length t then
    result_impossible "Out of bounds."
  else
    let c := ArrayList.read t n in
    result_success c.


(** * Frequent Patterns **)

(** The functions presented here are not from R source code, but
  represent frequent programming pattern in its source code. **)

(** ** While **)

(** A basic C-like loop **)
Definition while_loop runs A (a : A) expr stat : result A :=
  if%success expr a then
    let%success a := stat a in
    runs_while_loop runs a expr stat
  else
    result_success a.

Notation "'do%let' a ':=' e 'while' expr 'do' stat 'using' runs" :=
  (while_loop runs e (fun a => expr) (fun a => stat))
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' 'while' expr 'do' stat 'using' runs" :=
  (do%let _ := tt
   while expr
   do stat
   using runs)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ')' ':=' a 'while' expr 'do' stat 'using' runs" :=
  (do%let x := a
   while let (a1, a2) := x in expr
   do let (a1, a2) := x in stat
   using runs)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ')' ':=' a 'while' expr 'do' stat 'using' runs" :=
  (do%let x := a
   while let '(a1, a2, a3) := x in expr
   do let '(a1, a2, a3) := x in stat
   using runs)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' a 'while' expr 'do' stat 'using' runs" :=
  (do%let x := a
   while let '(a1, a2, a3, a4) := x in expr
   do let '(a1, a2, a3, a4) := x in stat
   using runs)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' a 'while' expr 'do' stat 'using' runs" :=
  (do%let x := a
   while let '(a1, a2, a3, a4, a5) := x in expr
   do let '(a1, a2, a3, a4, a5) := x in stat
   using runs)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' a 'while' expr 'do' stat 'using' runs" :=
  (do%let x := a
   while let '(a1, a2, a3, a4, a5, a6) := x in expr
   do let '(a1, a2, a3, a4, a5, a6) := x in stat
   using runs)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' a ':=' e 'whileb' expr 'do' stat 'using' runs" :=
  (do%let a := e
   while result_success (decide expr)
   do stat
   using runs)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' 'whileb' expr 'do' stat 'using' runs" :=
  (do%let
   while result_success (decide expr)
   do stat
   using runs)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ')' ':=' a 'whileb' expr 'do' stat 'using' runs" :=
  (do%let (a1, a2) := a
   while result_success (decide expr)
   do stat
   using runs)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ')' ':=' a 'whileb' expr 'do' stat 'using' runs" :=
  (do%let (a1, a2, a3) := a
   while result_success (decide expr)
   do stat
   using runs)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' a 'whileb' expr 'do' stat 'using' runs" :=
  (do%let (a1, a2, a3, a4) := a
   while result_success (decide expr)
   do stat
   using runs)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' a 'whileb' expr 'do' stat 'using' runs" :=
  (do%let (a1, a2, a3, a4, a5) := a
   while result_success (decide expr)
   do stat
   using runs)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' a 'whileb' expr 'do' stat 'using' runs" :=
  (do%let (a1, a2, a3, a4, a5, a6) := a
   while result_success (decide expr)
   do stat
   using runs)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' 'while' expr 'do' stat 'using' runs 'in' cont" :=
  (run%success
     do%let while expr
     do stat
     using runs in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' a ':=' e 'while' expr 'do' stat 'using' runs 'in' cont" :=
  (let%success a :=
     do%let a := e
     while expr
     do stat
     using runs in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ')' ':=' a 'while' expr 'do' stat 'using' runs 'in' cont" :=
  (let%success (a1, a2) :=
     do%let (a1, a2) := a
     while expr
     do stat
     using runs in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ')' ':=' a 'while' expr 'do' stat 'using' runs 'in' cont" :=
  (let%success (a1, a2, a3) :=
     do%let (a1, a2, a3) := a
     while expr
     do stat
     using runs in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' a 'while' expr 'do' stat 'using' runs 'in' cont" :=
  (let%success (a1, a2, a3, a4) :=
     do%let (a1, a2, a3, a4) := a
     while expr
     do stat
     using runs in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' a 'while' expr 'do' stat 'using' runs 'in' cont" :=
  (let%success (a1, a2, a3, a4, a5) :=
     do%let (a1, a2, a3, a4, a5) := a
     while expr
     do stat
     using runs in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' a 'while' expr 'do' stat 'using' runs 'in' cont" :=
  (let%success (a1, a2, a3, a4, a5, a6) :=
     do%let (a1, a2, a3, a4, a5, a6) := a
     while expr
     do stat
     using runs in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' 'whileb' expr 'do' stat 'using' runs 'in' cont" :=
  (do%success
   while result_success (decide expr)
   do stat
   using runs in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' a ':=' e 'whileb' expr 'do' stat 'using' runs 'in' cont" :=
  (do%success a := e
   while result_success (decide expr)
   do stat
   using runs in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ')' ':=' a 'whileb' expr 'do' stat 'using' runs 'in' cont" :=
  (do%success (a1, a2) := a
   while result_success (decide expr)
   do stat
   using runs in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ')' ':=' a 'whileb' expr 'do' stat 'using' runs 'in' cont" :=
  (do%success (a1, a2, a3) := a
   while result_success (decide expr)
   do stat
   using runs in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' a 'whileb' expr 'do' stat 'using' runs 'in' cont" :=
  (do%success (a1, a2, a3, a4) := a
   while result_success (decide expr)
   do stat
   using runs in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' a 'whileb' expr 'do' stat 'using' runs 'in' cont" :=
  (do%success (a1, a2, a3, a4, a5) := a
   while result_success (decide expr)
   do stat
   using runs in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' a 'whileb' expr 'do' stat 'using' runs 'in' cont" :=
  (do%success (a1, a2, a3, a4, a5, a6) := a
   while result_success (decide expr)
   do stat
   using runs in
   cont)
  (at level 50, left associativity) : monad_scope.

(** ** Fold **)

(** Looping through a list is a frequent pattern in R source code.
  [fold_left_listSxp_gen] corresponds to the C code
  [for (i = l, v = a; i != R_NilValue; i = CDR (i)) v = iterate ( *i, v); v]. **)
Definition fold_left_listSxp_gen runs (globals : Globals) A (l : SEXP) (a : A)
    (iterate : A -> SEXP -> SExpRec -> ListSxp_struct -> result A) : result A :=
  do%success (l, a) := (l, a)
  whileb l <> global_mapping globals R_NilValue
  do
    read%list l_, l_list := l in
    let%success a := iterate a l l_ l_list in
    result_success (list_cdrval l_list, a)
  using runs in
  result_success a.

Notation "'fold%let' a ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' runs ',' globals" :=
  (fold_left_listSxp_gen runs globals le e (fun a l l_ l_list => iterate))
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' runs ',' globals" :=
  (fold%let _ := tt
   along le
   as l, l_, l_list
   do iterate
   using runs, globals)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' '(' a1 ',' a2 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' runs ',' globals" :=
  (fold%let x := e
   along le
   as l, l_, l_list
   do let (a1, a2) := x in iterate
   using runs, globals)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' '(' a1 ',' a2 ',' a3 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' runs ',' globals" :=
  (fold%let x := e
   along le
   as l, l_, l_list
   do let '(a1, a2, a3) := x in iterate
   using runs, globals)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' runs ',' globals" :=
  (fold%let x := e
   along le
   as l, l_, l_list
   do let '(a1, a2, a3, a4) := x in iterate
   using runs, globals)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' runs ',' globals" :=
  (fold%let x := e
   along le
   as l, l_, l_list
   do let '(a1, a2, a3, a4, a5) := x in iterate
   using runs, globals)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' runs ',' globals" :=
  (fold%let x := e
   along le
   as l, l_, l_list
   do let '(a1, a2, a3, a4, a5, a6) := x in iterate
   using runs, globals)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (run%success
     fold%let
     along le
     as l, l_, l_list
     do iterate
     using runs, globals in
   cont)
    (at level 50, left associativity) : monad_scope.

Notation "'fold%success' a ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (let%success a :=
     fold%let a := e
     along le
     as l, l_, l_list
     do iterate
     using runs, globals in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' '(' a1 ',' a2 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (let%success (a1, a2) :=
     fold%let (a1, a2) := e
     along le
     as l, l_, l_list
     do iterate
     using runs, globals in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' '(' a1 ',' a2 ',' a3 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (let%success (a1, a2, a3) :=
     fold%let (a1, a2, a3) := e
     along le
     as l, l_, l_list
     do iterate
     using runs, globals in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (let%success (a1, a2, a3, a4) :=
     fold%let (a1, a2, a3, a4) := e
     along le
     as l, l_, l_list
     do iterate
     using runs, globals in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (let%success (a1, a2, a3, a4, a5) :=
     fold%let (a1, a2, a3, a4, a5) := e
     along le
     as l, l_, l_list
     do iterate
     using runs, globals in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (let%success (a1, a2, a3, a4, a5, a6) :=
     fold%let (a1, a2, a3, a4, a5, a6) := e
     along le
     as l, l_, l_list
     do iterate
     using runs, globals in
   cont)
  (at level 50, left associativity) : monad_scope.


(** [fold_left_listSxp] corresponds to the C code
  [for (i = l, v = a; i != R_NilValue; i = CDR (i)) v = iterate (CAR (i), TAG (i), v); v]. **)
Definition fold_left_listSxp runs globals A (l : SEXP) (a : A)
    (iterate : A -> SEXP -> SEXP -> result A) : result A :=
  fold%let a := a
  along l
  as _, _, l_list
  do iterate a (list_carval l_list) (list_tagval l_list)
  using runs, globals.

Notation "'fold%let' a ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' runs ',' globals" :=
  (fold_left_listSxp runs globals le e (fun a l_car l_tag => iterate))
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' runs ',' globals" :=
  (fold%let _ := tt
   along le
   as l_car, l_tag
   do iterate
   using runs, globals)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' '(' a1 ',' a2 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' runs ',' globals" :=
  (fold%let x := e
   along le
   as l_car, l_tag
   do let (a1, a2) := x in iterate
   using runs, globals)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' '(' a1 ',' a2 ',' a3 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' runs ',' globals" :=
  (fold%let x := e
   along le
   as l_car, l_tag
   do let '(a1, a2, a3) := x in iterate
   using runs, globals)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' runs ',' globals" :=
  (fold%let x := e
   along le
   as l_car, l_tag
   do let '(a1, a2, a3, a4) := x in iterate
   using runs, globals)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' runs ',' globals" :=
  (fold%let x := e
   along le
   as l_car, l_tag
   do let '(a1, a2, a3, a4, a5) := x in iterate
   using runs, globals)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' runs ',' globals" :=
  (fold%let x := e
   along le
   as l_car, l_tag
   do let '(a1, a2, a3, a4, a5, a6) := x in iterate
   using runs, globals)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (run%success
     fold%let _ := tt
     along le
     as l_car, l_tag
     do iterate
     using runs, globals in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' a ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (let%success a :=
     fold%let a := e
     along le
     as l_car, l_tag
     do iterate
     using runs, globals in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' '(' a1 ',' a2 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (let%success (a1, a2) :=
     fold%let (a1, a2) := e
     along le
     as l_car, l_tag
     do iterate
     using runs, globals in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' '(' a1 ',' a2 ',' a3 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (let%success (a1, a2, a3) :=
     fold%let (a1, a2, a3) := e
     along le
     as l_car, l_tag
     do iterate
     using runs, globals in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (let%success (a1, a2, a3, a4) :=
     fold%let (a1, a2, a3, a4) := e
     along le
     as l_car, l_tag
     do iterate
     using runs, globals in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (let%success (a1, a2, a3, a4, a5) :=
     fold%let (a1, a2, a3, a4, a5) := e
     along le
     as l_car, l_tag
     do iterate
     using runs, globals in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (let%success (a1, a2, a3, a4, a5, a6) :=
     fold%let (a1, a2, a3, a4, a5, a6) := e
     along le
     as l_car, l_tag
     do iterate
     using runs, globals in
   cont)
  (at level 50, left associativity) : monad_scope.


(** ** Return **)

(** The following notations deal with loops that may return.
  In these cases, one can use the definitions [result_rsuccess],
  or [result_rskip] for a normal ending of the loop, and
  [result_rreturn] for a breaking return. Note that this only
  breaks the current loop and its continuation, not the whole
  function. **)

Inductive normal_return A B :=
  | normal_result : A -> normal_return A B
  | return_result : B -> normal_return A B
  .
Arguments normal_result {A B}.
Arguments return_result {A B}.

Definition result_rsuccess {A B} r : result (normal_return A B) :=
  result_success (normal_result r).

Definition result_rskip {B} : result (normal_return _ B) :=
  result_rsuccess tt.

Definition result_rreturn {A B} r : result (normal_return A B) :=
  result_success (return_result r).

Definition match_rresult {A B C} (r : result (normal_return A B)) cont
    : result (normal_return C B) :=
  let%success res := r in
  match res with
  | normal_result r => cont r
  | return_result r => result_rreturn r
  end.

Notation "'let%return' a ':=' e 'in' cont" :=
  (match_rresult e (fun a => cont))
  (at level 50, left associativity) : monad_scope.

Notation "'run%return' c 'in' cont" :=
  (let%return _ := c in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%return' '(' a1 ',' a2 ')' ':=' e 'in' cont" :=
  (let%return a := e in
   let (a1, a2) := a in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%return' '(' a1 ',' a2 ',' a3 ')' ':=' e 'in' cont" :=
  (let%return a := e in
   let '(a1, a2, a3) := a in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%return' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'in' cont" :=
  (let%return a := e in
   let '(a1, a2, a3, a4) := a in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%return' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'in' cont" :=
  (let%return a := e in
   let '(a1, a2, a3, a4, a5) := a in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%return' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' e 'in' cont" :=
  (let%return a := e in
   let '(a1, a2, a3, a4, a5, a6) := a in cont)
  (at level 50, left associativity) : monad_scope.



(** Exiting the return-monad. **)
Definition exit_rresult {A B} (r : result (normal_return A B)) cont :=
  let%success res := r in
  match res with
  | normal_result r => cont r
  | return_result r => result_success r
  end.

Notation "'let%exit' a ':=' e 'in' cont" :=
  (exit_rresult e (fun a => cont))
  (at level 50, left associativity) : monad_scope.

Notation "'run%exit' c 'in' cont" :=
  (let%exit _ := c in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%exit' '(' a1 ',' a2 ')' ':=' e 'in' cont" :=
  (let%exit a := e in
   let (a1, a2) := a in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%exit' '(' a1 ',' a2 ',' a3 ')' ':=' e 'in' cont" :=
  (let%exit a := e in
   let '(a1, a2, a3) := a in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%exit' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'in' cont" :=
  (let%exit a := e in
   let '(a1, a2, a3, a4) := a in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%exit' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'in' cont" :=
  (let%exit a := e in
   let '(a1, a2, a3, a4, a5) := a in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%exit' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' e 'in' cont" :=
  (let%exit a := e in
   let '(a1, a2, a3, a4, a5, a6) := a in cont)
  (at level 50, left associativity) : monad_scope.


Definition continue_and_condition {A B} (r : normal_return A B) cond :=
  match r with
  | normal_result r => cond r
  | return_result r => result_success false
  end.

Definition get_success {A B} (r : normal_return A B) cont
    : result (normal_return A B) :=
  match r with
  | normal_result r => cont r
  | return_result r => result_rreturn r
  end.


Notation "'do%return' a ':=' e 'while' expr 'do' stat 'using' runs 'in' cont" :=
  (let%exit a :=
     do%let a := normal_result e
     while continue_and_condition a (fun a => expr)
     do get_success a (fun a => stat)
     using runs
    in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%return' 'while' expr 'do' stat 'using' runs 'in' cont" :=
  (do%return _ := tt
   while expr
   do stat
   using runs
   in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%return' '(' a1 ',' a2 ')' ':=' e 'while' expr 'do' stat 'using' runs 'in' cont" :=
  (do%return a := e
   while let (a1, a2) := a in expr
   do let (a1, a2) := a in stat
   using runs
   in let (a1, a2) := a in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%return' '(' a1 ',' a2 ',' a3 ')' ':=' e 'while' expr 'do' stat 'using' runs 'in' cont" :=
  (do%return a := e
   while let (a1, a2, a3) := a in expr
   do let (a1, a2, a3) := a in stat
   using runs
   in let (a1, a2, a3) := a in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%return' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'while' expr 'do' stat 'using' runs 'in' cont" :=
  (do%return a := e
   while let (a1, a2, a3, a4) := a in expr
   do let (a1, a2, a3, a4) := a in stat
   using runs
   in let (a1, a2, a3, a4) := a in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%return' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'while' expr 'do' stat 'using' runs 'in' cont" :=
  (do%return a := e
   while let (a1, a2, a3, a4, a5) := a in expr
   do let (a1, a2, a3, a4, a5) := a in stat
   using runs
   in let (a1, a2, a3, a4, a5) := a in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%return' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' e 'while' expr 'do' stat 'using' runs 'in' cont" :=
  (do%return a := e
   while let (a1, a2, a3, a4, a5, a6) := a in expr
   do let (a1, a2, a3, a4, a5, a6) := a in stat
   using runs
   in let (a1, a2, a3, a4, a5, a6) := a in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%return' a ':=' e 'whileb' expr 'do' stat 'using' runs 'in' cont" :=
  (do%return a := e
   while result_success (decide expr)
   do stat
   using runs
   in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%return' 'whileb' expr 'do' stat 'using' runs 'in' cont" :=
  (do%return
   while result_success (decide expr)
   do stat
   using runs
   in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%return' '(' a1 ',' a2 ')' ':=' e 'whileb' expr 'do' stat 'using' runs 'in' cont" :=
  (do%return (a1, a2) := e
   while result_success (decide expr)
   do stat
   using runs
   in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%return' '(' a1 ',' a2 ',' a3 ')' ':=' e 'whileb' expr 'do' stat 'using' runs 'in' cont" :=
  (do%return (a1, a2, a3) := e
   while result_success (decide expr)
   do stat
   using runs
   in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%return' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'whileb' expr 'do' stat 'using' runs 'in' cont" :=
  (do%return (a1, a2, a3, a4) := e
   while result_success (decide expr)
   do stat
   using runs
   in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%return' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'whileb' expr 'do' stat 'using' runs 'in' cont" :=
  (do%return (a1, a2, a3, a4, a5) := e
   while result_success (decide expr)
   do stat
   using runs
   in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%return' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' e 'whileb' expr 'do' stat 'using' runs 'in' cont" :=
  (do%return (a1, a2, a3, a4, a5, a6) := e
   while result_success (decide expr)
   do stat
   using runs
   in cont)
  (at level 50, left associativity) : monad_scope.


Notation "'fold%return' a ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (let%exit a :=
     fold%let a := normal_result e
     along le
     as l, l_, l_list
     do get_success a (fun a => iterate)
     using runs, globals
    in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%return' 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (fold%return ret := tt
   along le
   as l, l_, l_list
   do iterate
   using runs, globals in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%return' '(' a1 ',' a2 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (fold%return a := e
   along le
   as l, l_, l_list
   do let (a1, a2) := a in iterate
   using runs, globals in
   let (a1, a2) := a in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%return' '(' a1 ',' a2 ',' a3 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (fold%return a := e
   along le
   as l, l_, l_list
   do let (a1, a2, a3) := a in iterate
   using runs, globals in
   let (a1, a2, a3) := a in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%return' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (fold%return a := e
   along le
   as l, l_, l_list
   do let (a1, a2, a3, a4) := a in iterate
   using runs, globals in
   let (a1, a2, a3, a4) := a in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%return' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (fold%return a := e
   along le
   as l, l_, l_list
   do let (a1, a2, a3, a4, a5) := a in iterate
   using runs, globals in
   let (a1, a2, a3, a4, a5) := a in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%return' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (fold%return a := e
   along le
   as l, l_, l_list
   do let (a1, a2, a3, a4, a5, a6) := a in iterate
   using runs, globals in
   let (a1, a2, a3, a4, a5, a6) := a in
   cont)
  (at level 50, left associativity) : monad_scope.


Notation "'fold%return' a ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (let%exit a :=
     fold%let a := normal_result e
     along le
     as l_car, l_tag
     do get_success a (fun a => iterate)
     using runs, globals
    in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%return' 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (fold%return ret := tt
   along le
   as l_car, l_tag
   do iterate
   using runs, globals in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%return' '(' a1 ',' a2 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (fold%return a := e
   along le
   as l_car, l_tag
   do let (a1, a2) := a in iterate
   using runs, globals in
   let (a1, a2) := a in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%return' '(' a1 ',' a2 ',' a3 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (fold%return a := e
   along le
   as l_car, l_tag
   do let (a1, a2, a3) := a in iterate
   using runs, globals in
   let (a1, a2, a3) := a in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%return' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (fold%return a := e
   along le
   as l_car, l_tag
   do let (a1, a2, a3, a4) := a in iterate
   using runs, globals in
   let (a1, a2, a3, a4) := a in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%return' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (fold%return a := e
   along le
   as l_car, l_tag
   do let (a1, a2, a3, a4, a5) := a in iterate
   using runs, globals in
   let (a1, a2, a3, a4, a5) := a in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%return' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (fold%return a := e
   along le
   as l_car, l_tag
   do let (a1, a2, a3, a4, a5, a6) := a in iterate
   using runs, globals in
   let (a1, a2, a3, a4, a5, a6) := a in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%break' 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (run%success
     fold%return
     along le
     as l_car, l_tag
     do iterate
     using runs, globals
     in result_skip
    in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%break' a ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (let%success a :=
     fold%return a := e
     along le
     as l_car, l_tag
     do iterate
     using runs, globals
     in result_success a
    in cont)
    (at level 50, left associativity) : monad_scope.

Notation "'fold%break' '(' a1 ',' a2 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (let%success (a1, a2) :=
     fold%return (a1, a2) := e
     along le
     as l_car, l_tag
     do iterate
     using runs, globals
     in result_success (a1, a2)
    in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%break' '(' a1 ',' a2 ',' a3 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (let%success (a1, a2, a3) :=
     fold%return (a1, a2, a3) := e
     along le
     as l_car, l_tag
     do iterate
     using runs, globals
     in result_success (a1, a2, a3)
    in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%break' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (let%success (a1, a2, a3, a4) :=
     fold%return (a1, a2, a3, a4) := e
     along le
     as l_car, l_tag
     do iterate
     using runs, globals
     in result_success (a1, a2, a3, a4)
    in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%break' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' runs ',' globals 'in' cont" :=
  (let%success (a1, a2, a3, a4, a5) :=
     fold%return (a1, a2, a3, a4, a5) := e
     along le
     as l_car, l_tag
     do iterate
     using runs, globals
     in result_success (a1, a2, a3, a4, a5)
    in cont)
  (at level 50, left associativity) : monad_scope.


(** * Long Jump Monads **)

(** R source code uses long jumps.
  This monad specifies their behaviour.
  It corresponds to a call to [setjmp] in C:
  [result_longjump] addressed to another [setjmp] are propagated,
  and [result_longjump] addressed to this particular [setjmp] puts the local environment
  as it was when calling [setjmp] the first time, but with the value returned by the
  [result_longjump] costructor instead of the default one. **)

Definition set_longjump runs (A : Type) mask (cjmpbuf : nat) (f : context_type -> result A) : result A :=
  fun globals S =>
    match f mask globals S with
    | rresult_success a S0 => rresult_success a S0
    | rresult_longjump n mask S0 =>
      ifb cjmpbuf = n then
        runs_set_longjump runs mask cjmpbuf f globals S0
      else result_longjump n mask globals S0
    | rresult_error_stack stack s S0 => rresult_error_stack stack s S0
    | rresult_impossible_stack stack s S0 => rresult_impossible_stack stack s S0
    | rresult_not_implemented_stack stack s => rresult_not_implemented_stack stack s
    | rresult_bottom S0 => rresult_bottom S0
    end.

Notation "'set%longjump' cjmpbuf 'as' ret 'using' runs 'in' cont" :=
  (set_longjump runs empty_context_type cjmpbuf (fun ret => cont))
  (at level 50, left associativity) : monad_scope.


(** * Finite Loops **)

(** The following loops terminate in a finite number of steps and thus do not use fuel. **)

(** ** Along Lists **)

Definition for_list A B (a : A) (l : list B) body :=
  fold_left (fun i (r : result A) =>
      let%success a := r in
      body a i)
    (result_success a) l.

Notation "'do%let' a ':=' e 'for' i 'in%list' l 'do' body" :=
  (for_list e l (fun a i => body))
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' 'for' i 'in%list' l 'do' body" :=
  (do%let _ := tt for i in%list l do body)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ')' ':=' a 'for' i 'in%list' l 'do' body" :=
  (do%let x := a for i in%list l
   do let (a1, a2) := x in body)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ')' ':=' a 'for' i 'in%list' l 'do' body" :=
  (do%let x := a for i in%list l
   do let '(a1, a2, a3) := x in body)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' a 'for' i 'in%list' l 'do' body" :=
  (do%let x := a for i in%list l
   do let '(a1, a2, a3, a4) := x in body)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' a 'for' i 'in%list' l 'do' body" :=
  (do%let x := a for i in%list l
   do let '(a1, a2, a3, a4, a5) := x in body)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' a 'for' i 'in%list' l 'do' body" :=
  (do%let x := a for i in%list l
   do let '(a1, a2, a3, a4, a5, a6) := x in body)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' 'for' i 'in%list' l 'do' body 'in' cont" :=
  (run%success
     do%let for i in%list l
     do body in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' a ':=' e 'for' i 'in%list' l 'do' body 'in' cont" :=
  (let%success a :=
     do%let a := e
     for i in%list l
     do body in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ')' ':=' e 'for' i 'in%list' l 'do' body 'in' cont" :=
  (let%success (a1, a2) :=
     do%let (a1, a2) := e
     for i in%list l
     do body in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ')' ':=' e 'for' i 'in%list' l 'do' body 'in' cont" :=
  (let%success (a1, a2, a3) :=
     do%let (a1, a2, a3) := e
     for i in%list l
     do body in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'for' i 'in%list' l 'do' body 'in' cont" :=
  (let%success (a1, a2, a3, a4) :=
     do%let (a1, a2, a3, a4) := e
     for i in%list l
     do body in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'for' i 'in%list' l 'do' body 'in' cont" :=
  (let%success (a1, a2, a3, a4, a5) :=
     do%let (a1, a2, a3, a4, a5) := e
     for i in%list l
     do body in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' e 'for' i 'in%list' l 'do' body 'in' cont" :=
  (let%success (a1, a2, a3, a4, a5, a6) :=
     do%let (a1, a2, a3, a4, a5, a6) := e
     for i in%list l
     do body in
   cont)
  (at level 50, left associativity) : monad_scope.


(** ** Along Intervals **)

Definition for_loop A (a : A) (start : nat) (last : int) body :=
  ifb last < start then
    result_success a
  else
    (** We know that [last >= 0]. **)
    do%let x := a
    for i in%list seq start (1 + Z.to_nat last - start) do
      body x i.

Notation "'do%let' a ':=' e 'for' i 'from' start 'to' last 'do' body" :=
  (for_loop e start last (fun a i => body))
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' 'for' i 'from' start 'to' last 'do' body" :=
  (do%let _ := tt for i from start to last do body)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ')' ':=' a 'for' i 'from' start 'to' last 'do' body" :=
  (do%let x := a for i from start to last
   do let (a1, a2) := x in body)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ')' ':=' a 'for' i 'from' start 'to' last 'do' body" :=
  (do%let x := a for i from start to last
   do let '(a1, a2, a3) := x in body)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' a 'for' i 'from' start 'to' last 'do' body" :=
  (do%let x := a for i from start to last
   do let '(a1, a2, a3, a4) := x in body)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' a 'for' i 'from' start 'to' last 'do' body" :=
  (do%let x := a for i from start to last
   do let '(a1, a2, a3, a4, a5) := x in body)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' a 'for' i 'from' start 'to' last 'do' body" :=
  (do%let x := a for i from start to last
   do let '(a1, a2, a3, a4, a5, a6) := x in body)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' 'for' i 'from' start 'to' last 'do' body 'in' cont" :=
  (run%success
     do%let for i from start to last
     do body in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' a ':=' e 'for' i 'from' start 'to' last 'do' body 'in' cont" :=
  (let%success a :=
     do%let a := e
     for i from start to last
     do body in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ')' ':=' e 'for' i 'from' start 'to' last 'do' body 'in' cont" :=
  (let%success (a1, a2) :=
     do%let (a1, a2) := e
     for i from start to last
     do body in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ')' ':=' e 'for' i 'from' start 'to' last 'do' body 'in' cont" :=
  (let%success (a1, a2, a3) :=
     do%let (a1, a2, a3) := e
     for i from start to last
     do body in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'for' i 'from' start 'to' last 'do' body 'in' cont" :=
  (let%success (a1, a2, a3, a4) :=
     do%let (a1, a2, a3, a4) := e
     for i from start to last
     do body in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'for' i 'from' start 'to' last 'do' body 'in' cont" :=
  (let%success (a1, a2, a3, a4, a5) :=
     do%let (a1, a2, a3, a4, a5) := e
     for i from start to last
     do body in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' e 'for' i 'from' start 'to' last 'do' body 'in' cont" :=
  (let%success (a1, a2, a3, a4, a5, a6) :=
     do%let (a1, a2, a3, a4, a5, a6) := e
     for i from start to last
     do body in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%exit' a ':=' e 'for' i 'from' start 'to' last 'do' body 'in' cont" :=
  (let%exit a :=
     do%let ret := normal_result e
     for i from start to last
     do get_success ret (fun a => body) in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%exit' 'for' i 'from' start 'to' last 'do' body 'in' cont" :=
  (do%exit _ := tt
   for i from start to last
   do body in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%exit' '(' a1 ',' a2 ')' ':=' e 'for' i 'from' start 'to' last 'do' body 'in' cont" :=
  (do%exit a := e
   for i from start to last
   do let (a1, a2) := a in body
   in let (a1, a2) := a in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%exit' '(' a1 ',' a2 ',' a3 ')' ':=' e 'for' i 'from' start 'to' last 'do' body 'in' cont" :=
  (do%exit a := e
   for i from start to last
   do let '(a1, a2, a3) := a in body
   in let '(a1, a2, a3) := a in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%exit' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'for' i 'from' start 'to' last 'do' body 'in' cont" :=
  (do%exit a := e
   for i from start to last
   do let '(a1, a2, a3, a4) := a in body
   in let '(a1, a2, a3, a4) := a in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%exit' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'for' i 'from' start 'to' last 'do' body 'in' cont" :=
  (do%exit a := e
   for i from start to last
   do let '(a1, a2, a3, a4, a5) := a in body
   in let '(a1, a2, a3, a4, a5) := a in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%exit' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' e 'for' i 'from' start 'to' last 'do' body 'in' cont" :=
  (do%exit a := e
   for i from start to last
   do let '(a1, a2, a3, a4, a5, a6) := a in body
   in let '(a1, a2, a3, a4, a5, a6) := a in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%break' 'for' i 'from' start 'to' last 'do' body 'in' cont" :=
  (run%success
     do%exit
     for i from start to last
     do body
     in result_skip
   in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%break' a ':=' e 'for' i 'from' start 'to' last 'do' body 'in' cont" :=
  (let%success a :=
     do%exit a := e
     for i from start to last
     do body
     in result_success a
   in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%break' '(' a1 ',' a2 ')' ':=' e 'for' i 'from' start 'to' last 'do' body 'in' cont" :=
  (let%success (a1, a2) :=
     do%exit (a1, a2) := e
     for i from start to last
     do body
     in result_success (a1, a2)
   in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%break' '(' a1 ',' a2 ',' a3 ')' ':=' e 'for' i 'from' start 'to' last 'do' body 'in' cont" :=
  (let%success (a1, a2, a3) :=
     do%exit (a1, a2, a3) := e
     for i from start to last
     do body
     in result_success (a1, a2, a3)
   in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%break' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'for' i 'from' start 'to' last 'do' body 'in' cont" :=
  (let%success (a1, a2, a3, a4) :=
     do%exit (a1, a2, a3, a4) := e
     for i from start to last
     do body
     in result_success (a1, a2, a3, a4)
   in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%break' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'for' i 'from' start 'to' last 'do' body 'in' cont" :=
  (let%success (a1, a2, a3, a4, a5) :=
     do%exit (a1, a2, a3, a4, a5) := e
     for i from start to last
     do body
     in result_success (a1, a2, a3, a4, a5)
   in cont)
  (at level 50, left associativity) : monad_scope.


(** ** Along Arrays **)

Definition for_array A B (a : A) (array : ArrayList.array B) body :=
  do%let x := a
  for i in%list ArrayList.to_list array do
    body x i.

Notation "'do%let' a ':=' e 'for' i 'in%array' array 'do' body" :=
  (for_array e array (fun a i => body))
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' 'for' i 'in%array' array 'do' body" :=
  (do%let _ := tt for i in%array array do body)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ')' ':=' a 'for' i 'in%array' array 'do' body" :=
  (do%let x := a for i in%array array
   do let (a1, a2) := x in body)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ')' ':=' a 'for' i 'in%array' array 'do' body" :=
  (do%let x := a for i in%array array
   do let '(a1, a2, a3) := x in body)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' a 'for' i 'in%array' array 'do' body" :=
  (do%let x := a for i in%array array
   do let '(a1, a2, a3, a4) := x in body)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' a 'for' i 'in%array' array 'do' body" :=
  (do%let x := a for i in%array array
   do let '(a1, a2, a3, a4, a5) := x in body)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' a 'for' i 'in%array' array 'do' body" :=
  (do%let x := a for i in%array array
   do let '(a1, a2, a3, a4, a5, a6) := x in body)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' 'for' i 'in%array' array 'do' body 'in' cont" :=
  (run%success
     do%let for i in%array array
     do body in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' a ':=' e 'for' i 'in%array' array 'do' body 'in' cont" :=
  (let%success a :=
     do%let a := e
     for i in%array array
     do body in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ')' ':=' e 'for' i 'in%array' array 'do' body 'in' cont" :=
  (let%success (a1, a2) :=
     do%let (a1, a2) := e
     for i in%array array
     do body in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ')' ':=' e 'for' i 'in%array' array 'do' body 'in' cont" :=
  (let%success (a1, a2, a3) :=
     do%let (a1, a2, a3) := e
     for i in%array array
     do body in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'for' i 'in%array' array 'do' body 'in' cont" :=
  (let%success (a1, a2, a3, a4) :=
     do%let (a1, a2, a3, a4) := e
     for i in%array array
     do body in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'for' i 'in%array' array 'do' body 'in' cont" :=
  (let%success (a1, a2, a3, a4, a5) :=
     do%let (a1, a2, a3, a4, a5) := e
     for i in%array array
     do body in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' e 'for' i 'in%array' array 'do' body 'in' cont" :=
  (let%success (a1, a2, a3, a4, a5, a6) :=
     do%let (a1, a2, a3, a4, a5, a6) := e
     for i in%array array
     do body in
   cont)
  (at level 50, left associativity) : monad_scope.

