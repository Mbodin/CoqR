(** Monads.
  Provides monads to manipulate R objects easily. **)

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
Require Export State InternalTypes.


(** The monadic type is defined in the file InternalTypes.v. **)

Delimit Scope monad_scope with monad.
Open Scope monad_scope.


(** * Generic Monads **)

(** ** Function definitions **)

Definition add_stack (A : Type) fname (r : result A) : result A :=
  match r with
  | result_success S0 a => result_success S0 a
  | result_longjump S0 n t => result_longjump S0 n t
  | result_error_stack S0 stack s => result_error_stack S0 (fname :: stack) s
  | result_impossible_stack S0 stack s => result_impossible_stack S0 (fname :: stack) s
  | result_not_implemented_stack stack s => result_not_implemented_stack (fname :: stack) s
  | result_bottom S0 => result_bottom S0
  end.

Notation "'add%stack' fname 'in' cont" :=
  (add_stack fname cont)
  (at level 50, left associativity) : monad_scope.


Definition unimplemented_function (A : Type) fname : result A :=
  add%stack fname in
  result_not_implemented ("Function not implemented: " ++ fname ++ ".").
Arguments unimplemented_function [A].


(** ** [let]-monads **)

(** The monad for result. **)
Definition if_success (A B : Type) (r : result A) (f : state -> A -> result B) : result B :=
  match r with
  | result_success S0 a => f S0 a
  | result_longjump S0 n t => result_longjump S0 n t
  | result_error_stack S0 stack s => result_error_stack S0 stack s
  | result_impossible_stack S0 stack s => result_impossible_stack S0 stack s
  | result_not_implemented_stack stack s => result_not_implemented_stack stack s
  | result_bottom S0 => result_bottom S0
  end.

Notation "'let%success' a ':=' r 'using' S 'in' cont" :=
  (if_success r (fun S a => cont))
  (at level 50, left associativity) : monad_scope.

Notation "'let%success' '(' a1 ',' a2 ')' ':=' r 'using' S 'in' cont" :=
  (let%success x := r using S in
   let (a1, a2) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%success' '(' a1 ',' a2 ',' a3 ')' ':=' r 'using' S 'in' cont" :=
  (let%success x := r using S in
   let '(a1, a2, a3) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%success' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' r 'using' S 'in' cont" :=
  (let%success x := r using S in
   let '(a1, a2, a3, a4) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' r 'using' S 'in' cont" :=
  (let%success x := r using S in
   let '(a1, a2, a3, a4, a5) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' r 'using' S 'in' cont" :=
  (let%success x := r using S in
   let '(a1, a2, a3, a4, a5, a6) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ',' a7 ')' ':=' r 'using' S 'in' cont" :=
  (let%success x := r using S in
   let '(a1, a2, a3, a4, a5, a6, a7) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ',' a7 ',' a8 ')' ':=' r 'using' S 'in' cont" :=
  (let%success x := r using S in
   let '(a1, a2, a3, a4, a5, a6, a7, a8) := x in cont)
  (at level 50, left associativity) : monad_scope.


(** Similar to [if_success], but from an option type. We suppose that the option type is defined. **)
Definition if_defined_msg msg (A B : Type) S (o : option A) (f : A -> result B) : result B :=
  match o with
  | Some x => f x
  | None =>
    let msg :=
      ifb msg = ""%string then ""%string else (" (" ++ msg ++ ")")%string in
    add%stack "if_defined" ++ msg in
    result_impossible S "Undefined result."
  end.

Definition if_defined := if_defined_msg "".

Notation "'let%defined' a ':=' o 'using' S 'in' cont" :=
  (if_defined S o (fun a => cont))
  (at level 50, left associativity) : monad_scope.

Notation "'let%defined' '(' a1 ',' a2 ')' ':=' o 'using' S 'in' cont" :=
  (let%defined x := o using S in
   let (a1, a2) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%defined' '(' a1 ',' a2 ',' a3 ')' ':=' o 'using' S 'in' cont" :=
  (let%defined x := o using S in
   let '(a1, a2, a3) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%defined' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' o 'using' S 'in' cont" :=
  (let%defined x := o using S in
   let '(a1, a2, a3, a4) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%defined' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' o 'using' S 'in' cont" :=
  (let%defined x := o using S in
   let '(a1, a2, a3, a4, a5) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%defined' a ':=' o 'with' msg 'using' S 'in' cont" :=
  (if_defined_msg msg S o (fun a => cont))
  (at level 50, left associativity) : monad_scope.

Notation "'let%defined' '(' a1 ',' a2 ')' ':=' o 'with' msg 'using' S 'in' cont" :=
  (let%defined x := o with msg using S in
   let (a1, a2) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%defined' '(' a1 ',' a2 ',' a3 ')' ':=' o 'with' msg 'using' S 'in' cont" :=
  (let%defined x := o with msg using S in
   let '(a1, a2, a3) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%defined' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' o 'with' msg 'using' S 'in' cont" :=
  (let%defined x := o with msg using S in
   let '(a1, a2, a3, a4) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%defined' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' o 'with' msg 'using' S 'in' cont" :=
  (let%defined x := o with msg using S in
   let '(a1, a2, a3, a4, a5) := x in cont)
  (at level 50, left associativity) : monad_scope.


Notation "'write%defined' p ':=' p_ 'using' S 'in' cont" :=
  (let%defined S := write_SExp S p p_ with "write%defined" using S in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'read%defined' p_ ':=' p 'using' S 'in' cont" :=
  (let%defined p_ := read_SExp S p with "read%defined" using S in cont)
  (at level 50, left associativity) : monad_scope.


(** ** Flow-control Monads **)

Notation "'run%success' c 'using' S 'in' cont" :=
  (let%success _ := c using S in cont)
  (at level 50, left associativity) : monad_scope.

Definition result_skip S :=
  result_success S tt.

Definition if_then_else_success A (b : result bool) (c1 c2 : state -> result A) :=
  let%success b := b using S in
  if b then c1 S else c2 S.

Notation "'if%success' b 'using' S 'then' c1 'else' c2" :=
  (if_then_else_success b (fun S => c1) (fun S => c2))
  (at level 50, left associativity) : monad_scope.

Definition if_then_success A b c cont : result A :=
  run%success
    if%success b using S then
      c S
    else result_skip S using S in
  cont S.

Notation "'if%success' b 'using' S 'then' c 'in' cont" :=
  (if_then_success b (fun S => c) (fun S => cont))
  (at level 50, left associativity) : monad_scope.

Definition if_option_defined A B (c : result (option A)) cont_then cont_else : result B :=
  let%success ans := c using S in
  match ans with
  | Some ans => cont_then S ans
  | None => cont_else S
  end.

Notation "'if%defined' ans ':=' c 'using' S 'then' cont_then 'else' cont_else" :=
  (if_option_defined c (fun S ans => cont_then) (fun S => cont_else))
  (at level 50, left associativity) : monad_scope.


(** * Monads to View Objects Differently **)

(** ** Basic Language Elements **)

Definition if_is_prim A S (e_ : SExpRec) (cont : NonVector_SExpRec -> PrimSxp_struct -> result A) : result A :=
  let%defined e_ := get_NonVector e_ with "if_is_prim, vector test" using S in
  let%defined e_prim := get_primSxp e_ with "if_is_prim, prim test" using S in
  cont e_ e_prim.

Notation "'let%prim' a_ ',' a_prim ':=' e_ 'using' S 'in' cont" :=
  (if_is_prim S e_ (fun a_ a_prim => cont))
  (at level 50, left associativity) : monad_scope.


Definition if_is_sym A S (e_ : SExpRec) (cont : NonVector_SExpRec -> SymSxp_struct -> result A) : result A :=
  let%defined e_ := get_NonVector e_ with "if_is_sym, vector test" using S in
  let%defined e_sym := get_symSxp e_ with "if_is_sym, sym test" using S in
  cont e_ e_sym.

Notation "'let%sym' a_ ',' a_sym ':=' e_ 'using' S 'in' cont" :=
  (if_is_sym S e_ (fun a_ a_sym => cont))
  (at level 50, left associativity) : monad_scope.


Definition if_is_list A S (e_ : SExpRec) (cont : NonVector_SExpRec -> ListSxp_struct -> result A) : result A :=
  let%defined e_ := get_NonVector e_ with "if_is_list, vector test" using S in
  let%defined e_list := get_listSxp e_ with "if_is_list, list test" using S in
  cont e_ e_list.

Notation "'let%list' a_ ',' a_list ':=' e_ 'using' S 'in' cont" :=
  (if_is_list S e_ (fun a_ a_list => cont))
  (at level 50, left associativity) : monad_scope.


Definition if_is_env A S (e_ : SExpRec) (cont : NonVector_SExpRec -> EnvSxp_struct -> result A) : result A :=
  let%defined e_ := get_NonVector e_ with "if_is_env, vector test" using S in
  let%defined e_env := get_envSxp e_ with "if_is_env, env test" using S in
  cont e_ e_env.

Notation "'let%env' a_ ',' a_env ':=' e_ 'using' S 'in' cont" :=
  (if_is_env S e_ (fun a_ a_env => cont))
  (at level 50, left associativity) : monad_scope.


Definition if_is_clo A S (e_ : SExpRec) (cont : NonVector_SExpRec -> CloSxp_struct -> result A) : result A :=
  let%defined e_ := get_NonVector e_ with "if_is_clo, vector test" using S in
  let%defined e_clo := get_cloSxp e_ with "if_is_clo, clo test" using S in
  cont e_ e_clo.

Notation "'let%clo' a_ ',' a_clo ':=' e_ 'using' S 'in' cont" :=
  (if_is_clo S e_ (fun a_ a_clo => cont))
  (at level 50, left associativity) : monad_scope.


Definition if_is_prom A S (e_ : SExpRec) (cont : NonVector_SExpRec -> PromSxp_struct -> result A) : result A :=
  let%defined e_ := get_NonVector e_ with "if_is_prom, vector test" using S in
  let%defined e_prom := get_promSxp e_ with "if_is_prom, prom test" using S in
  cont e_ e_prom.

Notation "'let%prom' a_ ',' a_prom ':=' e_ 'using' S 'in' cont" :=
  (if_is_prom S e_ (fun a_ a_prom => cont))
  (at level 50, left associativity) : monad_scope.


Definition read_as_prim A S (e : SEXP) cont : result A :=
  let%defined e_ := read_SExp S e with "read_as_prim" using S in
  let%prim e_, e_prim := e_ using S in
  cont e_ e_prim.

Notation "'read%prim' e_ ',' e_prim ':=' e 'using' S 'in' cont" :=
  (read_as_prim S e (fun e_ e_prim => cont))
  (at level 50, left associativity) : monad_scope.


Definition read_as_sym A S (e : SEXP) cont : result A :=
  let%defined e_ := read_SExp S e with "read_as_sym" using S in
  let%sym e_, e_sym := e_ using S in
  cont e_ e_sym.

Notation "'read%sym' e_ ',' e_sym ':=' e 'using' S 'in' cont" :=
  (read_as_sym S e (fun e_ e_sym => cont))
  (at level 50, left associativity) : monad_scope.


Definition read_as_list A S (e : SEXP) cont : result A :=
  let%defined e_ := read_SExp S e with "read_as_list" using S in
  let%list e_, e_list := e_ using S in
  cont e_ e_list.

Notation "'read%list' e_ ',' e_list ':=' e 'using' S 'in' cont" :=
  (read_as_list S e (fun e_ e_list => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_as_list_all A S (e : SEXP) cont : result A :=
  read%list e_, e_list := e using S in
  cont e_ (list_carval e_list) (list_cdrval e_list) (list_tagval e_list).

Notation "'read%list' e_ ',' e_car ',' e_cdr ',' e_tag ':=' e 'using' S 'in' cont" :=
  (read_as_list_all S e (fun e_ e_car e_cdr e_tag => cont))
    (at level 50, left associativity) : monad_scope.

Definition read_as_list_components A S (e : SEXP) cont : result A :=
  read%list _, e_car, e_cdr, e_tag := e using S in
  cont e_car e_cdr e_tag.

Notation "'read%list' e_car ',' e_cdr ',' e_tag ':=' e 'using' S 'in' cont" :=
  (read_as_list_components S e (fun e_car e_cdr e_tag => cont))
  (at level 50, left associativity) : monad_scope.


Definition read_as_env A S (e : SEXP) cont : result A :=
  let%defined e_ := read_SExp S e with "read_as_env" using S in
  let%env e_, e_env := e_ using S in
  cont e_ e_env.

Notation "'read%env' e_ ',' e_env ':=' e 'using' S 'in' cont" :=
  (read_as_env S e (fun e_ e_env => cont))
  (at level 50, left associativity) : monad_scope.


Definition read_as_clo A S (e : SEXP) cont : result A :=
  let%defined e_ := read_SExp S e with "read_as_clo" using S in
  let%clo e_, e_clo := e_ using S in
  cont e_ e_clo.

Notation "'read%clo' e_ ',' e_clo ':=' e 'using' S 'in' cont" :=
  (read_as_clo S e (fun e_ e_clo => cont))
  (at level 50, left associativity) : monad_scope.


Definition read_as_prom A S (e : SEXP) cont : result A :=
  let%defined e_ := read_SExp S e with "read_as_prom" using S in
  let%prom e_, e_prom := e_ using S in
  cont e_ e_prom.

Notation "'read%prom' e_ ',' e_prom ':=' e 'using' S 'in' cont" :=
  (read_as_prom S e (fun e_ e_prom => cont))
  (at level 50, left associativity) : monad_scope.


(** ** Vectors **)

Definition read_cell_Vector_SExpRec A B S (v : Vector_SExpRec A) n cont : result B :=
  let%defined c := ArrayList.read_option v n with "read_cell_Vector_SExpRec" using S in
  cont c.

Notation "'read%cell' c ':=' v 'at' n 'using' S 'in' cont" :=
  (read_cell_Vector_SExpRec S v n (fun c => cont))
  (at level 50, left associativity) : monad_scope.


Definition update_Vector_SExpRec_cell A (v : Vector_SExpRec A) n c :=
  ifb n < ArrayList.length v then
    Some (update_Vector_SExpRec v (ArrayList.write v n c))
  else None.

Definition let_VectorChar A S e_ cont : result A :=
  let%defined e_vector := get_VectorChar e_ with "let_VectorChar" using S in
  cont S e_vector.

Notation "'let%VectorChar' e_vector ':=' e_ 'using' S 'in' cont" :=
  (let_VectorChar S e_ (fun S e_vector => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_as_VectorChar A S (e : SEXP) cont : result A :=
  let%defined e_ := read_SExp S e with "read_as_VectorChar" using S in
  let%VectorChar e_vector := e_ using S in
  cont e_vector.

Notation "'read%VectorChar' e_ ':=' e 'using' S 'in' cont" :=
  (read_as_VectorChar S e (fun e_ => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_nth_cell_VectorChar A S e_ n cont : result A :=
  let%VectorChar e_ := e_ using S in
  read%cell c := e_ at n using S in
  cont c.

Notation "'let%Char' c ':=' e_ 'at' n 'using' S 'in' cont" :=
  (read_nth_cell_VectorChar S e_ n (fun c => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_nth_cell_Char A S e n cont : result A :=
  read%VectorChar e_ := e using S in
  read%cell c := e_ at n using S in
  cont c.

Notation "'read%Char' c ':=' e 'at' n 'using' S 'in' cont" :=
  (read_nth_cell_Char S e n (fun c => cont))
  (at level 50, left associativity) : monad_scope.

Definition write_VectorChar A S e v cont : result A :=
  read%VectorChar e_ := e using S in
  let e_ := update_Vector_SExpRec e_ v in
  write%defined e := SExpRec_VectorChar e_ using S in
  cont S.

Notation "'write%VectorChar' e ':=' v 'using' S 'in' cont" :=
  (write_VectorChar S e v (fun S => cont))
  (at level 50, left associativity) : monad_scope.

Definition write_nth_cell_VectorChar A S e n c cont : result A :=
  read%VectorChar e_ := e using S in
  let%defined e_ := update_Vector_SExpRec_cell e_ n c with "write_nth_cell_VectorChar" using S in
  write%defined e := SExpRec_VectorChar e_ using S in
  cont S.

Notation "'write%Char' e 'at' n ':=' c 'using' S 'in' cont" :=
  (write_nth_cell_VectorChar S e n c (fun S => cont))
  (at level 50, left associativity) : monad_scope.


Definition let_VectorLogical A S e_ cont : result A :=
  let%defined e_vector := get_VectorLogical e_ with "let_VectorLogical" using S in
  cont S e_vector.

Notation "'let%VectorLogical' e_vector ':=' e_ 'using' S 'in' cont" :=
  (let_VectorLogical S e_ (fun S e_vector => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_as_VectorLogical A S (e : SEXP) cont : result A :=
  let%defined e_ := read_SExp S e with "read_as_VectorLogical" using S in
  let%VectorLogical e_vector := e_ using S in
  cont e_vector.

Notation "'read%VectorLogical' e_ ':=' e 'using' S 'in' cont" :=
  (read_as_VectorLogical S e (fun e_ => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_nth_cell_VectorLogical A S e_ n cont : result A :=
  let%VectorLogical e_ := e_ using S in
  read%cell c := e_ at n using S in
  cont c.

Notation "'let%Logical' c ':=' e_ 'at' n 'using' S 'in' cont" :=
  (read_nth_cell_VectorLogical S e_ n (fun c => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_nth_cell_Logical A S e n cont : result A :=
  read%VectorLogical e_ := e using S in
  read%cell c := e_ at n using S in
  cont c.

Notation "'read%Logical' c ':=' e 'at' n 'using' S 'in' cont" :=
  (read_nth_cell_Logical S e n (fun c => cont))
  (at level 50, left associativity) : monad_scope.

Definition write_VectorLogical A S e v cont : result A :=
  read%VectorLogical e_ := e using S in
  let e_ := update_Vector_SExpRec e_ v in
  write%defined e := SExpRec_VectorLogical e_ using S in
  cont S.

Notation "'write%VectorLogical' e ':=' v 'using' S 'in' cont" :=
  (write_VectorLogical S e v (fun S => cont))
  (at level 50, left associativity) : monad_scope.

Definition write_nth_cell_VectorLogical A S e n c cont : result A :=
  read%VectorLogical e_ := e using S in
  let%defined e_ := update_Vector_SExpRec_cell e_ n c with "write_nth_cell_VectorLogical" using S in
  write%defined e := SExpRec_VectorLogical e_ using S in
  cont S.

Notation "'write%Logical' e 'at' n ':=' c 'using' S 'in' cont" :=
  (write_nth_cell_VectorLogical S e n c (fun S => cont))
  (at level 50, left associativity) : monad_scope.


Definition let_VectorInteger A S e_ cont : result A :=
  let%defined e_vector := get_VectorInteger e_ with "let_VectorInteger" using S in
  cont S e_vector.

Notation "'let%VectorInteger' e_vector ':=' e_ 'using' S 'in' cont" :=
  (let_VectorInteger S e_ (fun S e_vector => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_as_VectorInteger A S (e : SEXP) cont : result A :=
  let%defined e_ := read_SExp S e with "read_as_VectorInteger" using S in
  let%VectorInteger e_vector := e_ using S in
  cont e_vector.

Notation "'read%VectorInteger' e_ ':=' e 'using' S 'in' cont" :=
  (read_as_VectorInteger S e (fun e_ => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_nth_cell_VectorInteger A S e_ n cont : result A :=
  let%VectorInteger e_ := e_ using S in
  read%cell c := e_ at n using S in
  cont c.

Notation "'let%Integer' c ':=' e_ 'at' n 'using' S 'in' cont" :=
  (read_nth_cell_VectorInteger S e_ n (fun c => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_nth_cell_Integer A S e n cont : result A :=
  read%VectorInteger e_ := e using S in
  read%cell c := e_ at n using S in
  cont c.

Notation "'read%Integer' c ':=' e 'at' n 'using' S 'in' cont" :=
  (read_nth_cell_Integer S e n (fun c => cont))
  (at level 50, left associativity) : monad_scope.

Definition write_VectorInteger A S e v cont : result A :=
  read%VectorInteger e_ := e using S in
  let e_ := update_Vector_SExpRec e_ v in
  write%defined e := SExpRec_VectorInteger e_ using S in
  cont S.

Notation "'write%VectorInteger' e ':=' v 'using' S 'in' cont" :=
  (write_VectorInteger S e v (fun S => cont))
  (at level 50, left associativity) : monad_scope.

Definition write_nth_cell_VectorInteger A S e n c cont : result A :=
  read%VectorInteger e_ := e using S in
  let%defined e_ := update_Vector_SExpRec_cell e_ n c with "write_nth_cell_VectorInteger" using S in
  write%defined e := SExpRec_VectorInteger e_ using S in
  cont S.

Notation "'write%Integer' e 'at' n ':=' c 'using' S 'in' cont" :=
  (write_nth_cell_VectorInteger S e n c (fun S => cont))
  (at level 50, left associativity) : monad_scope.


Definition let_VectorReal A S e_ cont : result A :=
  let%defined e_vector := get_VectorReal e_ with "let_VectorReal" using S in
  cont S e_vector.

Notation "'let%VectorReal' e_vector ':=' e_ 'using' S 'in' cont" :=
  (let_VectorReal S e_ (fun S e_vector => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_as_VectorReal A S (e : SEXP) cont : result A :=
  let%defined e_ := read_SExp S e with "read_as_VectorReal" using S in
  let%VectorReal e_vector := e_ using S in
  cont e_vector.

Notation "'read%VectorReal' e_ ':=' e 'using' S 'in' cont" :=
  (read_as_VectorReal S e (fun e_ => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_nth_cell_VectorReal A S e_ n cont : result A :=
  let%VectorReal e_ := e_ using S in
  read%cell c := e_ at n using S in
  cont c.

Notation "'let%Real' c ':=' e_ 'at' n 'using' S 'in' cont" :=
  (read_nth_cell_VectorReal S e_ n (fun c => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_nth_cell_Real A S e n cont : result A :=
  read%VectorReal e_ := e using S in
  read%cell c := e_ at n using S in
  cont c.

Notation "'read%Real' c ':=' e 'at' n 'using' S 'in' cont" :=
  (read_nth_cell_Real S e n (fun c => cont))
  (at level 50, left associativity) : monad_scope.

Definition write_VectorReal A S e v cont : result A :=
  read%VectorReal e_ := e using S in
  let e_ := update_Vector_SExpRec e_ v in
  write%defined e := SExpRec_VectorReal e_ using S in
  cont S.

Notation "'write%VectorReal' e ':=' v 'using' S 'in' cont" :=
  (write_VectorReal S e v (fun S => cont))
  (at level 50, left associativity) : monad_scope.

Definition write_nth_cell_VectorReal A S e n c cont : result A :=
  read%VectorReal e_ := e using S in
  let%defined e_ := update_Vector_SExpRec_cell e_ n c with "write_nth_cell_VectorReal" using S in
  write%defined e := SExpRec_VectorReal e_ using S in
  cont S.

Notation "'write%Real' e 'at' n ':=' c 'using' S 'in' cont" :=
  (write_nth_cell_VectorReal S e n c (fun S => cont))
  (at level 50, left associativity) : monad_scope.


Definition let_VectorComplex A S e_ cont : result A :=
  let%defined e_vector := get_VectorComplex e_ with "let_VectorComplex" using S in
  cont S e_vector.

Notation "'let%VectorComplex' e_vector ':=' e_ 'using' S 'in' cont" :=
  (let_VectorComplex S e_ (fun S e_vector => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_as_VectorComplex A S (e : SEXP) cont : result A :=
  let%defined e_ := read_SExp S e with "read_as_VectorComplex" using S in
  let%VectorComplex e_vector := e_ using S in
  cont e_vector.

Notation "'read%VectorComplex' e_ ':=' e 'using' S 'in' cont" :=
  (read_as_VectorComplex S e (fun e_ => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_nth_cell_VectorComplex A S e_ n cont : result A :=
  let%VectorComplex e_ := e_ using S in
  read%cell c := e_ at n using S in
  cont c.

Notation "'let%Complex' c ':=' e_ 'at' n 'using' S 'in' cont" :=
  (read_nth_cell_VectorComplex S e_ n (fun c => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_nth_cell_Complex A S e n cont : result A :=
  read%VectorComplex e_ := e using S in
  read%cell c := e_ at n using S in
  cont c.

Notation "'read%Complex' c ':=' e 'at' n 'using' S 'in' cont" :=
  (read_nth_cell_Complex S e n (fun c => cont))
  (at level 50, left associativity) : monad_scope.

Definition write_VectorComplex A S e v cont : result A :=
  read%VectorComplex e_ := e using S in
  let e_ := update_Vector_SExpRec e_ v in
  write%defined e := SExpRec_VectorComplex e_ using S in
  cont S.

Notation "'write%VectorComplex' e ':=' v 'using' S 'in' cont" :=
  (write_VectorComplex S e v (fun S => cont))
  (at level 50, left associativity) : monad_scope.

Definition write_nth_cell_VectorComplex A S e n c cont : result A :=
  read%VectorComplex e_ := e using S in
  let%defined e_ := update_Vector_SExpRec_cell e_ n c with "write_nth_cell_VectorComplex" using S in
  write%defined e := SExpRec_VectorComplex e_ using S in
  cont S.

Notation "'write%Complex' e 'at' n ':=' c 'using' S 'in' cont" :=
  (write_nth_cell_VectorComplex S e n c (fun S => cont))
  (at level 50, left associativity) : monad_scope.


Definition let_VectorPointer A S e_ cont : result A :=
  let%defined e_vector := get_VectorPointer e_ with "let_VectorPointer" using S in
  cont S e_vector.

Notation "'let%VectorPointer' e_vector ':=' e_ 'using' S 'in' cont" :=
  (let_VectorPointer S e_ (fun S e_vector => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_as_VectorPointer A S (e : SEXP) cont : result A :=
  let%defined e_ := read_SExp S e with "read_as_VectorPointer" using S in
  let%VectorPointer e_vector := e_ using S in
  cont e_vector.

Notation "'read%VectorPointer' e_ ':=' e 'using' S 'in' cont" :=
  (read_as_VectorPointer S e (fun e_ => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_nth_cell_VectorPointer A S e_ n cont : result A :=
  let%VectorPointer e_ := e_ using S in
  read%cell c := e_ at n using S in
  cont c.

Notation "'let%Pointer' c ':=' e_ 'at' n 'using' S 'in' cont" :=
  (read_nth_cell_VectorPointer S e_ n (fun c => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_nth_cell_Pointer A S e n cont : result A :=
  read%VectorPointer e_ := e using S in
  read%cell c := e_ at n using S in
  cont c.

Notation "'read%Pointer' c ':=' e 'at' n 'using' S 'in' cont" :=
  (read_nth_cell_Pointer S e n (fun c => cont))
  (at level 50, left associativity) : monad_scope.

Definition write_VectorPointer A S e v cont : result A :=
  read%VectorPointer e_ := e using S in
  let e_ := update_Vector_SExpRec e_ v in
  write%defined e := SExpRec_VectorPointer e_ using S in
  cont S.

Notation "'write%VectorPointer' e ':=' v 'using' S 'in' cont" :=
  (write_VectorPointer S e v (fun S => cont))
  (at level 50, left associativity) : monad_scope.

Definition write_nth_cell_VectorPointer A S e n c cont : result A :=
  read%VectorPointer e_ := e using S in
  let%defined e_ := update_Vector_SExpRec_cell e_ n c with "write_nth_cell_VectorPointer" using S in
  write%defined e := SExpRec_VectorPointer e_ using S in
  cont S.

Notation "'write%Pointer' e 'at' n ':=' c 'using' S 'in' cont" :=
  (write_nth_cell_VectorPointer S e n c (fun S => cont))
  (at level 50, left associativity) : monad_scope.


(** * Other Monads **)

(** ** [map]-monads **)

(** Mapping on-place the content of a pointer is a frequent scheme.
  Here is a monad for it. **)
Definition map_pointer (A : Type) S (map : SExpRec -> SExpRec) (p : SEXP)
    (cont : state -> result A) : result A :=
  read%defined p_ := p using S in
  write%defined p := map p_ using S in
  cont S.

Notation "'map%pointer' p 'with' map 'using' S 'in' cont" :=
  (map_pointer S map p (fun S => cont))
  (at level 50, left associativity) : monad_scope.

Notation "'map%gp' p 'with' f 'using' S 'in' cont" :=
  (map%pointer p with map_gp f using S in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'set%gp' p 'with' v 'using' S 'in' cont" :=
  (map%pointer p with set_gp v using S in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'set%attrib' p ':=' a 'using' S 'in' cont" :=
  (map%pointer p with set_attrib a using S in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'set%obj' p ':=' o 'using' S 'in' cont" :=
  (map%pointer p with set_obj o using S in cont)
  (at level 50, left associativity) : monad_scope.


(** Updating a list. **)
Definition map_list A S f (p : SEXP) (cont : state -> result A) : result A :=
  read%list p_, p_list := p using S in
  let p_ := {|
      NonVector_SExpRec_header := p_ ;
      NonVector_SExpRec_data := f p_list
    |} in
  write%defined p := p_ using S in
  cont S.

Notation "'map%list' p 'with' map 'using' S 'in' cont" :=
  (map_list S map p (fun S => cont))
  (at level 50, left associativity) : monad_scope.

(** Updating the first element of a list. **)
Definition set_car A S car (p : SEXP) (f : state -> result A) : result A :=
  map%list p with set_car_list car using S in f S.

Notation "'set%car' p ':=' car 'using' S 'in' cont" :=
  (set_car S car p (fun S => cont))
  (at level 50, left associativity) : monad_scope.

(** Updating the tail of a list. **)
Definition set_cdr A S cdr (p : SEXP) (f : state -> result A) : result A :=
  map%list p with set_cdr_list cdr using S in f S.

Notation "'set%cdr' p ':=' cdr 'using' S 'in' cont" :=
  (set_cdr S cdr p (fun S => cont))
  (at level 50, left associativity) : monad_scope.

(** Updating the tag of a list. **)
Definition set_tag A S tag (p : SEXP) (f : state -> result A) : result A :=
  map%list p with set_tag_list tag using S in f S.

Notation "'set%tag' p ':=' tag 'using' S 'in' cont" :=
  (set_tag S tag p (fun S => cont))
  (at level 50, left associativity) : monad_scope.
