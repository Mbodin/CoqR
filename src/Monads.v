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
Require Import Ascii.
Require Export State InternalTypes.


(** The monadic type is defined in the file InternalTypes.v. **)

Delimit Scope monad_scope with monad.
Open Scope monad_scope.


(** * Generic Monads **)

(** ** Manipulating the current state. **)

Definition get_state A (cont : state -> result A) : result A :=
  fun S => cont S S.

(** Getting the current state. **)
Notation "'get%state' S 'in' cont" :=
  (get_state (fun S => cont))
  (at level 50, left associativity) : monad_scope.

(** Replacing the current state by another one. **)
Definition set_state A S (cont : result A) : result A :=
  fun _ => cont S.

Notation "'set%state' S 'in' cont" :=
  (set_state S cont)
  (at level 50, left associativity) : monad_scope.

Definition map_state A (f : state -> state) (cont : result A) : result A :=
  get%state S in
  set%state f S in
  cont.

Notation "'map%state' S 'in' cont" :=
  (map_state S cont)
  (at level 50, left associativity) : monad_scope.


(** ** Function definitions **)

(** When entering a function, we mark it using this function.
  This can then help to trace function definitions when debugging. **)

(** We rely on two OCaml hooks to effectively trace functions. **)
Definition add_stack_entering A (name : string) (cont : unit -> A) := cont tt.
Definition add_stack_leaving A (name : string) (cont : unit -> A) := cont tt.

(** The main function. **)
Definition add_stack (A : Type) fname : result A -> result A :=
  add_stack_entering fname (fun _ r =>
    add_stack_leaving fname (fun _ => fun S =>
      match r S with
      | result_success a S0 => result_success a S0
      | result_longjump n t S0 => result_longjump n t S0
      | result_error_stack stack s S0 =>
        result_error_stack (fname :: stack) s S0
      | result_impossible_stack stack s S0 =>
        result_impossible_stack (fname :: stack) s S0
      | result_not_implemented_stack stack s =>
        result_not_implemented_stack (fname :: stack) s
      | result_bottom S0 => result_bottom S0
      end)).

Notation "'add%stack' fname 'in' cont" :=
  (add_stack fname cont)
  (at level 50, left associativity) : monad_scope.

(** We also provide a specialised version to mark unimplemented functions. **)
Definition unimplemented_function (A : Type) fname : result A :=
  add%stack fname in
  result_not_implemented ("Function not implemented: " ++ fname ++ ".").
Arguments unimplemented_function [A].


(** ** [let]-monads **)

(** The monad for result.  This is a usual monadic binder. **)
Definition if_success (A B : Type) (r : result A) (f : A -> result B) : result B := fun S =>
  match r S with
  | result_success a S0 => f a S0
  | result_longjump n t S0 => result_longjump n t S0
  | result_error_stack stack s S0 => result_error_stack stack s S0
  | result_impossible_stack stack s S0 => result_impossible_stack stack s S0
  | result_not_implemented_stack stack s => result_not_implemented_stack stack s
  | result_bottom S0 => result_bottom S0
  end.

(** We provide the [let%success] notation.  It takes a result and evaluate it.
  Some tuple notations are accepted for convenience. **)
Notation "'let%success' a ':=' r 'in' cont" :=
  (if_success r (fun a => cont))
  (at level 50, left associativity) : monad_scope.

Notation "'let%success' '(' a1 ',' a2 ')' ':=' r 'in' cont" :=
  (let%success x := r in
   let (a1, a2) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%success' '(' a1 ',' a2 ',' a3 ')' ':=' r 'in' cont" :=
  (let%success x := r in
   let '(a1, a2, a3) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%success' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' r 'in' cont" :=
  (let%success x := r in
   let '(a1, a2, a3, a4) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' r 'in' cont" :=
  (let%success x := r in
   let '(a1, a2, a3, a4, a5) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' r 'in' cont" :=
  (let%success x := r in
   let '(a1, a2, a3, a4, a5, a6) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ',' a7 ')' ':=' r 'in' cont" :=
  (let%success x := r in
   let '(a1, a2, a3, a4, a5, a6, a7) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ',' a7 ',' a8 ')' ':=' r 'in' cont" :=
  (let%success x := r in
   let '(a1, a2, a3, a4, a5, a6, a7, a8) := x in cont)
  (at level 50, left associativity) : monad_scope.


(** Similar to [if_success], but option types.  Success is given when the
  option type is defined. **)
Definition if_defined_msg msg (A B : Type) (o : option A) (f : A -> result B) : result B :=
  match o with
  | Some x => f x
  | None =>
    let msg :=
      ifb msg = ""%string then ""%string else (" (" ++ msg ++ ")")%string in
    add%stack "if_defined" ++ msg in
    result_impossible "Undefined result."
  end.

Definition if_defined := if_defined_msg "".

Definition if_success_defined_msg msg (A B : Type) (o : state -> option A) (f : A -> result B) : result B :=
  get%state S in
  if_defined_msg msg (o S) f.

Definition if_success_defined := if_success_defined_msg "".

(** Similar to [let%success], the [let%defined] notation takes an option type.
  Some tuple notations also have been defined for convenience. **)
Notation "'let%defined' a ':=' o 'in' cont" :=
  (if_defined o (fun a => cont))
  (at level 50, left associativity) : monad_scope.

Notation "'let%defined' '(' a1 ',' a2 ')' ':=' o 'in' cont" :=
  (let%defined x := o in
   let (a1, a2) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%defined' '(' a1 ',' a2 ',' a3 ')' ':=' o 'in' cont" :=
  (let%defined x := o in
   let '(a1, a2, a3) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%defined' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' o 'in' cont" :=
  (let%defined x := o in
   let '(a1, a2, a3, a4) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%defined' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' o 'in' cont" :=
  (let%defined x := o in
   let '(a1, a2, a3, a4, a5) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%success%defined' a ':=' o 'in' cont" :=
  (if_success_defined o (fun a => cont))
  (at level 50, left associativity) : monad_scope.

Notation "'let%success%defined' '(' a1 ',' a2 ')' ':=' o 'in' cont" :=
  (let%success%defined x := o in
   let (a1, a2) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%success%defined' '(' a1 ',' a2 ',' a3 ')' ':=' o 'in' cont" :=
  (let%success%defined x := o in
   let '(a1, a2, a3) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%success%defined' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' o 'in' cont" :=
  (let%success%defined x := o in
   let '(a1, a2, a3, a4) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%success%defined' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' o 'in' cont" :=
  (let%success%defined x := o in
   let '(a1, a2, a3, a4, a5) := x in cont)
  (at level 50, left associativity) : monad_scope.

(** When more than one [let%defined] is defined in the same function,
  it can be frustrating not to know which it is.  We provide the [with "msg"]
  notation to add a message that will be printed when debugging if the
  [let%defined] failed (that is, it received [None]). **)
Notation "'let%defined' a ':=' o 'with' msg 'in' cont" :=
  (if_defined_msg msg o (fun a => cont))
  (at level 50, left associativity) : monad_scope.

Notation "'let%defined' '(' a1 ',' a2 ')' ':=' o 'with' msg 'in' cont" :=
  (let%defined x := o with msg in
   let (a1, a2) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%defined' '(' a1 ',' a2 ',' a3 ')' ':=' o 'with' msg 'in' cont" :=
  (let%defined x := o with msg in
   let '(a1, a2, a3) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%defined' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' o 'with' msg 'in' cont" :=
  (let%defined x := o with msg in
   let '(a1, a2, a3, a4) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%defined' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' o 'with' msg 'in' cont" :=
  (let%defined x := o with msg in
   let '(a1, a2, a3, a4, a5) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%success%defined' a ':=' o 'with' msg 'in' cont" :=
  (if_success_defined_msg msg o (fun a => cont))
  (at level 50, left associativity) : monad_scope.

Notation "'let%success%defined' '(' a1 ',' a2 ')' ':=' o 'with' msg 'in' cont" :=
  (let%success%defined x := o with msg in
   let (a1, a2) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%success%defined' '(' a1 ',' a2 ',' a3 ')' ':=' o 'with' msg 'in' cont" :=
  (let%success%defined x := o with msg in
   let '(a1, a2, a3) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%success%defined' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' o 'with' msg 'in' cont" :=
  (let%success%defined x := o with msg in
   let '(a1, a2, a3, a4) := x in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%success%defined' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' o 'with' msg 'in' cont" :=
  (let%success%defined x := o with msg in
   let '(a1, a2, a3, a4, a5) := x in cont)
  (at level 50, left associativity) : monad_scope.


(** Typical instantiations of the [let%defined] monadic binder is by
  calling the functions [write_SExp] and [read_SExp].  We provide the
  following notations for these two frequent cases. **)

(** The notation [write%defined p := p_] writes the object [p_] in the
  place given by the pointer [p]. **)
Notation "'write%defined' p ':=' p_ 'in' cont" :=
  (let%success%defined S := write_SExp p p_ with "write%defined" in set%state S in cont)
  (at level 50, left associativity) : monad_scope.

(** The notation [read%defined p_ := p] reads the object pointer by [p],
  giving it the name [p_]. **)
Notation "'read%defined' p_ ':=' p 'in' cont" :=
  (let%success%defined p_ := read_SExp p with "read%defined" in cont)
  (at level 50, left associativity) : monad_scope.

Definition let_alloc A p_ cont : result A :=
  get%state S in
  let (S, p) := alloc_SExp p_ S in
  set%state S in
  cont p.

(** Allocates a new memory cell. **)
Notation "'let%alloc' p ':=' p_ 'in' cont" :=
  (let_alloc p_ (fun p => cont))
  (at level 50, left associativity) : monad_scope.


(** ** Flow-control Monads **)

(** The monadic binder [run%success] is equivalent to [let%success],
  but doesn’t bind any new term.  This is practical when we only care
  of the side-effects of an imperative function, but not its result. **)
Notation "'run%success' c 'in' cont" :=
  (let%success _ := c in cont)
  (at level 50, left associativity) : monad_scope.

(** The result [result_skip] returns an arbitrary value which is not
  meant to be bound. **)
Definition result_skip : result unit :=
  result_success tt.

(** When a function returns (through the monad) a boolean, a common
  operation is to case-analysis on it.  This function provides this
  notation shortcut. **)
Definition if_then_else_success A (b : result bool) (c1 c2 : result A) :=
  let%success b := b in
  if b then c1 else c2.

Notation "'if%success' b 'then' c1 'else' c2" :=
  (if_then_else_success b c1 c2)
  (at level 50, left associativity) : monad_scope.

(** Sometimes (typically in the precense of side-effects), we don’t
  need an [else] clause.  This notation enables not to write it,
  assuming that the [then] clause returns a [result unit]. **)
Definition if_then_success A b c cont : result A :=
  run%success
    if%success b then c
    else result_skip in
  cont.

Notation "'if%success' b 'then' c 'in' cont" :=
  (if_then_success b c cont)
  (at level 50, left associativity) : monad_scope.

(** Sometimes, a monadic function returns an option type (of the
  overall type [result (option A)]).  This notation enables to
  pattern-match it while providing a binding for the matched
  returned value. **)
Definition if_option_defined A B (c : result (option A)) cont_then cont_else : result B :=
  let%success ans := c in
  match ans with
  | Some ans => cont_then ans
  | None => cont_else
  end.

Notation "'if%defined' ans ':=' c 'then' cont_then 'else' cont_else" :=
  (if_option_defined c (fun ans => cont_then) cont_else)
  (at level 50, left associativity) : monad_scope.


(** * Monads to View Objects Differently **)

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

Definition read_as_prim A (e : SEXP) cont : result A :=
  let%success%defined e_ := read_SExp e with "read_as_prim" in
  let%prim e_, e_prim := e_ in
  cont e_ e_prim.

Notation "'read%prim' e_ ',' e_prim ':=' e 'in' cont" :=
  (read_as_prim e (fun e_ e_prim => cont))
  (at level 50, left associativity) : monad_scope.


Definition read_as_sym A (e : SEXP) cont : result A :=
  let%success%defined e_ := read_SExp e with "read_as_sym" in
  let%sym e_, e_sym := e_ in
  cont e_ e_sym.

Notation "'read%sym' e_ ',' e_sym ':=' e 'in' cont" :=
  (read_as_sym e (fun e_ e_sym => cont))
  (at level 50, left associativity) : monad_scope.


Definition read_as_list A (e : SEXP) cont : result A :=
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

Definition read_as_list_all A (e : SEXP) cont : result A :=
  read%list e_, e_list := e in
  cont e_ (list_carval e_list) (list_cdrval e_list) (list_tagval e_list).

Notation "'read%list' e_ ',' e_car ',' e_cdr ',' e_tag ':=' e 'in' cont" :=
  (read_as_list_all e (fun e_ e_car e_cdr e_tag => cont))
    (at level 50, left associativity) : monad_scope.

Definition read_as_list_components A (e : SEXP) cont : result A :=
  read%list _, e_car, e_cdr, e_tag := e in
  cont e_car e_cdr e_tag.

Notation "'read%list' e_car ',' e_cdr ',' e_tag ':=' e 'in' cont" :=
  (read_as_list_components e (fun e_car e_cdr e_tag => cont))
  (at level 50, left associativity) : monad_scope.


Definition read_as_env A (e : SEXP) cont : result A :=
  let%success%defined e_ := read_SExp e with "read_as_env" in
  let%env e_, e_env := e_ in
  cont e_ e_env.

Notation "'read%env' e_ ',' e_env ':=' e 'in' cont" :=
  (read_as_env e (fun e_ e_env => cont))
  (at level 50, left associativity) : monad_scope.


Definition read_as_clo A (e : SEXP) cont : result A :=
  let%success%defined e_ := read_SExp e with "read_as_clo" in
  let%clo e_, e_clo := e_ in
  cont e_ e_clo.

Notation "'read%clo' e_ ',' e_clo ':=' e 'in' cont" :=
  (read_as_clo e (fun e_ e_clo => cont))
  (at level 50, left associativity) : monad_scope.


Definition read_as_prom A (e : SEXP) cont : result A :=
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

Definition read_as_VectorChar A (e : SEXP) cont : result A :=
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

Definition read_as_VectorLogical A (e : SEXP) cont : result A :=
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

Definition read_as_VectorInteger A (e : SEXP) cont : result A :=
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

Definition read_as_VectorReal A (e : SEXP) cont : result A :=
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

Definition read_as_VectorComplex A (e : SEXP) cont : result A :=
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

Definition read_as_VectorPointer A (e : SEXP) cont : result A :=
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

Definition write_nth_cell_VectorPointer A e n c cont : result A :=
  read%VectorPointer e_ := e in
  let%defined e_ := update_Vector_SExpRec_cell e_ n c with "write_nth_cell_VectorPointer" in
  write%defined e := SExpRec_VectorPointer e_ in
  cont.

Notation "'write%Pointer' e 'at' n ':=' c 'in' cont" :=
  (write_nth_cell_VectorPointer e n c cont)
  (at level 50, left associativity) : monad_scope.


(** * Other Monads **)

(** ** [map]-monads **)

(** Mapping on-place the content of a pointer is a frequent scheme.
  Here is a monad binder for it. **)
Definition map_pointer (A : Type) (map : SExpRec -> SExpRec) (p : SEXP) (cont : result A) : result A :=
  add%stack "map_pointer" in
  read%defined p_ := p in
  write%defined p := map p_ in
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

(** The following function enables to set the [attrib] field of
  objects from a pointer. **)
Notation "'set%attrib' p ':=' a 'in' cont" :=
  (map%pointer p with set_attrib a in cont)
  (at level 50, left associativity) : monad_scope.

(** The following function enables to set the [obj] field of
  objects from a pointer. **)
Notation "'set%obj' p ':=' o 'in' cont" :=
  (map%pointer p with set_obj o in cont)
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


(** Updating a list. **)
Definition map_list A f (p : SEXP) (cont : result A) : result A :=
  add%stack "map_list" in
  read%list p_, p_list := p in
  let p_ := {|
      NonVector_SExpRec_header := p_ ;
      NonVector_SExpRec_data := f p_list
    |} in
  write%defined p := p_ in
  cont.

Notation "'map%list' p 'with' map 'in' cont" :=
  (map_list map p cont)
  (at level 50, left associativity) : monad_scope.

(** Updating the first element (car) of a list. **)
Definition set_car A car (p : SEXP) (cont : result A) : result A :=
  add%stack "set_car" in
  map%list p with set_car_list car in cont.

Notation "'set%car' p ':=' car 'in' cont" :=
  (set_car car p cont)
  (at level 50, left associativity) : monad_scope.

(** Updating the tail (cdr) of a list. **)
Definition set_cdr A cdr (p : SEXP) (cont : result A) : result A :=
  add%stack "set_cdr" in
  map%list p with set_cdr_list cdr in cont.

Notation "'set%cdr' p ':=' cdr 'in' cont" :=
  (set_cdr cdr p cont)
  (at level 50, left associativity) : monad_scope.

(** Updating the tag of a list. **)
Definition set_tag A tag (p : SEXP) (cont : result A) : result A :=
  add%stack "set_tag" in
  map%list p with set_tag_list tag in cont.

Notation "'set%tag' p ':=' tag 'in' cont" :=
  (set_tag tag p cont)
  (at level 50, left associativity) : monad_scope.

