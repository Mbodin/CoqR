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
Require Export State Globals Result.


(** The monadic type is defined in the file Result.v. **)

Delimit Scope monad_scope with monad.
Open Scope monad_scope.


(** * Generic Monadic Binders **)

(** ** Manipulating the current state. **)

Definition get_state A (cont : state -> contextual A) : contextual A :=
  fun globals S => cont S globals S.

(** Getting the current state. **)
Notation "'get%state' S 'in' cont" :=
  (get_state (fun S => cont))
  (at level 50, left associativity) : monad_scope.

(** Replacing the current state by another one. **)
Definition set_state A S (cont : contextual A) : contextual A :=
  fun globals _ => cont globals S.

Notation "'set%state' S 'in' cont" :=
  (set_state S cont)
  (at level 50, left associativity) : monad_scope.

(** Update the state. **)
Definition map_state A (f : state -> state) (cont : contextual A) : contextual A :=
  get%state S in
  set%state f S in
  cont.

Notation "'map%state' S 'in' cont" :=
  (map_state S cont)
  (at level 50, left associativity) : monad_scope.

(** Extract a state componenent. **)
Definition read_state A B (f : state -> A) (cont : A -> contextual B) : contextual B :=
  get%state S in
  cont (f S).

Notation "'read%state' a ':=' f 'in' cont" :=
  (read_state f (fun a => cont))
  (at level 50, left associativity) : monad_scope.


(** ** The [contextual] monad **)

(** *** Coercions to and from [_SEXP] and [_bool] **)

Definition contextual_result A : contextual A -> result A :=
  fun e globals S => result_success (e globals S) globals S.

(** [_SEXP] can be built from [SEXP] or from any global variable.
  These coercions will be used all the time accross the formalisation. **)
Definition SEXP_SEXP : SEXP -> _SEXP := @contextual_ret _.
Definition GlobalVariable_SEXP : GlobalVariable -> _SEXP :=
  fun G globals _ => read_globals globals G.

Coercion SEXP_SEXP : SEXP >-> _SEXP.
Coercion GlobalVariable_SEXP : GlobalVariable >-> _SEXP.

(** Functions about [_bool]. **)

Definition bool_bool : bool -> _bool := @contextual_ret _.
Coercion bool_bool : bool >-> _bool.

(** Some types associated with coercions. **)
Definition result_SEXP := result SEXP.
Definition _SEXP_result_SEXP : _SEXP -> result_SEXP := @contextual_result _.
Coercion _SEXP_result_SEXP : _SEXP >-> result_SEXP.

Definition result_bool := result bool.
Definition _bool_result_bool : _bool -> result_bool := @contextual_result _.
Coercion _bool_result_bool : _bool >-> result_bool.

(** *** Booleans operators over [_bool]. **)

Definition contextual_and (a b : _bool) : _bool :=
  let%contextual a := a in
  let%contextual b := b in
  (a && b : _bool).

Infix "'&&" := contextual_and (at level 40, left associativity).

Lemma contextual_and_bool : forall a b : bool,
  a '&& b = a && b.
Proof. reflexivity. Qed.

Definition contextual_or (a b : _bool) : _bool :=
  let%contextual a := a in
  let%contextual b := b in
  (a || b : _bool).

Infix "'||" := contextual_or (at level 50, left associativity).

Lemma contextual_or_bool : forall a b : bool,
  a '|| b = a || b.
Proof. reflexivity. Qed.

Definition contextual_neg (b : _bool) : _bool :=
  let%contextual b := b in
  (negb b : _bool).

Notation "'~ b" := (contextual_neg b) (at level 35, right associativity).

Lemma contextual_neg_bool : forall b : bool,
  '~ b = negb b.
Proof. reflexivity. Qed.

Definition contextual_decide P `{Decidable P} : _bool := decide P.
Arguments contextual_decide P {_}.

Notation "''decide' P" := (contextual_decide P) (at level 70, no associativity).

Definition contextual_eq A `{Comparable A} (a b : contextual A) : _bool :=
  let%contextual a := a in
  let%contextual b := b in
  'decide (a = b).

Definition contextual_eq_SEXP : _SEXP -> _SEXP -> _bool := @contextual_eq _ _.

Infix "'==" := contextual_eq_SEXP (at level 70, no associativity).

Notation "a '!= b" := ('~ (a '== b)) (at level 70, no associativity).

Notation "'ifc' b 'then' v1 'else' v2" :=
  (let%contextual x := b in if x then v1 else v2)
  (at level 200, right associativity) : type_scope.


(** This monadic binder enables to fetch a contextual value. **)
Definition get_contextual A B (e : contextual A) (cont : A -> contextual B) : contextual B :=
  fun globals S => cont (e globals S) globals S.

Notation "'let%fetch' a 'in' cont" :=
  (get_contextual a (fun a => cont))
  (at level 50, left associativity) : monad_scope.


(** Functions delaying contextual elements. **)

Definition contextual_pair A B (p : contextual A * contextual B) : contextual (A * B) :=
  let (a, b) := p in
  let%fetch a in
  let%fetch b in
  contextual_ret (a, b).

Definition contextual_left A B (p : contextual A * B) : contextual (A * B) :=
  let (a, b) := p in
  contextual_pair (a, contextual_ret b).

Definition contextual_right A B (p : A * contextual B) : contextual (A * B) :=
  let (a, b) := p in
  contextual_pair (contextual_ret a, b).

Definition contextual_list A : list (contextual A) -> contextual (list A) :=
  fold_left (fun a l =>
    let%fetch a in
    let%fetch l in
    contextual_ret (a :: l)) (contextual_ret nil).

Definition contextual_tuple2 := contextual_pair.
Definition contextual_tuple3 A B C (p : contextual A * contextual B * contextual C)
    : contextual (A * B * C) :=
  contextual_pair (contextual_pair (fst p), snd p).
Definition contextual_tuple4 A B C D (p : contextual A * contextual B * contextual C * contextual D)
    : contextual (A * B * C * D) :=
  contextual_pair (contextual_tuple3 (fst p), snd p).
Definition contextual_tuple5 A B C D E
    (p : contextual A * contextual B * contextual C * contextual D * contextual E)
    : contextual (A * B * C * D * E) :=
  contextual_pair (contextual_tuple4 (fst p), snd p).
Definition contextual_tuple6 A B C D E F
    (p : contextual A * contextual B * contextual C * contextual D * contextual E * contextual F)
    : contextual (A * B * C * D * E * F) :=
  contextual_pair (contextual_tuple5 (fst p), snd p).


(** ** Manipulating global variables. **)

Definition get_globals A (cont : Globals -> contextual A) : contextual A :=
  fun globals => cont globals globals.

(** Getting the current state of global variables. **)
Notation "'get%globals' S 'in' cont" :=
  (get_globals (fun S => cont))
  (at level 50, left associativity) : monad_scope.

(** Replacing the current state of global variables by another one.
  Note that the globals are not in the state of the monad: this does
	not propagate through the [run%success] commands.
  This monadic binder is only used in Rinit.v, where we actually have
	to define the global variables. **)
Definition set_globals A globals (cont : contextual A) : contextual A :=
  fun _ => cont globals.

Notation "'set%globals' globals 'in' cont" :=
  (set_globals globals cont)
  (at level 50, left associativity) : monad_scope.

Definition map_globals A f (cont : contextual A) : contextual A :=
  get%globals globals in
  set%globals f globals in
  cont.

Notation "'map%globals' f 'in' cont" :=
  (map_globals f cont)
  (at level 50, left associativity) : monad_scope.

(** Writing in the current state of global variables. **)
Definition write_globals A C (p : _SEXP) (cont : contextual A) : contextual A :=
  let%fetch p in
  map%globals fun globals => {{ globals with C := p }} in
  cont.

Notation "'write%globals' C ':=' p 'in' cont" :=
  (write_globals C p cont)
  (at level 50, left associativity) : monad_scope.

Definition write_globals_list A (L : list (_ * _SEXP)) (cont : contextual A) : contextual A :=
  let%contextual L := contextual_list (map (@contextual_right _ _) L) in
  map%globals fun globals => {{ globals with L }} in
  cont.

Notation "'write%globals' L 'in' cont" :=
  (write_globals_list L cont)
  (at level 50, left associativity) : monad_scope.


(** ** Function definitions **)

(** When entering a function, we mark it using this function.
  This can then help to trace function definitions when debugging. **)

(** We rely on two OCaml hooks to effectively trace functions.
  By default, these functions do nothing. **)
Definition add_stack_entering A (name : string) (cont : unit -> A) := cont tt.
Definition add_stack_leaving A (name : string) (cont : unit -> A) := cont tt.

(** This function is called at the beginning of any R function, and adds
  the given function name to the stack. **)
Definition add_stack (A : Type) fname : result A -> result A :=
  add_stack_entering fname (fun _ r =>
    add_stack_leaving fname (fun _ globals S =>
      match r globals S with
      | rresult_success a S0 => rresult_success a S0
      | rresult_longjump n t S0 => rresult_longjump n t S0
      | rresult_error_stack stack s S0 =>
        rresult_error_stack (fname :: stack) s S0
      | rresult_impossible_stack stack s S0 =>
        rresult_impossible_stack (fname :: stack) s S0
      | rresult_not_implemented_stack stack s =>
        rresult_not_implemented_stack (fname :: stack) s
      | rresult_bottom S0 => rresult_bottom S0
      end)).

Notation "'add%stack' fname 'in' cont" :=
  (add_stack fname cont)
  (at level 50, left associativity) : monad_scope.

(** We also provide a specialised version to mark unimplemented functions. **)
Definition unimplemented_function (A : Type) fname : result A :=
  add%stack fname in
  result_not_implemented ("Function not implemented: " ++ fname ++ ".").
Arguments unimplemented_function [A].


(** ** [let]-monadic-binders **)

(** The usual monadic binder for result. **)
Definition if_success (A B : Type) (r : result A) (f : A -> result B) : result B :=
  fun globals S =>
    match r globals S with
    | rresult_success a S0 => f a globals S0
    | rresult_longjump n t S0 => rresult_longjump n t S0
    | rresult_error_stack stack s S0 => rresult_error_stack stack s S0
    | rresult_impossible_stack stack s S0 => rresult_impossible_stack stack s S0
    | rresult_not_implemented_stack stack s => rresult_not_implemented_stack stack s
    | rresult_bottom S0 => rresult_bottom S0
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
  read%state v := o in
  if_defined_msg msg v f.

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

Definition write_defined A (p : _SEXP) p_ (cont : result A) :=
  let%fetch p in
  let%success%defined S := write_SExp p p_ with "write%defined" in
  set%state S in
  cont.

(** The notation [write%defined p := p_] writes the object [p_] in the
  place given by the pointer [p]. **)
Notation "'write%defined' p ':=' p_ 'in' cont" :=
  (write_defined p p_ cont)
  (at level 50, left associativity) : monad_scope.

Definition write_defined_contextual A p p_ (cont : result A) :=
  let%fetch p_ in
  write%defined p := p_ in
  cont.

Notation "'write%defined%contextual' p ':=' p_ 'in' cont" :=
  (write_defined_contextual p p_ cont)
  (at level 50, left associativity) : monad_scope.

Definition read_defined A (p : _SEXP) (cont : SExpRec -> result A) :=
  let%fetch p in
  let%success%defined p_ := read_SExp p with "read%defined" in
  cont p_.

(** The notation [read%defined p_ := p] reads the object pointer by [p],
  giving it the name [p_]. **)
Notation "'read%defined' p_ ':=' p 'in' cont" :=
  (read_defined p (fun p_ => cont))
  (at level 50, left associativity) : monad_scope.

Definition let_alloc A p_ cont : contextual A :=
  get%state S in
  let (S, p) := alloc_SExp p_ S in
  set%state S in
  cont p.

(** Allocates a new memory cell. **)
Notation "'let%alloc' p ':=' p_ 'in' cont" :=
  (let_alloc p_ (fun p => cont))
  (at level 50, left associativity) : monad_scope.

Definition let_alloc_contextual A p_ cont : contextual A :=
  let%fetch p_ in
  let%alloc p := p_ in
  cont p.

Notation "'let%alloc%contextual' p ':=' p_ 'in' cont" :=
  (let_alloc_contextual p_ (fun p => cont))
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
  operation is to case-analysis on it.
  This function provides a notation shortcut. **)
Definition if_then_else_success A (b : result bool) c1 c2 : result A :=
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

(** Similarly to [if_then_else_success] and [if_then_success], but on
  the [contextual] monad. **)

Definition if_then_else_contextual A (b : _bool) c1 c2 : result A :=
  if%success contextual_result b then c1 else c2.

Notation "'if%contextual' b 'then' c1 'else' c2" :=
  (if_then_else_contextual b c1 c2)
  (at level 50, left associativity) : monad_scope.

Definition if_then_contextual A (b : _bool) c cont : result A :=
  if%success contextual_result b then c in cont.

Notation "'if%contextual' b 'then' c 'in' cont" :=
  (if_then_contextual b c cont)
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

