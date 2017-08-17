(** Monads.
 * Provides monads to manipulate R objects easily. **)

Set Implicit Arguments.
Require Export State.


(** * Monadic Type **)

(** A monad type for results. **)
Inductive result (A : Type) :=
  | result_success : state -> A -> result A (** The program terminated in this state using this result. **)
  | result_error : state -> string -> result A (** The program resulted in the following error (not meant to be caught). **)
  | result_impossible : state -> string -> result A (** This result should never happen. We provide a string to help debugging. **)
  | result_not_implemented : string -> result A (** This result relies on a feature not yet implemented. **)
  | result_bottom : state -> result A (** We are out of fuel to compute anything. **)
  .
Arguments result_error [A].
Arguments result_impossible [A].
Arguments result_not_implemented [A].
Arguments result_bottom [A].

(** A precision about [result_not_implemented] and [result_error]:
 * if the C source code of R throw a not-implemented error, we consider
 * this as an error thrown in the original interpreter and use the
 * constructor [result_error].
 * We only throw [result_not_implemented] when our Coq code has not
 * implemented a behaviour of R. **)
(** The difference between [result_error] and [result_impossible] is
 * that [result_error] is thrown when the R interpreter throws an error
 * (usally using the [error] C function), and [result_impossible] is
 * thrown when R does not throw an error, but we know for sure that such
 * a case can never happen. Typically because the C program accepts an
 * impossible case to be missing, but that Coq does not recognise this
 * case to be impossible. So if there is a possible case in which Coq
 * must return something, but that the R interpreter in C does not cover
 * this case (for instance by writting [e->type] usingout checking whether
 * [e] actually maps to a valid expression), the Coq interpreter will
 * return [result_impossible]. **)

Delimit Scope monad_scope with monad.
Open Scope monad_scope.


(** * Generic Monads **)

(** The monad for result. **)
Definition if_success (A B : Type) (r : result A) (f : state -> A -> result B) : result B :=
  match r with
  | result_success S0 a => f S0 a
  | result_error S0 s => result_error S0 s
  | result_impossible S0 s => result_impossible S0 s
  | result_not_implemented s => result_not_implemented s
  | result_bottom S0 => result_bottom S0
  end.

Notation "'let%success' a ':=' r 'using' S 'in' cont" :=
  (if_success r (fun S a => cont))
  (at level 50, left associativity) : monad_scope.

Notation "'let%success' '(' a1 ',' a2 ')' ':=' r 'using' S 'in' cont" :=
  (let%success x := r using S in
   let '(a1, a2) := x in cont)
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


(** As for [if_success], but from an option type. We suppose that the option type is defined. **)
Definition if_defined (A B : Type) S (o : option A) (f : A -> result B) : result B :=
  match o with
  | Some x => f x
  | None => result_impossible S "[if_defined] got an undefined result."
  end.

Notation "'let%defined' a ':=' o 'using' S 'in' cont" :=
  (if_defined S o (fun a => cont))
  (at level 50, left associativity) : monad_scope.

Notation "'write%defined' p ':=' p_ 'using' S 'in' cont" :=
  (let%defined S := write_SExp S p p_ using S in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'read%defined' p_ ':=' p 'using' S 'in' cont" :=
  (let%defined p_ := read_SExp S p using S in cont)
  (at level 50, left associativity) : monad_scope.


(** Mapping onplace the content of a pointer is a frequent scheme.
 * Here is a monad for it. **)
Definition map_pointer (A : Type) S (map : SExpRec -> SExpRec) (p : SExpRec_pointer)
    (f : state -> result A) : result A :=
  let%defined p_ := read_SExp S p using S in
  write%defined p := map p_ using S in
  f S.

Notation "'map%pointer' p 'with' map 'using' S 'in' cont" :=
  (map_pointer S map p (fun S => cont))
  (at level 50, left associativity) : monad_scope.

Notation "'map%gp' p 'with' f 'using' S 'in' cont" :=
  (map%pointer p with map_gp f using S in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'set%gp' p 'with' v 'using' S 'in' cont" :=
  (map%pointer p with set_gp v using S in cont)
  (at level 50, left associativity) : monad_scope.


(** Updating a list. **)
Definition map_list A S f (p : SExpRec_pointer) (cont : state -> result A) : result A :=
  let%defined p_ := read_SExp S p using S in
  let%defined p_ := get_NonVector p_ using S in
  let%defined p_list := get_listSxp p_ using S in
  let p_list := f p_list in
  let p_ := {|
      NonVector_SExpRec_header := p_ ;
      NonVector_SExpRec_data := p_list
    |} in
  write%defined p := p_ using S in
  cont S.

Notation "'map%list' p 'with' map 'using' S 'in' cont" :=
  (map_list S map p (fun S => cont))
  (at level 50, left associativity) : monad_scope.

(** Updating the first element of a list. **)
Definition set_car A S car (p : SExpRec_pointer) (f : state -> result A) : result A :=
  map%list p with set_car_list car using S in f S.

Notation "'set%car' p ':=' car 'using' S 'in' cont" :=
  (set_car S car p (fun S => cont))
  (at level 50, left associativity) : monad_scope.

(** Updating the tail of a list. **)
Definition set_cdr A S cdr (p : SExpRec_pointer) (f : state -> result A) : result A :=
  map%list p with set_cdr_list cdr using S in f S.

Notation "'set%cdr' p ':=' cdr 'using' S 'in' cont" :=
  (set_cdr S cdr p (fun S => cont))
  (at level 50, left associativity) : monad_scope.

(** Updating the tag of a list. **)
Definition set_tag A S tag (p : SExpRec_pointer) (f : state -> result A) : result A :=
  map%list p with set_tag_list tag using S in f S.

Notation "'set%tag' p ':=' tag 'using' S 'in' cont" :=
  (set_car S tag p (fun S => cont))
  (at level 50, left associativity) : monad_scope.


(** * Monads to View Basic Language Elements Differently **)

Definition if_is_sym A S (e_ : SExpRec) (f : NonVector_SExpRec -> SymSxp_struct -> result A) : result A :=
  let%defined e_ := get_NonVector e_ using S in
  let%defined e_sym := get_symSxp e_ using S in
  f e_ e_sym.

Notation "'let%sym' a_ ',' a_sym ':=' e_ 'using' S 'in' cont" :=
  (if_is_sym S e_ (fun a_ a_sym => cont))
  (at level 50, left associativity) : monad_scope.

Definition if_is_list A S (e_ : SExpRec) (f : NonVector_SExpRec -> ListSxp_struct -> result A) : result A :=
  let%defined e_ := get_NonVector e_ using S in
  let%defined e_list := get_listSxp e_ using S in
  f e_ e_list.

Notation "'let%list' a_ ',' a_list ':=' e_ 'using' S 'in' cont" :=
  (if_is_list S e_ (fun a_ a_list => cont))
  (at level 50, left associativity) : monad_scope.

Definition if_is_clo A S (e_ : SExpRec) (f : NonVector_SExpRec -> CloSxp_struct -> result A) : result A :=
  let%defined e_ := get_NonVector e_ using S in
  let%defined e_clo := get_cloSxp e_ using S in
  f e_ e_clo.

Notation "'let%clo' a_ ',' a_clo ':=' e_ 'using' S 'in' cont" :=
  (if_is_clo S e_ (fun a_ a_clo => cont))
  (at level 50, left associativity) : monad_scope.

Definition if_is_env A S (e_ : SExpRec) (f : NonVector_SExpRec -> EnvSxp_struct -> result A) : result A :=
  let%defined e_ := get_NonVector e_ using S in
  let%defined e_env := get_envSxp e_ using S in
  f e_ e_env.

Notation "'let%env' a_ ',' a_env ':=' e_ 'using' S 'in' cont" :=
  (if_is_env S e_ (fun a_ a_env => cont))
  (at level 50, left associativity) : monad_scope.

Definition if_is_prim A S (e_ : SExpRec) (f : NonVector_SExpRec -> PrimSxp_struct -> result A) : result A :=
  let%defined e_ := get_NonVector e_ using S in
  let%defined e_prim := get_primSxp e_ using S in
  f e_ e_prim.

Notation "'let%prim' a_ ',' a_prim ':=' e_ 'using' S 'in' cont" :=
  (if_is_prim S e_ (fun a_ a_prim => cont))
  (at level 50, left associativity) : monad_scope.

Definition if_is_prom A S (e_ : SExpRec) (f : NonVector_SExpRec -> PromSxp_struct -> result A) : result A :=
  let%defined e_ := get_NonVector e_ using S in
  let%defined e_prom := get_promSxp e_ using S in
  f e_ e_prom.

Notation "'let%prom' a_ ',' a_prom ':=' e_ 'using' S 'in' cont" :=
  (if_is_prom S e_ (fun a_ a_prom => cont))
  (at level 50, left associativity) : monad_scope.


Definition read_as_sym A S (e : SExpRec_pointer) f : result A :=
  let%defined e_ := read_SExp S e using S in
  let%sym e_, e_sym := e_ using S in
  f e_ e_sym.

Notation "'read%sym' e_ ',' e_sym ':=' e 'using' S 'in' cont" :=
  (read_as_sym S e (fun e_ e_sym => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_as_list A S (e : SExpRec_pointer) f : result A :=
  let%defined e_ := read_SExp S e using S in
  let%list e_, e_list := e_ using S in
  f e_ e_list.

Notation "'read%list' e_ ',' e_list ':=' e 'using' S 'in' cont" :=
  (read_as_list S e (fun e_ e_list => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_as_clo A S (e : SExpRec_pointer) f : result A :=
  let%defined e_ := read_SExp S e using S in
  let%clo e_, e_clo := e_ using S in
  f e_ e_clo.

Notation "'read%clo' e_ ',' e_clo ':=' e 'using' S 'in' cont" :=
  (read_as_clo S e (fun e_ e_clo => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_as_env A S (e : SExpRec_pointer) f : result A :=
  let%defined e_ := read_SExp S e using S in
  let%env e_, e_env := e_ using S in
  f e_ e_env.

Notation "'read%env' e_ ',' e_env ':=' e 'using' S 'in' cont" :=
  (read_as_env S e (fun e_ e_env => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_as_prim A S (e : SExpRec_pointer) f : result A :=
  let%defined e_ := read_SExp S e using S in
  let%prim e_, e_prim := e_ using S in
  f e_ e_prim.

Notation "'read%prim' e_ ',' e_prim ':=' e 'using' S 'in' cont" :=
  (read_as_prim S e (fun e_ e_prim => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_as_prom A S (e : SExpRec_pointer) f : result A :=
  let%defined e_ := read_SExp S e using S in
  let%prom e_, e_prom := e_ using S in
  f e_ e_prom.

Notation "'read%prom' e_ ',' e_prom ':=' e 'using' S 'in' cont" :=
  (read_as_prom S e (fun e_ e_prom => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_as_VectorChar A S (e : SExpRec_pointer) f : result A :=
  let%defined e_ := read_SExp S e using S in
  let%defined e_ := get_VectorChar e_ using S in
  f e_.

Notation "'read%VectorChar' e_ ':=' e 'using' S 'in' cont" :=
  (read_as_VectorChar S e (fun e_ => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_as_VectorLogical A S (e : SExpRec_pointer) f : result A :=
  let%defined e_ := read_SExp S e using S in
  let%defined e_ := get_VectorLogical e_ using S in
  f e_.

Notation "'read%VectorLogical' e_ ':=' e 'using' S 'in' cont" :=
  (read_as_VectorLogical S e (fun e_ => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_as_VectorInteger A S (e : SExpRec_pointer) f : result A :=
  let%defined e_ := read_SExp S e using S in
  let%defined e_ := get_VectorInteger e_ using S in
  f e_.

Notation "'read%VectorInteger' e_ ':=' e 'using' S 'in' cont" :=
  (read_as_VectorInteger S e (fun e_ => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_as_VectorComplex A S (e : SExpRec_pointer) f : result A :=
  let%defined e_ := read_SExp S e using S in
  let%defined e_ := get_VectorComplex e_ using S in
  f e_.

Notation "'read%VectorComplex' e_ ':=' e 'using' S 'in' cont" :=
  (read_as_VectorComplex S e (fun e_ => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_as_VectorReal A S (e : SExpRec_pointer) f : result A :=
  let%defined e_ := read_SExp S e using S in
  let%defined e_ := get_VectorReal e_ using S in
  f e_.

Notation "'read%VectorReal' e_ ':=' e 'using' S 'in' cont" :=
  (read_as_VectorReal S e (fun e_ => cont))
  (at level 50, left associativity) : monad_scope.

Definition read_as_VectorPointers A S (e : SExpRec_pointer) f : result A :=
  let%defined e_ := read_SExp S e using S in
  let%defined e_ := get_VectorPointers e_ using S in
  f e_.

Notation "'read%VectorPointers' e_ ':=' e 'using' S 'in' cont" :=
  (read_as_VectorPointers S e (fun e_ => cont))
  (at level 50, left associativity) : monad_scope.


