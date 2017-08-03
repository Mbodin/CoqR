(** Monads.
 * Provides monads to manipulate R objects easily. **)

Set Implicit Arguments.
Require Export State.


(** * Monadic Type **)

(** A monad type for results. **)
Inductive result (A : Type) :=
  | result_success : state -> A -> result A (** The program terminated in this state with this result. **)
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
 * this case (for instance by writting [e->type] without checking whether
 * [e] actually maps to a valid expression), the Coq interpreter will
 * return [result_impossible]. **)


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

(** As for [if_success], but from an option type. We suppose that the option type is defined. **)
Definition if_defined (A B : Type) S (o : option A) (f : A -> result B) : result B :=
  match o with
  | Some x => f x
  | None => result_impossible S "[if_defined] got an undefined result."
  end.

(** Mapping onplace the content of a pointer is a frequent scheme.
 * Here is a monad for it. **)
Definition map_pointer (A : Type) S (map : SExpRec -> SExpRec) (p : SExpRec_pointer)
    (f : state -> result A) : result A :=
  if_defined S (read_SExp S p) (fun p_ =>
    if_defined S (write_SExp S p (map p_)) f).

(** Updating a list. **)
Definition map_list A S f (p : SExpRec_pointer) (cont : state -> result A) : result A :=
  if_defined S (read_SExp S p) (fun p_ =>
    if_defined S (get_NonVector p_) (fun p_ =>
      if_defined S (get_listSxp p_) (fun p_list =>
        let p_list := f p_list in
        let p_ := {|
            NonVector_SExpRec_header := p_ ;
            NonVector_SExpRec_data := p_list
          |} in
        if_defined S (write_SExp S p p_) cont))).

(** Updating the first element of a list. **)
Definition set_car A S car (p : SExpRec_pointer) (f : state -> result A) : result A :=
  map_list S (set_car_list car) p f.

(** Updating the tail of a list. **)
Definition set_cdr A S cdr (p : SExpRec_pointer) (f : state -> result A) : result A :=
  map_list S (set_cdr_list cdr) p f.

(** Updating the tag of a list. **)
Definition set_tag A S tag (p : SExpRec_pointer) (f : state -> result A) : result A :=
  map_list S (set_tag_list tag) p f.


(** * Monads to View Basic Language Elements Differently **)

Definition if_is_sym A S (e_ : SExpRec) (f : NonVector_SExpRec -> SymSxp_struct -> result A) : result A :=
  if_defined S (get_NonVector e_) (fun e_ =>
    if_defined S (get_symSxp e_) (fun e_sym =>
      f e_ e_sym)).

Definition if_is_list A S (e_ : SExpRec) (f : NonVector_SExpRec -> ListSxp_struct -> result A) : result A :=
  if_defined S (get_NonVector e_) (fun e_ =>
    if_defined S (get_listSxp e_) (fun e_list =>
      f e_ e_list)).

Definition if_is_clo A S (e_ : SExpRec) (f : NonVector_SExpRec -> CloSxp_struct -> result A) : result A :=
  if_defined S (get_NonVector e_) (fun e_ =>
    if_defined S (get_cloSxp e_) (fun e_clo =>
      f e_ e_clo)).

Definition if_is_env A S (e_ : SExpRec) (f : NonVector_SExpRec -> EnvSxp_struct -> result A) : result A :=
  if_defined S (get_NonVector e_) (fun e_ =>
    if_defined S (get_envSxp e_) (fun e_env =>
      f e_ e_env)).

Definition if_is_prim A S (e_ : SExpRec) (f : NonVector_SExpRec -> PrimSxp_struct -> result A) : result A :=
  if_defined S (get_NonVector e_) (fun e_ =>
    if_defined S (get_primSxp e_) (fun e_prim =>
      f e_ e_prim)).

Definition if_is_prom A S (e_ : SExpRec) (f : NonVector_SExpRec -> PromSxp_struct -> result A) : result A :=
  if_defined S (get_NonVector e_) (fun e_ =>
    if_defined S (get_promSxp e_) (fun e_prom =>
      f e_ e_prom)).


Definition read_as_sym A S (e : SExpRec_pointer) f : result A :=
  if_defined S (read_SExp S e) (fun e_ =>
    if_is_sym S e_ f).

Definition read_as_list A S (e : SExpRec_pointer) f : result A :=
  if_defined S (read_SExp S e) (fun e_ =>
    if_is_list S e_ f).

Definition read_as_clo A S (e : SExpRec_pointer) f : result A :=
  if_defined S (read_SExp S e) (fun e_ =>
    if_is_clo S e_ f).

Definition read_as_env A S (e : SExpRec_pointer) f : result A :=
  if_defined S (read_SExp S e) (fun e_ =>
    if_is_env S e_ f).

Definition read_as_prim A S (e : SExpRec_pointer) f : result A :=
  if_defined S (read_SExp S e) (fun e_ =>
    if_is_prim S e_ f).

Definition read_as_prom A S (e : SExpRec_pointer) f : result A :=
  if_defined S (read_SExp S e) (fun e_ =>
    if_is_prom S e_ f).

Definition read_as_VectorChar A S (e : SExpRec_pointer) f : result A :=
  if_defined S (read_SExp S e) (fun e_ =>
    if_defined S (get_VectorChar e_) f).

Definition read_as_VectorLogical A S (e : SExpRec_pointer) f : result A :=
  if_defined S (read_SExp S e) (fun e_ =>
    if_defined S (get_VectorLogical e_) f).

Definition read_as_VectorInteger A S (e : SExpRec_pointer) f : result A :=
  if_defined S (read_SExp S e) (fun e_ =>
    if_defined S (get_VectorInteger e_) f).

Definition read_as_VectorComplex A S (e : SExpRec_pointer) f : result A :=
  if_defined S (read_SExp S e) (fun e_ =>
    if_defined S (get_VectorComplex e_) f).

Definition read_as_VectorReal A S (e : SExpRec_pointer) f : result A :=
  if_defined S (read_SExp S e) (fun e_ =>
    if_defined S (get_VectorReal e_) f).

Definition read_as_VectorPointers A S (e : SExpRec_pointer) f : result A :=
  if_defined S (read_SExp S e) (fun e_ =>
    if_defined S (get_VectorPointers e_) f).

