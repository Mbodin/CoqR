(** Monads.
* Provides some model for the C memory and some monads to manipulate it easily. **)

(** * A model for the C memory **)

(** The global state of the C environment. In particular, it maps SEXP
  pointers to their corresponding expressions. **)
Record state := make_state {
    heap_SExp :> nat -> option SExprRec ;
    free_pointer : nat ;
    free_pointer_free : forall p, p > free_pointer -> heap_SExp p = None
  }.

(** Allocate a new cell and provide it an initial value **)
Definition alloc_SExp (S : state) e :=
  let p := free_pointer S in
  { S with heap_SExp free_pointer := S free_pointer, p' := If p = p' then Some e else S p' }

(** Writes a value in the state. Might return [None] if the cell is not already allocated. **)
Definition write_SExp (S : state) p e :=
  match S p with
  | None => None
  | Some _ =>
    Some { S with heap_SExp p' := If p = p' then Some e else S p' }
  end.

Definition read_SExp (S : state) (p : SExpRec_pointer) :=
  match p with
  | None => None
  | Some p => S p
  end.


(** * Monads **)

(* TODO: Define JSCest’s style out type. *)

Definition if_defined (A B : Type) (o : option A) (f : A -> option B) : option B :=
  match o with
  | None => None
  | Some x => f x
  end.

Definition if_returns (A B : Type) (o : option (state * A)) (f : state -> A -> option B) : option B :=
  match o with
  | None => None
  | Some (S, x) => f S x
  end.


