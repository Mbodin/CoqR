(** Monads.
* Provides some model for the C memory and some monads to manipulate it easily. **)

(** * A model for the C memory **)

Require Export Rinternals TLC.LibHeap Shared.
Require Import TLC.LibStream.

(** The global state of the C environment. In particular, it maps SEXP
  pointers to their corresponding expressions. **)
Record state := make_state {
    state_heap_SExp :> heap nat SExpRec ;
    state_fresh_locations : stream nat ;
    state_fresh_locations_fresh : forall n,
      ~ indom state_heap_SExp (LibStream.nth n state_fresh_locations) ;
    state_fresh_locations_different : forall n1 n2,
      n1 <> n2 ->
      LibStream.nth n1 state_fresh_locations <> LibStream.nth n2 state_fresh_locations
  }.

(** Allocate a new cell and provide it an initial value **)
Definition alloc_SExp (S : state) (e : SExpRec) : state * nat.
  refine (let p := stream_head (state_fresh_locations S) in ({|
      state_heap_SExp := write S p e ;
      state_fresh_locations := stream_tail (state_fresh_locations S) |},
    p)).
  - introv I. rewrite stream_tail_nth in I. forwards~ I': @indom_write_inv I.
    + unfolds p. rewrite stream_head_nth. applys* state_fresh_locations_different.
    + applys~ state_fresh_locations_fresh I'.
  - introv D. repeat rewrite stream_tail_nth. applys* state_fresh_locations_different.
Defined.

(** Writes a value in the state. Might return [None] if the cell is not already allocated. **)
Definition write_SExp (S : state) (p : nat) (e : SExpRec) : option state.
  refine (match read_option S p as r return _ = r -> _ with
          | None => fun _ => None
          | Some _ => fun Eq => Some {|
              state_heap_SExp := write S p e ;
              state_fresh_locations := state_fresh_locations S |}
          end eq_refl).
  - introv. apply not_indom_write.
    + introv E. applys state_fresh_locations_fresh. rewrite E.
      applys~ read_option_indom Eq.
    + applys~ state_fresh_locations_fresh.
  - apply* state_fresh_locations_different.
Defined.

(** Reads a value in the state. **)
Definition read_SExp (S : state) (p : SExpRec_pointer) :=
  match p with
  | None => None
  | Some p => read_option S p
  end.

Lemma alloc_SExp_read_SExp : forall S S' e p,
  alloc_SExp S e = (S', p) ->
  read_SExp S' (Some p) = Some e.
Proof. introv Eq. inverts Eq. simpl. rewrite~ read_option_write_same. Qed.

Lemma destruct_write_SExp_None : forall (S : state) p e,
  read_option S p = None ->
  write_SExp S p e = None.
Proof.
  introv E. unfolds.
  asserts: (forall T P (x : option T) (f1 : None = x -> P None) (f2 : forall v, Some v = x -> _) (H : None = x),
    match x as r return r = x -> P r with
    | None => f1
    | Some v => fun E => f2 v E
    end eq_refl =
    match H in _ = r return P r with
    | eq_refl => f1 H
    end).
  introv. destruct~ H.
  asserts: (forall T P (x : option T) (f1 : x = None -> P None) (f2 : forall v, x = Some v -> _) (H1 : x = None) (H2 : None = x),
    match x as r return x = r -> P r with
    | None => f1
    | Some v => fun E => f2 v E
    end eq_refl =
    match H2 in _ = r return P r with
    | eq_refl => f1 H1
    end).
  introv. destruct H2. clear. destruct H1. destruct (eq_sym H) eqn: Eq. clear. destruct H.
  forwards: TEMP (read_option S p). erewrite H.
  asserts: (forall T P (x : option T) (f1 : None = x -> P None) (f2 : forall v, Some v = x -> _) (H : None = x),
    match x as r return r = x -> P r with
    | None => f1
    | Some v => fun E => f2 v E
    end eq_refl =
    match H in _ = r return P r with
    | eq_refl => f1 H
    end).
   skip.
  forwards: TEMP (read_option S p). erewrite H.
  asserts: (forall (x : bool) (P : bool -> Type) (t : true = x -> P true) (f : false = x -> P false) (H : true = x),
     (if b as b' return b' = b -> P b'
      then t
      else f) eq_refl
     = match H in (_ = b') return P b' with
       | eq_refl => t H
       end).
  asserts: (forall (b : bool) (P : bool -> Type) (t : true = b -> P true) (f : false = b -> P false) (H : true = b),
     (if b as b' return b' = b -> P b'
      then t
      else f) eq_refl
     = match H in (_ = b') return P b' with
       | eq_refl => t H
       end).
  asserts: (forall T P (x : option T) (f1 : None = x -> P None) (f2 : forall v, Some v = x -> _) (H : x = None),
    match x as r return _ = r -> P r with
    | None => f1
    | Some v => f2 v
    end eq_refl =
    match H in _ = r return P r with
    | eq_refl => f1 H
    end).
                   
Qed.

Lemma destruct_write_SExp : forall S p e v,
  read_option S p = Some v ->
  exists S',
    write_SExp S p e = Some S'
    /\ S' = write S p e.

Lemma write_SExp_read_SExp_same : forall S S' e p,
  write_SExp S p e = Some S' ->
  read_SExp S' (Some p) = Some e.
Proof.
  introv. unfolds write_SExp. generalize (read_option S p). Eq. unfolds in Eq. destruct (read_option S p). inverts Eq.
Qed.

Lemma write_SExp_read_SExp : forall S S' e p p',
  write_SExp S p e = Some S' ->
  p <> p' ->
  read_SExp S' (Some p') = read_SExp S (Some p').
Proof.
Qed.

Lemma read_SExp_write_SExp : forall S e e' p,
  read_SExp S (Some p) = Some e ->
  exists S', write_SExp S p e' = Some S'.
Proof.
Qed.


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


