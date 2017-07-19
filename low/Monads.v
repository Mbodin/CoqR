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
  refine (match read_option S p as r return r = _ -> _ with
          | None => fun _ => None
          | Some _ => fun Eq => Some {|
              state_heap_SExp := write S p e ;
              state_fresh_locations := state_fresh_locations S |}
          end eq_refl).
  - introv. apply not_indom_write.
    + introv E. applys state_fresh_locations_fresh. rewrite E.
      symmetry in Eq. applys~ read_option_indom Eq.
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
  asserts R: (forall T P (x : option T) (f1 : None = x -> P None) (f2 : forall v, Some v = x -> _)
      (H : None = x),
    match x as r return r = x -> P r with
    | None => f1
    | Some v => fun E => f2 v E
    end eq_refl
    = match H in _ = r return P r with
      | eq_refl => f1 H
      end).
  + clear. introv. destruct~ H.
  + symmetry in E. lets R': (rm R) (read_option S p). erewrite (R' _ _ E). destruct~ E.
Qed.

Lemma destruct_write_SExp : forall (S : state) p e v,
  read_option S p = Some v ->
  exists S',
    write_SExp S p e = Some S'
    /\ (S' : heap _ _) = write S p e.
Proof.
  introv E. unfolds write_SExp.
  asserts R: (forall T T' (x : option T) (f1 : None = x -> T') (f2 : forall v, Some v = x -> T')
      v (H : Some v = x),
    match x as r return r = x -> T' with
    | None => f1
    | Some v => fun E => f2 v E
    end eq_refl
    = f2 v H).
  + clear. introv. destruct~ H.
  + symmetry in E. lets R': (rm R) (read_option S p). rewrite (R' _ _ _ E). clear.
    eexists. splits~.
Qed.

Lemma write_SExp_read_SExp_same : forall S S' e p,
  write_SExp S p e = Some S' ->
  read_SExp S' (Some p) = Some e.
Proof.
  introv E. simpl. destruct (read_option S p) eqn: E'.
  + forwards (S2&E1&E2): destruct_write_SExp E'.
    rewrite E in E1. inverts E1. rewrite E2. rewrite~ read_option_write_same.
  + forwards Eq: destruct_write_SExp_None E'. rewrite Eq in E. false*.
Qed.

Lemma write_SExp_read_SExp : forall S S' e p p',
  write_SExp S p e = Some S' ->
  p <> p' ->
  read_SExp S' (Some p') = read_SExp S (Some p').
Proof.
  introv E D. simpl. destruct (read_option S p) eqn: E'.
  + forwards (S2&E1&E2): destruct_write_SExp E'.
    rewrite E in E1. inverts E1. rewrite E2. rewrite~ read_option_write.
  + forwards Eq: destruct_write_SExp_None E'. rewrite Eq in E. false*.
Qed.

Lemma read_SExp_write_SExp : forall S e e' p,
  read_SExp S (Some p) = Some e ->
  exists S', write_SExp S p e' = Some S'.
Proof.
  introv E. simpl in E. forwards (S'&E1&E2): destruct_write_SExp E.
  exists S'. rewrite~ E1.
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
  | Some (S0, x) => f S0 x
  end.


