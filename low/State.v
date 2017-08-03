(** Monads.
 * Provides a model for the C memory, as well as most R global variables. **)

Set Implicit Arguments.
Require Export String.
Require Export RinternalsAux TLC.LibHeap Shared.
Require Import TLC.LibStream.


(** * A Model for the C Memory **)

(** The global state of the C memory. In particular, it maps SEXP
 * pointers to their corresponding expressions. **)
Record memory := make_memory {
    state_heap_SExp :> heap nat SExpRec ;
    state_fresh_locations : stream nat ;
    state_fresh_locations_fresh : forall n,
      ~ indom state_heap_SExp (LibStream.nth n state_fresh_locations) ;
    state_fresh_locations_different : forall n1 n2,
      n1 <> n2 ->
      LibStream.nth n1 state_fresh_locations <> LibStream.nth n2 state_fresh_locations
  }.

(** Allocate a new cell and provide it an initial value **)
Definition alloc_memory_SExp_nat (S : memory) (e_ : SExpRec) : memory * nat.
  refine (let p := stream_head (state_fresh_locations S) in ({|
      state_heap_SExp := write S p e_ ;
      state_fresh_locations := stream_tail (state_fresh_locations S) |},
    p)).
  - introv I. rewrite stream_tail_nth in I. forwards~ I': @indom_write_inv I.
    + unfolds p. rewrite stream_head_nth. applys* state_fresh_locations_different.
    + applys~ state_fresh_locations_fresh I'.
  - introv D. repeat rewrite stream_tail_nth. applys* state_fresh_locations_different.
Defined.

Definition alloc_memory_SExp S e_ : memory * SExpRec_pointer :=
  let (S, p) := alloc_memory_SExp_nat S e_ in
  (S, Some p).

(** Writes a value in the state. Might return [None] if the cell is not already allocated. **)
Definition write_memory_SExp_nat (S : memory) (e : nat) (e_ : SExpRec) : option memory.
  refine (match read_option S e as r return r = _ -> _ with
          | None => fun _ => None
          | Some _ => fun Eq => Some {|
              state_heap_SExp := write S e e_ ;
              state_fresh_locations := state_fresh_locations S |}
          end eq_refl).
  - introv. apply not_indom_write.
    + introv E. applys state_fresh_locations_fresh. rewrite E.
      symmetry in Eq. applys~ read_option_indom Eq.
    + applys~ state_fresh_locations_fresh.
  - apply* state_fresh_locations_different.
Defined.

Definition write_memory_SExp (S : memory) (e : SExpRec_pointer) (e_ : SExpRec) :=
  match e with
  | None => None
  | Some e => write_memory_SExp_nat S e e_
  end.

Definition read_SExp_nat (S : memory) (e : nat) : option SExpRec :=
  read_option S e.

(** Reads a value in the state. **)
Definition read_SExp (S : memory) (e : SExpRec_pointer) :=
  match e with
  | None => None
  | Some e => read_SExp_nat S e
  end.

Lemma alloc_memory_SExp_nat_read_SExp : forall S S' e_ e,
  alloc_memory_SExp_nat S e_ = (S', e) ->
  read_SExp S' (Some e) = Some e_.
Proof. introv Eq. inverts Eq. do 2 unfolds. simpl. rewrite~ read_option_write_same. Qed.

Lemma alloc_memory_SExp_read_SExp : forall S S' e_ e,
  alloc_memory_SExp S e_ = (S', e) ->
  read_SExp S' e = Some e_.
Proof. introv Eq. inverts Eq. applys* alloc_memory_SExp_nat_read_SExp. Qed.

Lemma destruct_write_memory_SExp_nat_None : forall (S : memory) e e_,
  read_option S e = None ->
  write_memory_SExp_nat S e e_ = None.
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
  + symmetry in E. lets R': (rm R) (read_option S e). erewrite (R' _ _ E). destruct~ E.
Qed.

Lemma destruct_write_memory_SExp_nat : forall (S : memory) e e_ v,
  read_option S e = Some v ->
  exists S',
    write_memory_SExp_nat S e e_ = Some S'
    /\ (S' : heap _ _) = write S e e_.
Proof.
  introv E. unfolds write_memory_SExp_nat.
  asserts R: (forall T T' (x : option T) (f1 : None = x -> T') (f2 : forall v, Some v = x -> T')
      v (H : Some v = x),
    match x as r return r = x -> T' with
    | None => f1
    | Some v => fun E => f2 v E
    end eq_refl
    = f2 v H).
  + clear. introv. destruct~ H.
  + symmetry in E. lets R': (rm R) (read_option S e). rewrite (R' _ _ _ E). clear.
    eexists. splits~.
Qed.

Lemma write_memory_SExp_nat_read_SExp_same : forall S S' e_ e,
  write_memory_SExp_nat S e e_ = Some S' ->
  read_SExp S' (Some e) = Some e_.
Proof.
  introv E. simpl. destruct (read_option S e) eqn: E'.
  + forwards (S2&E1&E2): destruct_write_memory_SExp_nat E'.
    rewrite E in E1. inverts E1. unfolds. rewrite E2. rewrite~ read_option_write_same.
  + forwards Eq: destruct_write_memory_SExp_nat_None E'. rewrite Eq in E. false*.
Qed.

Lemma write_memory_SExp_read_SExp_same : forall S S' e_ e,
  write_memory_SExp S e e_ = Some S' ->
  read_SExp S' e = Some e_.
Proof. introv E. destruct e; tryfalse. applys~ write_memory_SExp_nat_read_SExp_same E. Qed.

Lemma write_memory_SExp_nat_read_SExp : forall S S' e_ e e',
  write_memory_SExp_nat S e e_ = Some S' ->
  e <> e' ->
  read_SExp S' (Some e') = read_SExp S (Some e').
Proof.
  introv E D. simpl. destruct (read_option S e) eqn: E'.
  + forwards (S2&E1&E2): destruct_write_memory_SExp_nat E'.
    rewrite E in E1. inverts E1. unfolds. rewrite E2. rewrite~ read_option_write.
  + forwards Eq: destruct_write_memory_SExp_nat_None E'. rewrite Eq in E. false*.
Qed.

Lemma write_memory_SExp_read_SExp : forall S S' e_ e e',
  write_memory_SExp S e e_ = Some S' ->
  e <> e' ->
  read_SExp S' e' = read_SExp S e'.
Proof.
  introv E D. destruct e; tryfalse. destruct e'.
  + applys~ write_memory_SExp_nat_read_SExp E.
  + reflexivity.
Qed.

Lemma read_SExp_write_memory_SExp_nat : forall S e_ e'_ e,
  read_SExp S (Some e) = Some e_ ->
  exists S', write_memory_SExp_nat S e e'_ = Some S'.
Proof.
  introv E. simpl in E. forwards (S'&E1&E2): destruct_write_memory_SExp_nat E.
  exists S'. rewrite~ E1.
Qed.

Lemma read_SExp_write_memory_SExp : forall S e_ e'_ e,
  read_SExp S e = Some e_ ->
  exists S', write_memory_SExp S e e'_ = Some S'.
Proof. introv E. destruct e; tryfalse. applys~ read_SExp_write_memory_SExp_nat E. Qed.


(** * A Model for R’s State **)

Record state := make_state {
    state_memory :> memory
  }.


Definition state_with_memory (S : state) m := {|
    state_memory := m
  |}.

Definition alloc_SExp (S : state) e_ :=
  let (m, e) := alloc_memory_SExp S e_ in
  (state_with_memory S m, e).

Definition write_SExp (S : state) e e_ :=
  match write_memory_SExp S e e_ with
  | Some m => Some (state_with_memory S m)
  | None => None
  end.


(** * Initial State **)

(** ** Initial Memory **)

CoFixpoint all_locations n : stream nat :=
  n ::: (all_locations (1 + n)).

Lemma all_locations_nth : forall n m,
  nth m (all_locations n) = m + n.
Proof.
  introv. gen n. induction m; introv.
  - reflexivity.
  - simpl. rewrite~ IHm.
Qed.

Definition empty_memory : memory.
  refine {|
      state_heap_SExp := empty ;
      state_fresh_locations := all_locations 0
    |}.
  - introv. apply~ @not_indom_empty. typeclass.
  - introv D. repeat rewrite all_locations_nth. math.
Defined.


(* TODO: Fix this. Also track “None” in the Coq and replace it by the corresponding value. *)
Definition NULL : SExpRec_pointer := None.
Definition R_NilValue : SExpRec_pointer := NULL. (* snd (alloc_SExp empty_state Nil_SExpRec). *)
Definition R_DotsSymbol : SExpRec_pointer := NULL. (* TODO: See names.c *)
Definition R_GlobalEnv : SExpRec_pointer := NULL. (* TODO: See envir.c *)
Definition R_EmptyEnv : SExpRec_pointer := NULL. (* TODO: See envir.c *)
Definition R_BaseEnv : SExpRec_pointer := NULL. (* TODO: See envir.c *)
Definition R_UnboundValue : SExpRec_pointer := NULL. (* TODO: See names.c *)
Definition R_MissingArg : SExpRec_pointer := NULL. (* TODO: See names.c *)


(** ** Initial State **)

Definition empty_state := {|
    state_memory := empty_memory
  |}.

Definition initial_state := empty_state.

