(** Monads.
 * Provides some model for the C memory and some monads to manipulate it easily. **)

Set Implicit Arguments.
Require Export String.
Require Export RinternalsAux TLC.LibHeap Shared.
Require Import TLC.LibStream.

(** * A Model for the C Memory **)

(** ** Basic Model **)

(** The global state of the C environment. In particular, it maps SEXP
 * pointers to their corresponding expressions. **)
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
Definition alloc_SExp_nat (S : state) (e : SExpRec) : state * nat.
  refine (let p := stream_head (state_fresh_locations S) in ({|
      state_heap_SExp := write S p e ;
      state_fresh_locations := stream_tail (state_fresh_locations S) |},
    p)).
  - introv I. rewrite stream_tail_nth in I. forwards~ I': @indom_write_inv I.
    + unfolds p. rewrite stream_head_nth. applys* state_fresh_locations_different.
    + applys~ state_fresh_locations_fresh I'.
  - introv D. repeat rewrite stream_tail_nth. applys* state_fresh_locations_different.
Defined.

Definition alloc_SExp S e : state * SExpRec_pointer :=
  let (S, p) := alloc_SExp_nat S e in
  (S, Some p).

(** Writes a value in the state. Might return [None] if the cell is not already allocated. **)
Definition write_SExp_nat (S : state) (p : nat) (e : SExpRec) : option state.
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

Definition write_SExp (S : state) (p : SExpRec_pointer) (e : SExpRec) :=
  match p with
  | None => None
  | Some p => write_SExp_nat S p e
  end.

Definition read_SExp_nat (S : state) (p : nat) : option SExpRec :=
  read_option S p.

(** Reads a value in the state. **)
Definition read_SExp (S : state) (p : SExpRec_pointer) :=
  match p with
  | None => None
  | Some p => read_SExp_nat S p
  end.

Lemma alloc_SExp_nat_read_SExp : forall S S' e p,
  alloc_SExp_nat S e = (S', p) ->
  read_SExp S' (Some p) = Some e.
Proof. introv Eq. inverts Eq. do 2 unfolds. simpl. rewrite~ read_option_write_same. Qed.

Lemma alloc_SExp_read_SExp : forall S S' e p,
  alloc_SExp S e = (S', p) ->
  read_SExp S' p = Some e.
Proof. introv Eq. inverts Eq. applys* alloc_SExp_nat_read_SExp. Qed.

Lemma destruct_write_SExp_nat_None : forall (S : state) p e,
  read_option S p = None ->
  write_SExp_nat S p e = None.
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

Lemma destruct_write_SExp_nat : forall (S : state) p e v,
  read_option S p = Some v ->
  exists S',
    write_SExp_nat S p e = Some S'
    /\ (S' : heap _ _) = write S p e.
Proof.
  introv E. unfolds write_SExp_nat.
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

Lemma write_SExp_nat_read_SExp_same : forall S S' e p,
  write_SExp_nat S p e = Some S' ->
  read_SExp S' (Some p) = Some e.
Proof.
  introv E. simpl. destruct (read_option S p) eqn: E'.
  + forwards (S2&E1&E2): destruct_write_SExp_nat E'.
    rewrite E in E1. inverts E1. unfolds. rewrite E2. rewrite~ read_option_write_same.
  + forwards Eq: destruct_write_SExp_nat_None E'. rewrite Eq in E. false*.
Qed.

Lemma write_SExp_read_SExp_same : forall S S' e p,
  write_SExp S p e = Some S' ->
  read_SExp S' p = Some e.
Proof. introv E. destruct p; tryfalse. applys~ write_SExp_nat_read_SExp_same E. Qed.

Lemma write_SExp_nat_read_SExp : forall S S' e p p',
  write_SExp_nat S p e = Some S' ->
  p <> p' ->
  read_SExp S' (Some p') = read_SExp S (Some p').
Proof.
  introv E D. simpl. destruct (read_option S p) eqn: E'.
  + forwards (S2&E1&E2): destruct_write_SExp_nat E'.
    rewrite E in E1. inverts E1. unfolds. rewrite E2. rewrite~ read_option_write.
  + forwards Eq: destruct_write_SExp_nat_None E'. rewrite Eq in E. false*.
Qed.

Lemma write_SExp_read_SExp : forall S S' e p p',
  write_SExp S p e = Some S' ->
  p <> p' ->
  read_SExp S' p' = read_SExp S p'.
Proof.
  introv E D. destruct p; tryfalse. destruct p'.
  + applys~ write_SExp_nat_read_SExp E.
  + reflexivity.
Qed.

Lemma read_SExp_write_SExp_nat : forall S e e' p,
  read_SExp S (Some p) = Some e ->
  exists S', write_SExp_nat S p e' = Some S'.
Proof.
  introv E. simpl in E. forwards (S'&E1&E2): destruct_write_SExp_nat E.
  exists S'. rewrite~ E1.
Qed.

Lemma read_SExp_write_SExp : forall S e e' p,
  read_SExp S p = Some e ->
  exists S', write_SExp S p e' = Some S'.
Proof. introv E. destruct p; tryfalse. applys~ read_SExp_write_SExp_nat E. Qed.


(* TODO: Do we need this? There is already allocList from Reval/memory.c
(** ** Support for Arrays **)

Fixpoint alloc_array_SExp S (es : list SExpRec) : state * SExpRec_pointer :=
  match es with
  | nil => (S, None)
  | e :: es =>
    let (S, p) := alloc_SExp S e in
  end.

Lemmae of the form: if the read is in the length of the array, then it succeeds.
*)

(** ** Initial Memory **)

Definition empty_state : state.
  refine {|
      state_heap_SExp := empty ;
      state_fresh_locations := stream nat TODO
    |}.
  - introv. apply indom_empty.
  - introv D. apply* D.
Defined.

(* TODO: Fix this. Also track “None” in the Coq and replace it by the corresponding value. *)
Definition NULL := None.
Definition R_DotsSymbol := ?.
Definition R_GlobalEnv := ?.
Definition R_EmptyEnv := ?.
Definition R_BaseEnv := ?.
Definition R_UnboundValue := ?.
Definition R_MissingArg := ?.
Definition R_NilValue := snd (alloc_SExp empty_state Nil_SExpRec).
Definition initial_state := fst (alloc_SExp empty_state Nil_SExpRec).


(** * Monads **)

(** ** Monadic Type **)

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
 * more subjective. Sometimes, R returns an error because R consider
 * that something can not happen.
 * As a general rule, the only difference between [result_error] and
 * [result_impossible] is that we do care in this formalisation that
 * [result_impossible] may never be returned, whilst we consider that
 * [result_error] is not a huge issue. **)

(** ** Generic Monads **)

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

(** Updating the first element of a list. **)
Definition set_car A S car (p : SExpRec_pointer) (f : state -> result A) : result A :=
  if_defined S (read_SExp S p) (fun p_ =>
    if_defined S (get_listSxp p_) (fun p_list =>
      let p_list := set_car_list car p_list in
      let p_ := {|
          SExpRec_header := SExpRec_header p_ ;
          SExpRec_data := p_list
        |} in
      if_defined S (write_SExp S p p_) f).

(** ** Monads to View Basic Language Elements Differently **)

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

