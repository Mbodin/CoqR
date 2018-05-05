(** State.
  Provides a model for the C memory. **)

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
Require Export String.
Require Export RinternalsAux TLC.LibHeap Common.
Require Import TLC.LibStream.

(** * A Model for the C Memory **)

(** ** Definition **)

(** The global state of the C memory. In particular, it maps SEXP
  pointers to their corresponding expressions. **)
Record memory := make_memory {
    state_heap_SExp :> heap nat SExpRec ;
    state_fresh_locations : stream nat ;
    state_fresh_locations_fresh : forall n,
      ~ indom state_heap_SExp (LibStream.nth n state_fresh_locations) ;
    state_fresh_locations_different : forall n1 n2,
      n1 <> n2 ->
      LibStream.nth n1 state_fresh_locations <> LibStream.nth n2 state_fresh_locations
  }.

(** ** Some properties about it **)

(** Due to the coercion between [memory] and [heap], it is possible to
  have an hypothesis displayed as [S1 = S2] whilst it really means
  [state_heap_SExp S1 = state_heap_SExp S2].  To get the full equality,
  we need the operation below. **)

Record memory_same_except_for_memory S1 S2 := make_memory_same_except_for_memory {
    memory_same_except_for_memory_fresh_locations :
      state_fresh_locations S1 = state_fresh_locations S2
  }.

Lemma memory_same_except_for_memory_refl : forall S,
  memory_same_except_for_memory S S.
Proof. introv. constructors*. Qed.

Lemma memory_same_except_for_memory_trans : forall S1 S2 S3,
  memory_same_except_for_memory S1 S2 ->
  memory_same_except_for_memory S2 S3 ->
  memory_same_except_for_memory S1 S3.
Proof. introv [E1] [E2]. constructors. etransitivity; eassumption. Qed.

Lemma memory_same_except_for_memory_sym : forall S1 S2,
  memory_same_except_for_memory S1 S2 ->
  memory_same_except_for_memory S2 S1.
Proof. introv [E]. constructors*. Qed.

Lemma memory_same_except_for_memory_eq : forall S1 S2,
  memory_same_except_for_memory S1 S2 ->
  (S1 : heap _ _) = (S2 : heap _ _) ->
  S1 = S2.
Proof. introv [E1] E2. destruct S1, S2. simpls. substs. fequals. Qed.

(** As the definition of heaps is axiomatic and only describes its
  interface, there is no easy way to prove that two heaps are equals.
  This is fine, as what we usually need is to prove that two heaps are
  equivalent.  The following definition catches this notion. **)

Record memory_equiv (S1 S2 : memory) := make_memory_equiv {
    memory_equiv_heap : heap_equiv S1 S2 ;
    memory_equiv_rest : memory_same_except_for_memory S1 S2
  }.

Lemma memory_equiv_refl : forall S,
  memory_equiv S S.
Proof.
  introv. constructors.
  - apply~ heap_equiv_refl.
  - apply~ memory_same_except_for_memory_refl.
Qed.

Lemma memory_equiv_trans : forall S1 S2 S3,
  memory_equiv S1 S2 ->
  memory_equiv S2 S3 ->
  memory_equiv S1 S3.
Proof.
  introv [E1 R1] [E2 R2]. constructors.
  - applys~ heap_equiv_trans E1 E2.
  - applys~ memory_same_except_for_memory_trans R1 R2.
Qed.

Lemma memory_equiv_sym : forall S1 S2,
  memory_equiv S1 S2 ->
  memory_equiv S2 S1.
Proof.
  introv [E R]. constructors.
  - applys~ heap_equiv_sym E.
  - applys~ memory_same_except_for_memory_sym R.
Qed.

(** ** Operations **)

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

Definition alloc_memory_SExp S e_ : memory * SEXP :=
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

Definition write_memory_SExp (S : memory) (e : SEXP) (e_ : SExpRec) :=
  match e with
  | None => None
  | Some e => write_memory_SExp_nat S e e_
  end.

Definition read_SExp_nat (S : memory) (e : nat) : option SExpRec :=
  read_option S e.

(** Reads a value in the state. **)
Definition read_SExp (S : memory) (e : SEXP) :=
  match e with
  | None => None
  | Some e => read_SExp_nat S e
  end.

(** ** Operation properties **)

Lemma read_SExp_NULL : forall S,
  read_SExp S NULL = None.
Proof. reflexivity. Qed.

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

Lemma destruct_write_memory_SExp_nat_None_inv : forall (S : memory) e e_,
  write_memory_SExp_nat S e e_ = None ->
  read_option S e = None.
Proof.
  introv E. unfolds in E.
  asserts R: (forall T T' (x : option T) (f : forall v, Some v = x -> _),
      match x as r return r = x -> option T' with
      | None => fun _ => None
      | Some v => fun E => Some (f _ E)
      end eq_refl
      = None ->
    x = None).
  + clear. introv E. destruct~ x. inverts~ E.
  + applys (rm R) E.
Qed.

Lemma destruct_write_memory_SExp_nat : forall (S : memory) e e_ v,
  read_option S e = Some v ->
  exists S',
    write_memory_SExp_nat S e e_ = Some S'
    /\ (S' : heap _ _) = write S e e_
    /\ memory_same_except_for_memory S S'.
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
    eexists. splits~. constructors. reflexivity.
Qed.

Lemma destruct_write_memory_SExp_nat_inv : forall (S S' : memory) e e_,
  write_memory_SExp_nat S e e_ = Some S' ->
  exists v, read_option S e = Some v.
Proof.
  introv W. destruct read_option eqn: R; autos*.
  rewrite* destruct_write_memory_SExp_nat_None in W. inverts* W.
Qed.

Lemma write_memory_SExp_nat_read_SExp_same : forall S S' e_ e,
  write_memory_SExp_nat S e e_ = Some S' ->
  read_SExp S' (Some e) = Some e_.
Proof.
  introv E. simpl. forwards (v&E'): destruct_write_memory_SExp_nat_inv E.
  forwards (S2&E1&E2&_): destruct_write_memory_SExp_nat E'.
  rewrite E in E1. inverts E1. unfolds. rewrite E2. rewrite~ read_option_write_same.
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
  introv E D. simpl. forwards (v&E'): destruct_write_memory_SExp_nat_inv E.
  forwards (S2&E1&E2&_): destruct_write_memory_SExp_nat E'.
  rewrite E in E1. inverts E1. unfolds. rewrite E2. rewrite~ read_option_write.
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

Lemma read_SExp_write_memory_SExp_None : forall S e'_ e,
  read_SExp S e = None ->
  write_memory_SExp S e e'_ = None.
Proof.
  introv E. unfolds. destruct~ e.
  applys~ destruct_write_memory_SExp_nat_None E.
Qed.

Lemma write_memory_SExp_read_SExp_None : forall S e'_ e,
  write_memory_SExp S e e'_ = None ->
  read_SExp S e = None.
Proof.
  introv E. unfolds in E. destruct~ e.
  applys~ destruct_write_memory_SExp_nat_None_inv E.
Qed.

Lemma read_SExp_equiv : forall S1 S2 e,
  memory_equiv S1 S2 ->
  read_SExp S1 e = read_SExp S2 e.
Proof.
  introv E. destruct~ e. simpl. unfolds.
  apply~ heap_equiv_read_option. applys~ memory_equiv_heap E.
Qed.

Lemma alloc_memory_SExp_equiv : forall S1 S2 S1' S2' e_ e1 e2,
  memory_equiv S1 S2 ->
  alloc_memory_SExp S1 e_ = (S1', e1) ->
  alloc_memory_SExp S2 e_ = (S2', e2) ->
  e1 = e2 /\ memory_equiv S1' S2'.
Proof.
  introv E A1 A2. splits.
  - inverts A1. inverts A2.
    rewrites~ >> memory_same_except_for_memory_fresh_locations (memory_equiv_rest E).
  - constructors~.
    + inverts A1. inverts A2. simpl.
      rewrites~ >> memory_same_except_for_memory_fresh_locations (memory_equiv_rest E).
      applys~ heap_equiv_write E.
    + constructors~. inverts A1. inverts A2. simpl.
      rewrites~ >> memory_same_except_for_memory_fresh_locations (memory_equiv_rest E).
Qed.

Lemma write_memory_SExp_equiv : forall S1 S2 S1' S2' e e_,
  memory_equiv S1 S2 ->
  write_memory_SExp S1 e e_ = Some S1' ->
  write_memory_SExp S2 e e_ = Some S2' ->
  memory_equiv S1' S2'.
Proof.
  introv E W1 W2. destruct e; tryfalse. simpls.
  forwards (v1&E1): destruct_write_memory_SExp_nat_inv W1.
  forwards (S1''&W1'&E1'&R1): destruct_write_memory_SExp_nat E1.
  rewrite W1 in W1'. inverts W1'.
  forwards (v2&E2): destruct_write_memory_SExp_nat_inv W2.
  forwards (S2''&W2'&E2'&R2): destruct_write_memory_SExp_nat E2.
  rewrite W2 in W2'. inverts W2'. constructors~.
  - rewrite E1'. rewrite E2'. applys~ heap_equiv_write E.
  - applys memory_same_except_for_memory_trans S1.
    + applys~ memory_same_except_for_memory_sym R1.
    + applys~ memory_same_except_for_memory_trans (memory_equiv_rest E) R2.
Qed.

Lemma write_memory_SExp_nat_write_memory_SExp_nat_eq : forall S1 S2 S3 p p_1 p_2,
  write_memory_SExp_nat S1 p p_1 = Some S2 ->
  write_memory_SExp_nat S2 p p_2 = Some S3 ->
  exists S3',
    write_memory_SExp_nat S1 p p_2 = Some S3'
    /\ memory_equiv S3 S3'.
Proof.
  introv W1 W2. forwards (v1&R1): destruct_write_memory_SExp_nat_inv W1.
  forwards (v2&R2): destruct_write_memory_SExp_nat_inv W2.
  forwards (S2'&W1'&ES2'&E12): destruct_write_memory_SExp_nat p_1 R1.
  rewrite W1' in W1. inverts W1.
  forwards (S3'&W3'&ES3'&E23): destruct_write_memory_SExp_nat p_2 R2.
  rewrite W3' in W2. inverts W2.
  forwards (S2'&W2'&ES2''&E12'): destruct_write_memory_SExp_nat p_2 R1.
  rewrite W2'. eexists. splits*. constructors~.
  - rewrite ES2''. rewrite ES3'. rewrite ES2'.
    apply~ heap_equiv_write_write. apply~ heap_equiv_refl.
  - applys~ memory_same_except_for_memory_trans E12'.
    apply memory_same_except_for_memory_sym.
    applys~ memory_same_except_for_memory_trans E12 E23.
Qed.

Lemma write_memory_SExp_write_memory_SExp_eq : forall S1 S2 S3 p p_1 p_2,
  write_memory_SExp S1 p p_1 = Some S2 ->
  write_memory_SExp S2 p p_2 = Some S3 ->
  exists S3',
    write_memory_SExp S1 p p_2 = Some S3'
    /\ memory_equiv S3 S3'.
Proof.
  introv W1 W2. destruct p as [p|]; tryfalse. simpls.
  applys~ write_memory_SExp_nat_write_memory_SExp_nat_eq W1 W2.
Qed.

Lemma write_memory_SExp_nat_write_memory_SExp_nat_neq : forall S1 S2 S3 p1 p2 p_1 p_2,
  p1 <> p2 ->
  write_memory_SExp_nat S1 p1 p_1 = Some S2 ->
  write_memory_SExp_nat S2 p2 p_2 = Some S3 ->
  exists S2' S3',
    write_memory_SExp_nat S1 p2 p_2 = Some S2'
    /\ write_memory_SExp_nat S2' p1 p_1 = Some S3'
    /\ memory_equiv S3 S3'.
Proof.
  introv D W1 W2. forwards (v1&R1): destruct_write_memory_SExp_nat_inv W1.
  forwards (v2&R2): destruct_write_memory_SExp_nat_inv W2.
  forwards (S2'&W1'&ES2'&E12): destruct_write_memory_SExp_nat p_1 R1.
  rewrite W1' in W1. inverts W1.
  forwards (S3'&W3'&ES3'&E23): destruct_write_memory_SExp_nat p_2 R2.
  rewrite W3' in W2. inverts W2.
  forwards (S2'&W2'&ES2''&E12'): destruct_write_memory_SExp_nat S1 p2 p_2.
  { apply~ @binds_read_option. apply read_option_binds in R2.
    rewrite ES2' in R2. applys~ @binds_write_neq_inv R2. }
  forwards (S3'&W3''&ES3''&E23'): destruct_write_memory_SExp_nat S2' p1 p_1.
  { apply~ @binds_read_option. apply read_option_binds in R1.
    rewrite ES2''. applys~ @binds_write_neq R1. }
  exists S2' S3'. splits~. constructors~.
  - rewrite ES3'. rewrite ES3''. rewrite ES2'. rewrite ES2''.
    apply~ heap_equiv_write_swap. apply~ heap_equiv_refl.
  - applys~ memory_same_except_for_memory_trans E23'.
    applys~ memory_same_except_for_memory_trans E12'.
    apply memory_same_except_for_memory_sym.
    applys~ memory_same_except_for_memory_trans E12 E23.
Qed.

Lemma write_memory_SExp_write_memory_SExp_neq : forall S1 S2 S3 p1 p2 p_1 p_2,
  p1 <> p2 ->
  write_memory_SExp S1 p1 p_1 = Some S2 ->
  write_memory_SExp S2 p2 p_2 = Some S3 ->
  exists S2' S3',
    write_memory_SExp S1 p2 p_2 = Some S2'
    /\ write_memory_SExp S2' p1 p_1 = Some S3'
    /\ memory_equiv S3 S3'.
Proof.
  introv D W1 W2. destruct p1 as [p1|], p2 as [p2|]; tryfalse. simpls.
  applys~ write_memory_SExp_nat_write_memory_SExp_nat_neq W1 W2.
Qed.

Lemma alloc_memory_SExp_nat_write_memory_SExp_nat_eq : forall S1 S2 S3 p p_1 p_2,
  alloc_memory_SExp_nat S1 p_1 = (S2, p) ->
  write_memory_SExp_nat S2 p p_2 = Some S3 ->
  exists S3',
    alloc_memory_SExp_nat S1 p_2 = (S3', p)
    /\ memory_equiv S3 S3'.
Proof.
  introv A W. forwards (v&R): destruct_write_memory_SExp_nat_inv W.
  forwards (S3'&W'&ES3'&E23): destruct_write_memory_SExp_nat p_2 R.
  rewrite W' in W. inverts W.
  eexists. splits~.
  - inverts A. unfolds. simpl. fequals.
  - simpl. constructors~.
    + simpl. rewrite ES3'. inverts A. simpl.
      apply~ heap_equiv_write_write. apply~ heap_equiv_refl.
    + apply memory_same_except_for_memory_sym.
      applys~ memory_same_except_for_memory_trans E23.
      inverts A. constructors~; simpl.
Qed.

Lemma alloc_memory_SExp_write_memory_SExp_eq : forall S1 S2 S3 p p_1 p_2,
  alloc_memory_SExp S1 p_1 = (S2, p) ->
  write_memory_SExp S2 p p_2 = Some S3 ->
  exists S3',
    alloc_memory_SExp S1 p_2 = (S3', p)
    /\ memory_equiv S3 S3'.
Proof.
  introv A W. destruct p as [p|]; tryfalse. simpls.
  forwards~ (S3'&W'&E): alloc_memory_SExp_nat_write_memory_SExp_nat_eq S1 p p_1 W.
  - inverts~ A.
  - exists S3'. splits~. unfolds. rewrite~ W'.
Qed.

Lemma alloc_memory_SExp_nat_write_memory_SExp_nat_neq : forall S1 S2 S3 p1 p2 p_1 p_2,
  p1 <> p2 ->
  alloc_memory_SExp_nat S1 p_1 = (S2, p1) ->
  write_memory_SExp_nat S2 p2 p_2 = Some S3 ->
  exists S2' S3',
    write_memory_SExp_nat S1 p2 p_2 = Some S2'
    /\ alloc_memory_SExp_nat S2' p_1 = (S3', p1)
    /\ memory_equiv S3 S3'.
Proof.
  introv D A W. forwards (v&R): destruct_write_memory_SExp_nat_inv W.
  forwards (S3'&W'&ES3'&E23): destruct_write_memory_SExp_nat p_2 R.
  rewrite W' in W. inverts W.
  forwards (S2'&W2'&ES2''&E12'): destruct_write_memory_SExp_nat S1 p2 p_2.
  { apply~ @binds_read_option. apply read_option_binds in R.
    inverts A. simpls. applys~ @binds_write_neq_inv R. }
  exists S2'. eexists. splits~.
  - inverts A. unfolds. simpl. fequals.
    rewrites~ >> memory_same_except_for_memory_fresh_locations E12'.
  - simpl. constructors~.
    + simpl. rewrite ES2''. rewrite ES3'. inverts A. simpl.
      rewrites~ >> memory_same_except_for_memory_fresh_locations E12'.
      apply~ heap_equiv_write_swap.
      * introv AE. false state_fresh_locations_fresh S2'.
        rewrite <- stream_head_nth. rewrite AE. rewrite ES2''. apply~ @indom_write_eq.
      * apply~ heap_equiv_refl.
    + apply memory_same_except_for_memory_sym.
      applys~ memory_same_except_for_memory_trans E23.
      inverts A. constructors~; simpl.
      rewrites~ >> memory_same_except_for_memory_fresh_locations E12'.
Qed.

Lemma alloc_memory_SExp_write_memory_SExp_neq : forall S1 S2 S3 p1 p2 p_1 p_2,
  p1 <> p2 ->
  alloc_memory_SExp S1 p_1 = (S2, p1) ->
  write_memory_SExp S2 p2 p_2 = Some S3 ->
  exists S2' S3',
    write_memory_SExp S1 p2 p_2 = Some S2'
    /\ alloc_memory_SExp S2' p_1 = (S3', p1)
    /\ memory_equiv S3 S3'.
Proof.
  introv D A W. destruct p1 as [p1|], p2 as [p2|]; tryfalse. simpls.
  forwards~ (S2'&S3'&W'&A'&E): alloc_memory_SExp_nat_write_memory_SExp_nat_neq S1 p1 p_1 W.
  - inverts~ A.
  - exists S2' S3'. splits~. inverts~ A'.
Qed.


(** * A Model for R’s Contexts **)

(** Contexts are defined in the file main/context.c of R source code. **)

Definition context_type := nbits 7.

Definition CTXT_TOPLEVEL := 0.
Definition CTXT_NEXT := 1.
Definition CTXT_BREAK := 2.
Definition CTXT_LOOP := 3.
Definition CTXT_FUNCTION := 4.
Definition CTXT_CCODE := 8.
Definition CTXT_RETURN := 12.
Definition CTXT_BROWSER := 16.
Definition CTXT_GENERIC := 20.
Definition CTXT_RESTART := 32.
Definition CTXT_BUILTIN := 64.

Definition Ctxt_TopLevel : context_type := @nat_to_nbits 7 CTXT_TOPLEVEL ltac:(nbits_ok).
Definition Ctxt_Next : context_type := @nat_to_nbits 7 CTXT_NEXT ltac:(nbits_ok).
Definition Ctxt_Break : context_type := @nat_to_nbits 7 CTXT_BREAK ltac:(nbits_ok).
Definition Ctxt_Loop : context_type := @nat_to_nbits 7 CTXT_LOOP ltac:(nbits_ok).
Definition Ctxt_Function : context_type := @nat_to_nbits 7 CTXT_FUNCTION ltac:(nbits_ok).
Definition Ctxt_CCode : context_type := @nat_to_nbits 7 CTXT_CCODE ltac:(nbits_ok).
Definition Ctxt_Return : context_type := @nat_to_nbits 7 CTXT_RETURN ltac:(nbits_ok).
Definition Ctxt_Browser : context_type := @nat_to_nbits 7 CTXT_BROWSER ltac:(nbits_ok).
Definition Ctxt_Generic : context_type := @nat_to_nbits 7 CTXT_GENERIC ltac:(nbits_ok).
Definition Ctxt_Restart : context_type := @nat_to_nbits 7 CTXT_RESTART ltac:(nbits_ok).
Definition Ctxt_Builtin : context_type := @nat_to_nbits 7 CTXT_BUILTIN ltac:(nbits_ok).

Definition empty_context_type := Ctxt_TopLevel.

Instance context_type_Comparable : Comparable context_type.
  typeclass.
Defined.

Instance context_type_Inhab : Inhab context_type.
  apply prove_Inhab. apply empty_context_type.
Defined.

Definition context_type_mask (t1 t2 : context_type) :=
  nbits_intersects t1 t2.

Definition context_type_merge (t1 t2 : context_type) :=
  nbits_or t1 t2.


(** Note: not all fields have been modeled. See the report or the
  original definition in the file include/Defn.h for more details. **)
(** The [cjmpbuf] field is here just a number, different for all
  context. The jumping process occurs by returning a special
  result (see Monads.v or the repport). **)
(** RCNTXT, *context **)
Inductive context := make_context {
    context_nextcontext : option context ;
    context_cjmpbuf : nat ;
    context_callflag : context_type ;
    context_promargs : SEXP ;
    context_callfun : SEXP ;
    context_sysparent : SEXP ;
    context_call : SEXP ;
    context_cloenv : SEXP ;
    context_conexit : SEXP ;
    context_returnValue : SEXP ;
    context_jumptarget : option context ;
    context_jumpmask : context_type
  }.

Fixpoint context_rect' (P : context -> Type) HNoneNone HNoneSome HSomeNone HSomeSome c : P c :=
  match c with
  | make_context nextcontext cjmpbuf callflag promargs callfun sysparent call cloenv
      conexit returnValue jumptarget jumpmask =>
    match nextcontext, jumptarget with
    | None, None =>
      HNoneNone cjmpbuf callflag promargs callfun sysparent call cloenv conexit returnValue jumpmask
    | None, Some c' =>
      HNoneSome c' (context_rect' P HNoneNone HNoneSome HSomeNone HSomeSome c')
        cjmpbuf callflag promargs callfun sysparent call cloenv conexit returnValue jumpmask
    | Some c', None =>
      HSomeNone c' (context_rect' P HNoneNone HNoneSome HSomeNone HSomeSome c')
        cjmpbuf callflag promargs callfun sysparent call cloenv conexit returnValue jumpmask
    | Some c1, Some c2 =>
      HSomeSome c1 c2 (context_rect' P HNoneNone HNoneSome HSomeNone HSomeSome c1)
        (context_rect' P HNoneNone HNoneSome HSomeNone HSomeSome c2)
        cjmpbuf callflag promargs callfun sysparent call cloenv conexit returnValue jumpmask
    end
  end.

Definition context_ind' (P : context -> Prop) := context_rect' P.

Fixpoint context_rect_next_context (P : context -> Type) HNone HSome c : P c :=
  match c with
  | make_context nextcontext cjmpbuf callflag promargs callfun sysparent call cloenv
      conexit returnValue jumptarget jumpmask =>
    match nextcontext with
    | None =>
      HNone cjmpbuf callflag promargs callfun sysparent call cloenv conexit returnValue jumptarget jumpmask
    | Some c' =>
      HSome c' (context_rect_next_context P HNone HSome c')
        cjmpbuf callflag promargs callfun sysparent call cloenv conexit returnValue jumptarget jumpmask
    end
  end.

Definition context_ind_next_context (P : context -> Prop) := context_rect_next_context P.

Fixpoint context_rect_jumptarget (P : context -> Type) HNone HSome c : P c :=
  match c with
  | make_context nextcontext cjmpbuf callflag promargs callfun sysparent call cloenv
      conexit returnValue jumptarget jumpmask =>
    match jumptarget with
    | None =>
      HNone nextcontext cjmpbuf callflag promargs callfun sysparent call cloenv conexit returnValue jumpmask
    | Some c' =>
      HSome c' (context_rect_jumptarget P HNone HSome c')
       nextcontext cjmpbuf callflag promargs callfun sysparent call cloenv conexit returnValue jumpmask
    end
  end.

Definition context_ind_jumptarget (P : context -> Prop) := context_rect_jumptarget P.

Instance context_Comparable : Comparable context.
  applys make_comparable. intros c1.
  induction c1 using context_rect'; intros c2;
    induction c2 using context_rect'; prove_decidable_eq.
Defined.

Definition context_with_callflag context callflag := {|
     context_nextcontext := context_nextcontext context ;
     context_cjmpbuf := context_cjmpbuf context ;
     context_callflag := callflag ;
     context_promargs := context_promargs context ;
     context_callfun := context_callfun context ;
     context_sysparent := context_sysparent context ;
     context_call := context_call context ;
     context_cloenv := context_cloenv context ;
     context_conexit := context_conexit context ;
     context_returnValue := context_returnValue context ;
     context_jumptarget := context_jumptarget context ;
     context_jumpmask := context_jumpmask context
   |}.

Definition context_with_conexit context conexit := {|
     context_nextcontext := context_nextcontext context ;
     context_cjmpbuf := context_cjmpbuf context ;
     context_callflag := context_callflag context ;
     context_promargs := context_promargs context ;
     context_callfun := context_callfun context ;
     context_sysparent := context_sysparent context ;
     context_call := context_call context ;
     context_cloenv := context_cloenv context ;
     context_conexit := conexit ;
     context_returnValue := context_returnValue context ;
     context_jumptarget := context_jumptarget context ;
     context_jumpmask := context_jumpmask context
   |}.

Definition context_with_returnValue context returnValue := {|
     context_nextcontext := context_nextcontext context ;
     context_cjmpbuf := context_cjmpbuf context ;
     context_callflag := context_callflag context ;
     context_promargs := context_promargs context ;
     context_callfun := context_callfun context ;
     context_sysparent := context_sysparent context ;
     context_call := context_call context ;
     context_cloenv := context_cloenv context ;
     context_conexit := context_conexit context ;
     context_returnValue := returnValue ;
     context_jumptarget := context_jumptarget context ;
     context_jumpmask := context_jumpmask context
   |}.

Definition context_with_jumptarget context jumptarget := {|
     context_nextcontext := context_nextcontext context ;
     context_cjmpbuf := context_cjmpbuf context ;
     context_callflag := context_callflag context ;
     context_promargs := context_promargs context ;
     context_callfun := context_callfun context ;
     context_sysparent := context_sysparent context ;
     context_call := context_call context ;
     context_cloenv := context_cloenv context ;
     context_conexit := context_conexit context ;
     context_returnValue := context_returnValue context ;
     context_jumptarget := jumptarget ;
     context_jumpmask := context_jumpmask context
   |}.

Definition context_with_jumpmask context jumpmask := {|
     context_nextcontext := context_nextcontext context ;
     context_cjmpbuf := context_cjmpbuf context ;
     context_callflag := context_callflag context ;
     context_promargs := context_promargs context ;
     context_callfun := context_callfun context ;
     context_sysparent := context_sysparent context ;
     context_call := context_call context ;
     context_cloenv := context_cloenv context ;
     context_conexit := context_conexit context ;
     context_returnValue := context_returnValue context ;
     context_jumptarget := context_jumptarget context ;
     context_jumpmask := jumpmask
   |}.


(** * A Model for R’s Connections **)

(** Output and input can perform various side effects, as well as
  calling function that may not be marshalable.  To avoid any
  difficulties, we define indirections. **)

Inductive open_type :=
  | null_open
  .

Inductive close_type :=
  | null_close
  .

Inductive destroy_type :=
  | null_destroy
  .

Inductive print_type :=
  | null_print
  | stdout_print
  | stderr_print
  .

Inductive flush_type :=
  | null_flush
  | stdout_flush
  | stderr_flush
  .


(** The following definition corresponds to the type
  [Rconn]/[Rconnection] in the file include/R_ext/Connections.h]. **)

Inductive Rconnection := make_Rconnection {
    Rconnection_class : string ;
    Rconnection_description : string ;
    Rconnection_mode : string ;
    Rconnection_text : bool ;
    Rconnection_isopen : bool ;
    Rconnection_incomplete : bool ;
    Rconnection_canread : bool ;
    Rconnection_canwrite : bool ;
    Rconnection_canseek : bool ;
    Rconnection_blocking : bool ;
    Rconnection_isGzcon : bool ;
    Rconnection_open : open_type ;
    Rconnection_close : close_type ;
    Rconnection_destroy : destroy_type ;
    Rconnection_print : print_type (** Corresponds to [vfprintf], but simplified. **) ;
    Rconnection_fflush : flush_type ;

    (** We allows connections to store information to represent the
      external state of the connection.  For instance, for random
      values, it can be the stream of future values. **)
    Rconnection_type : Type ;
    Rconnection_state : Rconnection_type
  }.

Definition Rconnection_with_class c class := {|
    Rconnection_class := class ;
    Rconnection_description := Rconnection_description c ;
    Rconnection_mode := Rconnection_mode c ;
    Rconnection_text := Rconnection_text c ;
    Rconnection_isopen := Rconnection_isopen c ;
    Rconnection_incomplete := Rconnection_incomplete c ;
    Rconnection_canread := Rconnection_canread c ;
    Rconnection_canwrite := Rconnection_canwrite c ;
    Rconnection_canseek := Rconnection_canseek c ;
    Rconnection_blocking := Rconnection_blocking c ;
    Rconnection_isGzcon := Rconnection_isGzcon c ;
    Rconnection_open := Rconnection_open c ;
    Rconnection_close := Rconnection_close c ;
    Rconnection_destroy := Rconnection_destroy c ;
    Rconnection_print := Rconnection_print c ;
    Rconnection_fflush := Rconnection_fflush c ;
    Rconnection_state := Rconnection_state c
  |}.

Definition Rconnection_with_isopen c isopen := {|
    Rconnection_class := Rconnection_class c ;
    Rconnection_description := Rconnection_description c ;
    Rconnection_mode := Rconnection_mode c ;
    Rconnection_text := Rconnection_text c ;
    Rconnection_isopen := isopen ;
    Rconnection_incomplete := Rconnection_incomplete c ;
    Rconnection_canread := Rconnection_canread c ;
    Rconnection_canwrite := Rconnection_canwrite c ;
    Rconnection_canseek := Rconnection_canseek c ;
    Rconnection_blocking := Rconnection_blocking c ;
    Rconnection_isGzcon := Rconnection_isGzcon c ;
    Rconnection_open := Rconnection_open c ;
    Rconnection_close := Rconnection_close c ;
    Rconnection_destroy := Rconnection_destroy c ;
    Rconnection_print := Rconnection_print c ;
    Rconnection_fflush := Rconnection_fflush c ;
    Rconnection_state := Rconnection_state c
  |}.

Definition Rconnection_with_canread c canread := {|
    Rconnection_class := Rconnection_class c ;
    Rconnection_description := Rconnection_description c ;
    Rconnection_mode := Rconnection_mode c ;
    Rconnection_text := Rconnection_text c ;
    Rconnection_isopen := Rconnection_isopen c ;
    Rconnection_incomplete := Rconnection_incomplete c ;
    Rconnection_canread := canread ;
    Rconnection_canwrite := Rconnection_canwrite c ;
    Rconnection_canseek := Rconnection_canseek c ;
    Rconnection_blocking := Rconnection_blocking c ;
    Rconnection_isGzcon := Rconnection_isGzcon c ;
    Rconnection_open := Rconnection_open c ;
    Rconnection_close := Rconnection_close c ;
    Rconnection_destroy := Rconnection_destroy c ;
    Rconnection_print := Rconnection_print c ;
    Rconnection_fflush := Rconnection_fflush c ;
    Rconnection_state := Rconnection_state c
  |}.

Definition Rconnection_with_canwrite c canwrite := {|
    Rconnection_class := Rconnection_class c ;
    Rconnection_description := Rconnection_description c ;
    Rconnection_mode := Rconnection_mode c ;
    Rconnection_text := Rconnection_text c ;
    Rconnection_isopen := Rconnection_isopen c ;
    Rconnection_incomplete := Rconnection_incomplete c ;
    Rconnection_canread := Rconnection_canread c ;
    Rconnection_canwrite := canwrite ;
    Rconnection_canseek := Rconnection_canseek c ;
    Rconnection_blocking := Rconnection_blocking c ;
    Rconnection_isGzcon := Rconnection_isGzcon c ;
    Rconnection_open := Rconnection_open c ;
    Rconnection_close := Rconnection_close c ;
    Rconnection_destroy := Rconnection_destroy c ;
    Rconnection_print := Rconnection_print c ;
    Rconnection_fflush := Rconnection_fflush c ;
    Rconnection_state := Rconnection_state c
  |}.

Definition Rconnection_with_destroy c destroy := {|
    Rconnection_class := Rconnection_class c ;
    Rconnection_description := Rconnection_description c ;
    Rconnection_mode := Rconnection_mode c ;
    Rconnection_text := Rconnection_text c ;
    Rconnection_isopen := Rconnection_isopen c ;
    Rconnection_incomplete := Rconnection_incomplete c ;
    Rconnection_canread := Rconnection_canread c ;
    Rconnection_canwrite := Rconnection_canwrite c ;
    Rconnection_canseek := Rconnection_canseek c ;
    Rconnection_blocking := Rconnection_blocking c ;
    Rconnection_isGzcon := Rconnection_isGzcon c ;
    Rconnection_open := Rconnection_open c ;
    Rconnection_close := Rconnection_close c ;
    Rconnection_destroy := destroy ;
    Rconnection_print := Rconnection_print c ;
    Rconnection_fflush := Rconnection_fflush c ;
    Rconnection_state := Rconnection_state c
  |}.

Definition Rconnection_with_print c print := {|
    Rconnection_class := Rconnection_class c ;
    Rconnection_description := Rconnection_description c ;
    Rconnection_mode := Rconnection_mode c ;
    Rconnection_text := Rconnection_text c ;
    Rconnection_isopen := Rconnection_isopen c ;
    Rconnection_incomplete := Rconnection_incomplete c ;
    Rconnection_canread := Rconnection_canread c ;
    Rconnection_canwrite := Rconnection_canwrite c ;
    Rconnection_canseek := Rconnection_canseek c ;
    Rconnection_blocking := Rconnection_blocking c ;
    Rconnection_isGzcon := Rconnection_isGzcon c ;
    Rconnection_open := Rconnection_open c ;
    Rconnection_close := Rconnection_close c ;
    Rconnection_destroy := Rconnection_destroy c ;
    Rconnection_print := print ;
    Rconnection_fflush := Rconnection_fflush c ;
    Rconnection_state := Rconnection_state c
  |}.

Definition Rconnection_with_fflush c fflush := {|
    Rconnection_class := Rconnection_class c ;
    Rconnection_description := Rconnection_description c ;
    Rconnection_mode := Rconnection_mode c ;
    Rconnection_text := Rconnection_text c ;
    Rconnection_isopen := Rconnection_isopen c ;
    Rconnection_incomplete := Rconnection_incomplete c ;
    Rconnection_canread := Rconnection_canread c ;
    Rconnection_canwrite := Rconnection_canwrite c ;
    Rconnection_canseek := Rconnection_canseek c ;
    Rconnection_blocking := Rconnection_blocking c ;
    Rconnection_isGzcon := Rconnection_isGzcon c ;
    Rconnection_open := Rconnection_open c ;
    Rconnection_close := Rconnection_close c ;
    Rconnection_destroy := Rconnection_destroy c ;
    Rconnection_print := Rconnection_print c ;
    Rconnection_fflush := fflush ;
    Rconnection_state := Rconnection_state c
  |}.

Definition Rconnection_with_external_state c A (state : A) := {|
    Rconnection_class := Rconnection_class c ;
    Rconnection_description := Rconnection_description c ;
    Rconnection_mode := Rconnection_mode c ;
    Rconnection_text := Rconnection_text c ;
    Rconnection_isopen := Rconnection_isopen c ;
    Rconnection_incomplete := Rconnection_incomplete c ;
    Rconnection_canread := Rconnection_canread c ;
    Rconnection_canwrite := Rconnection_canwrite c ;
    Rconnection_canseek := Rconnection_canseek c ;
    Rconnection_blocking := Rconnection_blocking c ;
    Rconnection_isGzcon := Rconnection_isGzcon c ;
    Rconnection_open := Rconnection_open c ;
    Rconnection_close := Rconnection_close c ;
    Rconnection_destroy := Rconnection_destroy c ;
    Rconnection_print := Rconnection_print c ;
    Rconnection_fflush := Rconnection_fflush c ;
    Rconnection_state := state
  |}.


(** We now resolve the indirection. **)
Definition interpret_open t (c : Rconnection) : option (Rconnection * bool) :=
  match t with
  | null_open => None
  end.

Definition interpret_close t (c : Rconnection) : option Rconnection :=
  match t with
  | null_close => Some (Rconnection_with_isopen c false)
  end.

Definition interpret_destroy t (c : Rconnection) : option Rconnection :=
  match t with
  | null_destroy => Some c
  end.

Parameters run_stdout_print run_stderr_print : Rconnection -> string -> option Rconnection.

Definition interpret_print t (c : Rconnection) str : option Rconnection :=
  match t with
  | null_print => None
  | stdout_print => run_stdout_print c str
  | stderr_print => run_stderr_print c str
  end.

Parameters run_stdout_flush run_stderr_flush : Rconnection -> option Rconnection.

Definition interpret_flush t (c : Rconnection) : option Rconnection :=
  match t with
  | null_flush => None
  | stdout_flush => run_stdout_flush c
  | stderr_flush => run_stderr_flush c
  end.

(** The following functions are translations from functions of main/connections.c. **)

Definition init_con description mode := {|
    Rconnection_class := "" ;
    Rconnection_description := description ;
    Rconnection_mode := mode ;
    Rconnection_isopen := false ;
    Rconnection_incomplete := false ;
    Rconnection_blocking := false ;
    Rconnection_isGzcon := false ;
    Rconnection_canread := true ;
    Rconnection_canwrite := true ;
    Rconnection_canseek := false ;
    Rconnection_text := true ;
    Rconnection_open := null_open ;
    Rconnection_close := null_close ;
    Rconnection_destroy := null_destroy ;
    Rconnection_print := null_print ;
    Rconnection_fflush := null_flush ;
    Rconnection_state := tt
  |}.

Definition newterminal description mode :=
  let c := init_con description mode in
  let c := Rconnection_with_isopen c true in
  let c := Rconnection_with_canread c (decide (mode = "r"%string)) in
  let c := Rconnection_with_canwrite c (decide (mode = "w"%string)) in
  c.


(** * A Model for R’s State **)

Record state := make_state {
    state_memory :> memory ;
    state_context : context ;
    R_ExitContext : option context ;
    R_SymbolTable : SEXP ;
    R_ReturnedValue : SEXP ;
    R_Connections : list Rconnection (** Simply [Connections] in main/connections.c. **) ;
    R_OutputCon : nat ;
    R_asymSymbol : list SEXP (** Simply [asymSymbol] in main/eval.c. **)
  }.

Definition R_GlobalContext := state_context.

Record state_same_except_for_memory S1 S2 := make_state_same_except_for_memory {
    state_same_except_for_memory_state_context :
      state_context S1 = state_context S2 ;
    state_same_except_for_memory_R_ExitContext :
      R_ExitContext S1 = R_ExitContext S2 ;
    state_same_except_for_memory_R_SymbolTable :
      R_SymbolTable S1 = R_SymbolTable S2 ;
    state_same_except_for_memory_R_ReturnedValue :
      R_ReturnedValue S1 = R_ReturnedValue S2 ;
    state_same_except_for_memory_R_Connections :
      R_Connections S1 = R_Connections S2 ;
    state_same_except_for_memory_R_OutputCon :
      R_OutputCon S1 = R_OutputCon S2 ;
    state_same_except_for_memory_R_asymSymbol :
      R_asymSymbol S1 = R_asymSymbol S2
  }.

Lemma state_same_except_for_memory_refl : forall S,
  state_same_except_for_memory S S.
Proof. introv. constructors*. Qed.

Lemma state_same_except_for_memory_trans : forall S1 S2 S3,
  state_same_except_for_memory S1 S2 ->
  state_same_except_for_memory S2 S3 ->
  state_same_except_for_memory S1 S3.
Proof. introv [E1] [E2]. constructors; etransitivity; eassumption. Qed.

Lemma state_same_except_for_memory_sym : forall S1 S2,
  state_same_except_for_memory S1 S2 ->
  state_same_except_for_memory S2 S1.
Proof. introv [E]. constructors*. Qed.

Lemma state_same_except_for_memory_eq : forall S1 S2,
  state_same_except_for_memory S1 S2 ->
  state_memory S1 = state_memory S2 ->
  S1 = S2.
Proof. introv [E1] E2. destruct S1, S2. simpls. substs. fequals. Qed.

Record state_equiv (S1 S2 : state) := make_state_equiv {
    state_equiv_memory : memory_equiv S1 S2 ;
    state_equiv_rest : state_same_except_for_memory S1 S2
  }.

Lemma state_equiv_refl : forall S,
  state_equiv S S.
Proof.
  introv. constructors.
  - apply~ memory_equiv_refl.
  - apply~ state_same_except_for_memory_refl.
Qed.

Lemma state_equiv_trans : forall S1 S2 S3,
  state_equiv S1 S2 ->
  state_equiv S2 S3 ->
  state_equiv S1 S3.
Proof.
  introv [E1 R1] [E2 R2]. constructors.
  - applys~ memory_equiv_trans E1 E2.
  - applys~ state_same_except_for_memory_trans R1 R2.
Qed.

Lemma state_equiv_sym : forall S1 S2,
  state_equiv S1 S2 ->
  state_equiv S2 S1.
Proof.
  introv [E R]. constructors.
  - applys~ memory_equiv_sym E.
  - applys~ state_same_except_for_memory_sym R.
Qed.

Definition state_with_memory S m := {|
    state_memory := m ;
    state_context := state_context S ;
    R_ExitContext := R_ExitContext S ;
    R_SymbolTable := R_SymbolTable S ;
    R_ReturnedValue := R_ReturnedValue S ;
    R_Connections := R_Connections S ;
    R_OutputCon := R_OutputCon S ;
    R_asymSymbol := R_asymSymbol S
  |}.

Lemma state_same_except_for_memory_state_with_memory : forall S m,
  state_same_except_for_memory S (state_with_memory S m).
Proof. introv. destruct S. constructors~. Qed.

Definition state_with_context S c := {|
    state_memory := state_memory S ;
    state_context := c ;
    R_ExitContext := R_ExitContext S ;
    R_SymbolTable := R_SymbolTable S ;
    R_ReturnedValue := R_ReturnedValue S ;
    R_Connections := R_Connections S ;
    R_OutputCon := R_OutputCon S ;
    R_asymSymbol := R_asymSymbol S
  |}.

Definition update_R_ExitContext S c := {|
    state_memory := state_memory S ;
    state_context := state_context S ;
    R_ExitContext := c ;
    R_SymbolTable := R_SymbolTable S ;
    R_ReturnedValue := R_ReturnedValue S ;
    R_Connections := R_Connections S ;
    R_OutputCon := R_OutputCon S ;
    R_asymSymbol := R_asymSymbol S
  |}.

Definition update_R_SymbolTable S p := {|
    state_memory := state_memory S ;
    state_context := state_context S ;
    R_ExitContext := R_ExitContext S ;
    R_SymbolTable := p ;
    R_ReturnedValue := R_ReturnedValue S ;
    R_Connections := R_Connections S ;
    R_OutputCon := R_OutputCon S ;
    R_asymSymbol := R_asymSymbol S
  |}.

Definition update_R_ReturnedValue S p := {|
    state_memory := state_memory S ;
    state_context := state_context S ;
    R_ExitContext := R_ExitContext S ;
    R_SymbolTable := R_SymbolTable S ;
    R_ReturnedValue := p ;
    R_Connections := R_Connections S ;
    R_OutputCon := R_OutputCon S ;
    R_asymSymbol := R_asymSymbol S
  |}.

Definition update_R_Connections S cs := {|
    state_memory := state_memory S ;
    state_context := state_context S ;
    R_ExitContext := R_ExitContext S ;
    R_SymbolTable := R_SymbolTable S ;
    R_ReturnedValue := R_ReturnedValue S ;
    R_Connections := cs ;
    R_OutputCon := R_OutputCon S ;
    R_asymSymbol := R_asymSymbol S
  |}.

Definition update_R_OutputCon S outputCon := {|
    state_memory := state_memory S ;
    state_context := state_context S ;
    R_ExitContext := R_ExitContext S ;
    R_SymbolTable := R_SymbolTable S ;
    R_ReturnedValue := R_ReturnedValue S ;
    R_Connections := R_Connections S ;
    R_OutputCon := outputCon ;
    R_asymSymbol := R_asymSymbol S
  |}.

Definition update_R_asymSymbol S asl := {|
    state_memory := state_memory S ;
    state_context := state_context S ;
    R_ExitContext := R_ExitContext S ;
    R_SymbolTable := R_SymbolTable S ;
    R_ReturnedValue := R_ReturnedValue S ;
    R_Connections := R_Connections S ;
    R_OutputCon := R_OutputCon S ;
    R_asymSymbol := asl
  |}.


(** Wrapping up with the functions defined in the previous section. **)

Definition alloc_SExp (S : state) e_ :=
  let (m, e) := alloc_memory_SExp S e_ in
  (state_with_memory S m, e).

Definition write_SExp (S : state) e e_ :=
  match write_memory_SExp S e e_ with
  | Some m => Some (state_with_memory S m)
  | None => None
  end.

Lemma write_read_SExp_None : forall S p e_,
  write_SExp S p e_ = None ->
  read_SExp S p = None.
Proof.
  introv E. unfolds in E. destruct write_memory_SExp eqn: E'; inverts E.
  applys~ write_memory_SExp_read_SExp_None E'.
Qed.

Lemma read_write_SExp_None : forall (S : state) p e_,
  read_SExp S p = None ->
  write_SExp S p e_ = None.
Proof. introv E. unfolds. rewrite~ read_SExp_write_memory_SExp_None. Qed.

Lemma alloc_read_SExp_Some : forall S1 S2 e e_,
  alloc_SExp S1 e_ = (S2, e) ->
  read_SExp S2 e = Some e_.
Proof.
  introv E. unfolds in E. destruct alloc_memory_SExp eqn: E'. inverts E.
  apply~ alloc_memory_SExp_read_SExp. rewrite* E'.
Qed.

Lemma alloc_write_SExp_not_None : forall S1 S2 e e1_ e2_,
  alloc_SExp S1 e1_ = (S2, e) ->
  write_SExp S2 e e2_ <> None.
Proof.
  introv E1 E2. lets E3: write_read_SExp_None E2.
  lets E4: alloc_read_SExp_Some E1. rewrite E3 in E4. inverts E4.
Qed.

Lemma read_write_SExp_eq : forall (S S' : state) p e_,
  write_SExp S p e_ = Some S' ->
  read_SExp S' p = Some e_.
Proof.
  introv W. unfolds in W. destruct write_memory_SExp eqn:E; inverts W.
  apply* write_memory_SExp_read_SExp_same.
Qed.

Lemma read_write_SExp_neq : forall (S S' : state) p1 p2 e_,
  write_SExp S p1 e_ = Some S' ->
  p1 <> p2 ->
  read_SExp S' p2 = read_SExp S p2.
Proof.
  introv W D. unfolds in W. destruct write_memory_SExp eqn:E; inverts W.
  applys* write_memory_SExp_read_SExp D.
Qed.

Lemma alloc_read_SExp_neq : forall S1 S2 e1 e2 e_,
  alloc_SExp S1 e_ = (S2, e2) ->
  e1 <> e2 ->
  read_SExp S2 e1 = read_SExp S1 e1.
Proof.
  introv A D. inverts A. unfolds. simpl. destruct~ e1.
  unfolds read_SExp_nat. simpl. apply* read_option_write.
Qed.

Lemma alloc_read_SExp_fresh : forall S S' e e_,
  alloc_SExp S e_ = (S', e) ->
  read_SExp S e = None.
Proof.
  introv A. inverts A. simpl. apply not_indom_read_option.
  rewrite stream_head_nth. apply* state_fresh_locations_fresh.
Qed.

Lemma alloc_read_SExp_eq : forall S S' e e_,
  alloc_SExp S e_ = (S', e) ->
  read_SExp S' e = Some e_.
Proof. introv A. inverts A. apply read_option_write_same. Qed.

Lemma alloc_read_SExp_diff : forall S S' p p' p_ p'_,
  alloc_SExp S p_ = (S', p) ->
  read_SExp S p' = Some p'_ ->
  p <> p'.
Proof. introv A E N. substs. rewrite (alloc_read_SExp_fresh A) in E. inverts~ E. Qed.

Lemma read_write_SExp_Some : forall (S : state) p p_ p_',
  read_SExp S p = Some p_ ->
  exists S', write_SExp S p p_' = Some S'.
Proof.
  introv E. unfolds write_SExp. lets (S'&E'): read_SExp_write_memory_SExp E.
  rewrite* E'.
Qed.

Lemma write_read_SExp_Some : forall S S' p p_,
  write_SExp S p p_ = Some S' ->
  exists p_', read_SExp S p = Some p_'.
Proof.
  introv W. destruct read_SExp eqn: R.
  - exists*.
  - rewrite~ read_write_SExp_None in W. inverts W.
Qed.

Lemma write_SExp_NULL : forall S p_,
  write_SExp S NULL p_ = None.
Proof. reflexivity. Qed.

Lemma alloc_SExp_equiv : forall S1 S2 S1' S2' e1 e2 e_,
  state_equiv S1 S2 ->
  alloc_SExp S1 e_ = (S1', e1) ->
  alloc_SExp S2 e_ = (S2', e2) ->
  e1 = e2 /\ state_equiv S1' S2'.
Proof.
  introv E A1 A2. unfolds alloc_SExp.
  destruct (alloc_memory_SExp S1) as [S1'' e1'] eqn: A1'. inverts A1.
  destruct (alloc_memory_SExp S2) as [S2'' e2'] eqn: A2'. inverts A2.
  forwards~ (Ee&ES): alloc_memory_SExp_equiv A1' A2'.
  - applys~ state_equiv_memory E.
  - subst. splits~. constructors~.
    applys~ state_same_except_for_memory_trans S1.
    { apply~ state_same_except_for_memory_sym.
      apply state_same_except_for_memory_state_with_memory. }
    applys~ state_same_except_for_memory_trans E.
    apply state_same_except_for_memory_state_with_memory.
Qed.

Lemma write_SExp_equiv : forall S1 S2 S1' S2' e e_,
  state_equiv S1 S2 ->
  write_SExp S1 e e_ = Some S1' ->
  write_SExp S2 e e_ = Some S2' ->
  state_equiv S1' S2'.
Proof.
  introv E W1 W2. unfolds write_SExp.
  destruct (write_memory_SExp S1) eqn: W1'; inverts W1.
  destruct (write_memory_SExp S2) eqn: W2'; inverts W2.
  forwards~ ES: write_memory_SExp_equiv W1' W2'.
  - applys~ state_equiv_memory E.
  - subst. constructors~.
    applys~ state_same_except_for_memory_trans S1.
    { apply~ state_same_except_for_memory_sym.
      apply state_same_except_for_memory_state_with_memory. }
    applys~ state_same_except_for_memory_trans E.
    apply state_same_except_for_memory_state_with_memory.
Qed.

Lemma write_SExp_equiv_exists : forall S1 S2 S1' e e_,
  state_equiv S1 S2 ->
  write_SExp S1 e e_ = Some S1' ->
  exists S2',
    write_SExp S2 e e_ = Some S2'
    /\ state_equiv S1' S2'.
Proof.
  introv E W1. forwards (e_'&Ee_): write_read_SExp_Some W1.
  rewrites >> read_SExp_equiv E in Ee_.
  forwards (S2'&W2): read_write_SExp_Some Ee_. exists S2'. splits*.
  applys* write_SExp_equiv E W1 W2.
Qed.

Lemma write_SExp_write_SExp_eq : forall S1 S2 S3 p p_1 p_2,
  write_SExp S1 p p_1 = Some S2 ->
  write_SExp S2 p p_2 = Some S3 ->
  exists S3',
    write_SExp S1 p p_2 = Some S3'
    /\ state_equiv S3 S3'.
Proof.
  introv W1 W2. unfolds write_SExp.
  destruct (write_memory_SExp S1 p p_1) eqn: W1'; tryfalse.
  destruct (write_memory_SExp S2 p p_2) eqn: W2'; tryfalse.
  inverts W1. inverts W2.
  forwards~ (S3'&W'&E): write_memory_SExp_write_memory_SExp_eq W1' W2'.
  rewrite W'. eexists. splits*. constructors~.
  applys~ state_same_except_for_memory_trans S1.
  { apply~ state_same_except_for_memory_sym.
    applys~ state_same_except_for_memory_trans state_same_except_for_memory_state_with_memory.
    apply state_same_except_for_memory_state_with_memory. }
  apply state_same_except_for_memory_state_with_memory.
Qed.

Lemma write_SExp_write_SExp_neq : forall S1 S2 S3 p1 p2 p_1 p_2,
  p1 <> p2 ->
  write_SExp S1 p1 p_1 = Some S2 ->
  write_SExp S2 p2 p_2 = Some S3 ->
  exists S2' S3',
    write_SExp S1 p2 p_2 = Some S2'
    /\ write_SExp S2' p1 p_1 = Some S3'
    /\ state_equiv S3 S3'.
Proof.
  introv D W1 W2. unfolds write_SExp.
  destruct (write_memory_SExp S1 p1 p_1) eqn: W1'; tryfalse.
  destruct (write_memory_SExp S2 p2 p_2) eqn: W2'; tryfalse.
  inverts W1. inverts W2.
  forwards~ (S2'&S3'&W1&W2&E): write_memory_SExp_write_memory_SExp_neq W1' W2'.
  rewrite W1. do 2 eexists. splits*.
  - simpl. rewrite* W2.
  - simpls~. constructors~.
    applys~ state_same_except_for_memory_trans S1.
    { apply~ state_same_except_for_memory_sym.
      applys~ state_same_except_for_memory_trans state_same_except_for_memory_state_with_memory.
      apply state_same_except_for_memory_state_with_memory. }
    applys~ state_same_except_for_memory_trans state_same_except_for_memory_state_with_memory.
    apply state_same_except_for_memory_state_with_memory.
Qed.

Lemma alloc_SExp_write_SExp_eq : forall S1 S2 S3 p p_1 p_2,
  alloc_SExp S1 p_1 = (S2, p) ->
  write_SExp S2 p p_2 = Some S3 ->
  exists S3',
    alloc_SExp S1 p_2 = (S3', p)
    /\ state_equiv S3 S3'.
Proof.
  introv A W. unfolds write_SExp.
  destruct (write_memory_SExp S2 p p_2) eqn: W'; tryfalse. inverts W.
  forwards~ (S3'&A'&E): alloc_memory_SExp_write_memory_SExp_eq W'.
  - inverts A. reflexivity.
  - unfolds alloc_SExp. rewrite A'. eexists. splits*.
    constructors~. destruct alloc_memory_SExp in A. inverts A.
    applys~ state_same_except_for_memory_trans S1.
    { apply~ state_same_except_for_memory_sym.
      applys~ state_same_except_for_memory_trans state_same_except_for_memory_state_with_memory.
      apply state_same_except_for_memory_state_with_memory. }
    apply state_same_except_for_memory_state_with_memory.
Qed.

Lemma alloc_SExp_write_SExp_neq : forall S1 S2 S3 p1 p2 p_1 p_2,
  p1 <> p2 ->
  alloc_SExp S1 p_1 = (S2, p1) ->
  write_SExp S2 p2 p_2 = Some S3 ->
  exists S2' S3',
    write_SExp S1 p2 p_2 = Some S2'
    /\ alloc_SExp S2' p_1 = (S3', p1)
    /\ state_equiv S3 S3'.
Proof.
  introv D A W. unfolds write_SExp.
  destruct (write_memory_SExp S2 p2 p_2) eqn: W'; tryfalse. inverts W.
  forwards~ (S2'&S3'&W&A'&E): alloc_memory_SExp_write_memory_SExp_neq D W'.
  - inverts A. reflexivity.
  - rewrite W. do 2 eexists. splits*.
    + inverts A'. reflexivity.
    + constructors~. unfolds in A. destruct alloc_memory_SExp in A. inverts A.
      applys~ state_same_except_for_memory_trans S1.
      { apply~ state_same_except_for_memory_sym.
        applys~ state_same_except_for_memory_trans state_same_except_for_memory_state_with_memory.
        apply state_same_except_for_memory_state_with_memory. }
      applys~ state_same_except_for_memory_trans state_same_except_for_memory_state_with_memory.
      apply state_same_except_for_memory_state_with_memory.
Qed.


(** * Initial Memory **)

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


(** * Generic Instances **)

Instance memory_Inhab : Inhab memory :=
  prove_Inhab empty_memory.

Instance context_Inhab : Inhab context.
  apply prove_Inhab. constructors; typeclass || apply arbitrary.
Qed.

Instance state_Rconnection : Inhab Rconnection.
  apply prove_Inhab. apply (newterminal "dummy" "???").
Qed.

Instance state_Inhab : Inhab state.
  apply prove_Inhab. constructors; typeclass || apply arbitrary.
Qed.

