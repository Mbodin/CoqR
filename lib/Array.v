(** Arrays are important in R.
  This file provide a simple functional interface.
  We define arrays as lists for simplicity, but we extract them differently for efficiency. **)

Set Implicit Arguments.

Require Export Shared TLC.LibNat.

Module Type ArraySpec.

Parameter array : Type -> Type.

Parameter length : forall T, array T -> nat.

Parameter read : forall T, array T -> nat -> option T.
Parameter write : forall T, array T -> nat -> T -> array T.

Parameter from_list : forall T, list T -> array T.
Parameter to_list : forall T, array T -> list T.

Parameter read_defined : forall T (a : array T) n,
  n < length a ->
  exists t, read a n = Some t.

Parameter read_write_eq : forall T a (t : T) n,
  n < length a ->
  read (write a n t) n = Some t.

Parameter read_write_neq : forall T a (t : T) n1 n2,
  n1 <> n2 ->
  read (write a n1 t) n2 = read a n2.

Parameter write_length : forall T a (t : T) n,
  length (write a n t) = length a.

Parameter from_list_length : forall T (l : list T),
  length (from_list l) = LibList.length l.

Parameter to_list_length : forall T (a : array T),
  LibList.length (to_list a) = length a.

Parameter from_list_read : forall T (l : list T) n,
  read (from_list l) n = nth_option n l.

Parameter to_list_read : forall T (a : array T) n,
  nth_option n (to_list a) = read a n.

End ArraySpec.

Module Array : ArraySpec.

Definition array := list.

Definition length T := length : array T -> nat.

Definition read T (a : array T) n := nth_option n a.
Definition write T a n (t : T) := update n t a.

Definition from_list T := id : list T -> array T.
Definition to_list T := id : array T -> list T.


Lemma read_defined : forall T (a : array T) n,
  n < length a ->
  exists t, read a n = Some t.
Proof.
  introv I. destruct (read a n) eqn: E.
  - exists*.
  - apply nth_option_length in E. unfolds length. nat_math.
Qed.

Lemma read_write_eq : forall T a (t : T) n,
  n < length a ->
  read (write a n t) n = Some t.
Proof.
  introv I. destruct (read a n) eqn: E.
  - apply nth_option_defined in E. rewrite nth_update_eq.
  - apply nth_option_length in E. unfolds length. nat_math.
Qed.

Lemma read_write_neq : forall T a (t : T) n1 n2,
  n1 <> n2 ->
  read (write a n1 t) n2 = read a n2.
Proof.
Qed.

Lemma write_length : forall T a (t : T) n,
  length (write a n t) = length a.
Proof.
Qed.

Lemma from_list_length : forall T (l : list T),
  length (from_list l) = LibList.length l.
Proof.
Qed.

Lemma to_list_length : forall T (a : array T),
  LibList.length (to_list a) = length a.
Proof.
Qed.

Lemma from_list_read : forall T (l : list T) n,
  read (from_list l) n = nth_option n l.
Proof.
Qed.

Lemma to_list_read : forall T (a : array T) n,
  nth_option n (to_list a) = read a n.
Proof.
Qed.

End Array.
