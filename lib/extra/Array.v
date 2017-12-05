(** Arrays are important in R.
  This file provide a simple functional interface.
  We define arrays as lists for simplicity, but we extract them differently for efficiency. **)

Set Implicit Arguments.

Require Export Shared TLC.LibNat.

(** * Module Type Definition **)

Module Type ArraySpec.

Parameter array : Type -> Type.

Parameter length : forall T, array T -> nat.

Parameter read : forall T `{Inhab T}, array T -> nat -> T.
Parameter write : forall T, array T -> nat -> T -> array T.

Parameter from_list : forall T, list T -> array T.
Parameter to_list : forall T, array T -> list T.

Parameter read_write_eq : forall T `{Inhab T} a (t : T) n,
  n < length a ->
  read (write a n t) n = t.

Parameter read_write_neq : forall T `{Inhab T} a (t : T) n1 n2,
  n2 < length a ->
  n1 <> n2 ->
  read (write a n1 t) n2 = read a n2.

Parameter write_length : forall T a (t : T) n,
  length (write a n t) = length a.

Parameter from_list_length : forall T (l : list T),
  length (from_list l) = LibList.length l.

Parameter to_list_length : forall T (a : array T),
  LibList.length (to_list a) = length a.

Parameter from_list_read : forall T `{Inhab T} (l : list T) n,
  read (from_list l) n = nth n l.

Parameter to_list_read : forall T `{Inhab T} (a : array T) n,
  nth n (to_list a) = read a n.

End ArraySpec.


Module Type ArrayExtra (A : ArraySpec).

Import A.

Parameter map : forall T1 T2, (T1 -> T2) -> array T1 -> array T2.

Parameter map_length : forall T1 T2 (f : T1 -> T2) a,
  length (map f a) = length a.

Parameter map_read : forall T1 T2 `{Inhab T1} `{Inhab T2} (f : T1 -> T2) a n,
  n < length a ->
  read (map f a) n = f (read a n).

End ArrayExtra.


(** * Implementation **)

Module ArrayList <: ArraySpec.

Definition array := list.

Definition length T := length : array T -> nat.

Definition read T `{Inhab T} (a : array T) n := nth n a.
Definition write T (a : array T) n t := update n t a : array T.

Definition from_list T := id : list T -> array T.
Definition to_list T := id : array T -> list T.

Lemma read_write_eq : forall T `{Inhab T} a (t : T) n,
  n < length a ->
  read (write a n t) n = t.
Proof. introv I. apply nth_update_eq. unfolds length. nat_math. Qed.

Lemma read_write_neq : forall T `{Inhab T} a (t : T) n1 n2,
  n2 < length a ->
  n1 <> n2 ->
  read (write a n1 t) n2 = read a n2.
Proof. introv I D. applys nth_update_neq D. unfolds length. nat_math. Qed.

Lemma write_length : forall T a (t : T) n,
  length (write a n t) = length a.
Proof. introv. apply length_update. Qed.

Lemma from_list_length : forall T (l : list T),
  length (from_list l) = LibList.length l.
Proof. reflexivity. Qed.

Lemma to_list_length : forall T (a : array T),
  LibList.length (to_list a) = length a.
Proof. reflexivity. Qed.

Lemma from_list_read : forall T `{Inhab T} (l : list T) n,
  read (from_list l) n = nth n l.
Proof. reflexivity. Qed.

Lemma to_list_read : forall T `{Inhab T} (a : array T) n,
  nth n (to_list a) = read a n.
Proof. reflexivity. Qed.

End ArrayList.


Module ArrayListExtra <: ArrayExtra (ArrayList).

Export ArrayList.

Definition map : forall T1 T2, (T1 -> T2) -> array T1 -> array T2 := LibList.map.

Lemma map_length : forall T1 T2 (f : T1 -> T2) a,
  length (map f a) = length a.
Proof. introv. apply length_map. Qed.

Lemma map_read : forall T1 T2 `{Inhab T1} `{Inhab T2} (f : T1 -> T2) a n,
  n < length a ->
  read (map f a) n = f (read a n).
Proof. introv I. apply~ map_nth. Qed.

End ArrayListExtra.

