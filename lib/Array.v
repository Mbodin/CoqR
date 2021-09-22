(** Arrays are important in R.
  This file provide a simple functional interface.
  We define arrays as lists for simplicity, but we extract them differently for efficiency. **)

Set Implicit Arguments.

From TLC Require Export LibNat LibContainer.
Require Import Heap.
Require Export Common.

(** * Module Type Definition **)

Module Type ArraySpec.

Parameter array : Type -> Type.

Parameter length : forall T, array T -> nat.

Parameter read_option : forall T, array T -> nat -> option T.

Parameter write : forall T, array T -> nat -> T -> array T.

Parameter empty : forall T, array T.

Parameter map : forall T1 T2, (T1 -> T2) -> array T1 -> array T2.

Parameter from_list : forall T, list T -> array T.
Parameter to_list : forall T, array T -> list T.

Parameter read_option_Some_exists : forall T (a : array T) n,
  n < length a ->
  exists v, read_option a n = Some v.

Parameter read_option_None : forall T (a : array T) n,
  n >= length a ->
  read_option a n = None.

Parameter read_option_write_eq : forall T a (t : T) n,
  n < length a ->
  read_option (write a n t) n = Some t.

Parameter read_option_write_neq : forall T a (t : T) n1 n2,
  n2 < length a ->
  n1 <> n2 ->
  read_option (write a n1 t) n2 = read_option a n2.

Parameter write_length : forall T a (t : T) n,
  length (write a n t) = length a.

Parameter empty_length : forall T,
  length (@empty T) = 0.

Parameter from_list_length : forall T (l : list T),
  length (from_list l) = LibList.length l.

Parameter to_list_length : forall T (a : array T),
  LibList.length (to_list a) = length a.

Parameter from_list_read_option : forall T (l : list T) n,
  read_option (from_list l) n = nth_option n l.

Parameter to_list_read_option : forall T (a : array T) n,
  nth_option n (to_list a) = read_option a n.

Parameter map_length : forall T1 T2 (f : T1 -> T2) a,
  length (map f a) = length a.

Parameter map_read_option : forall T1 T2 (f : T1 -> T2) a n v,
  read_option a n = Some v ->
  read_option (map f a) n = Some (f v).

End ArraySpec.


Module ArrayExtra (A : ArraySpec).

Include A.

Instance bagCard T : BagCard (array T) := {|
    card := @length T
  |}.

Instance bagReadOption T : BagReadOption nat T (array T) := {|
    Heap.read_option := @read_option T
  |}.
Instance bagRead T `{Inhab T} : BagRead nat T (array T) :=
  ReadOptionToRead nat T (array T).

Instance bagUpdate T : BagUpdate nat T (array T) := {|
    LibContainer.update a n t := write a n t
  |}.

Instance bagEmpty T : BagEmpty (array T) := {|
   LibContainer.empty := empty T
 |}.

Lemma read_option_Some : forall T `{Inhab T} (a : array T) n,
  n < length a ->
  read_option a n = Some (read a n).
Proof.
  introv I. forwards~ (v&E): read_option_Some_exists I.
  simpl. rewrite~ E.
Qed.

Lemma None_read_option : forall T (a : array T) n,
  read_option a n = None ->
  n >= length a.
Proof.
  introv E. tests~: (n >= length a).
  forwards (v&Ev): read_option_Some_exists a n. { nat_math. }
  rewrite Ev in E. inverts E.
Qed.

Lemma read_write_eq : forall T `{Inhab T} a (t : T) n,
  n < length a ->
  read (write a n t) n = t.
Proof. introv I. unfold write. simpl. rewrite~ read_option_write_eq. Qed.

Lemma read_write_neq : forall T `{Inhab T} a (t : T) n1 n2,
  n2 < length a ->
  n1 <> n2 ->
  read (write a n1 t) n2 = read a n2.
Proof. introv I D. unfold write. simpl. rewrite~ read_option_write_neq. Qed.

Lemma from_list_read : forall T `{Inhab T} (l : list T) n,
  n < LibList.length l ->
  read (from_list l) n = nth n l.
Proof.
  introv I. lets E: (from_list_read_option l n).
  rewrite read_option_Some with (H := H) in E.
  - symmetry in E. apply nth_option_defined with (H := H) in E. rewrite~ <- E.
  - rewrite~ from_list_length.
Qed.

Lemma to_list_read : forall T `{Inhab T} (a : array T) n,
  n < length a ->
  nth n (to_list a) = read a n.
Proof.
  introv I. lets E: (to_list_read_option a n).
  rewrite read_option_Some with (H := H) in E; autos~.
  apply nth_option_defined with (H := H) in E; autos~.
Qed.

Lemma map_read : forall T1 T2 `{Inhab T1} `{Inhab T2} (f : T1 -> T2) a n,
  n < length a ->
  read (map f a) n = f (read a n).
Proof.
  introv I. forwards E1: read_option_Some I. forwards E2: map_read_option f E1.
  rewrite <- (map_length f) in I. forwards E3: read_option_Some I.
  rewrite E3 in E2. inverts~ E2.
Qed.

End ArrayExtra.


(** * Implementation **)

Module ArrayList : ArraySpec.

Definition array T := list T.

Definition length : forall T, array T -> nat := length.

Definition read_option T (a : array T) n := nth_option n a.

Definition write {T} (a : array T) n t := update n t a.

Definition from_list T := id : list T -> array T.
Definition to_list T := id : array T -> list T.

Definition empty T : array T := nil.

Definition map : forall T1 T2, (T1 -> T2) -> array T1 -> array T2 := LibList.map.

Lemma read_option_Some_exists : forall T (a : array T) n,
  n < length a ->
  exists v, read_option a n = Some v.
Proof.
  introv I. destruct read_option eqn: E.
  - autos*.
  - unfolds in E. apply nth_option_length in E. unfolds length. nat_math.
Qed.

Lemma read_option_None : forall T (a : array T) n,
  n >= length a ->
  read_option a n = None.
Proof. introv I. apply~ nth_option_length. Qed.

Lemma read_option_write_eq : forall T a (t : T) n,
  n < length a ->
  read_option (write a n t) n = Some t.
Proof. introv I. apply~ nth_option_update_eq. Qed.

Lemma read_option_write_neq : forall T a (t : T) n1 n2,
  n2 < length a ->
  n1 <> n2 ->
  read_option (write a n1 t) n2 = read_option a n2.
Proof.
  introv I D. tests I': (n1 < length a).
  - apply~ nth_option_update_neq.
  - fequals. unfold write. apply~ update_out. unfolds length. nat_math.
Qed.

Lemma write_length : forall T a (t : T) n,
  length (write a n t) = length a.
Proof. introv. apply~ length_update. Qed.

Lemma from_list_length : forall T (l : list T),
  length (from_list l) = LibList.length l.
Proof. reflexivity. Qed.

Lemma to_list_length : forall T (a : array T),
  LibList.length (to_list a) = length a.
Proof. reflexivity. Qed.

Lemma empty_length : forall T,
  length (empty T) = 0.
Proof. reflexivity. Qed.

Lemma from_list_read_option : forall T (l : list T) n,
  read_option (from_list l) n = nth_option n l.
Proof. reflexivity. Qed.

Lemma to_list_read_option : forall T (a : array T) n,
  nth_option n (to_list a) = read_option a n.
Proof. reflexivity. Qed.

Lemma map_length : forall T1 T2 (f : T1 -> T2) a,
  length (map f a) = length a.
Proof. introv. apply~ length_map. Qed.

Lemma map_read_option : forall T1 T2 (f : T1 -> T2) a n v,
  read_option a n = Some v ->
  read_option (map f a) n = Some (f v).
Proof. introv E. apply Nth_nth_option in E. apply Nth_nth_option. applys~ map_Nth E. Qed.

End ArrayList.


Module ArrayListExtra := ArrayExtra (ArrayList).

