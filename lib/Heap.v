(** An instanciation of heaps.
  It is based on the AVL-tree implementation from the standard library. **)

From Coq Require Import OrderedTypeEx FSets.FMapAVL.
From Lib Require Import LibExec.
From TLC Require Export LibTactics LibReflect LibContainer.


(** * Addition to LibContainer about read_option **)

(** ** Definitions **)

Class BagReadOption A B T := { read_option : T -> A -> option B }.

Class BagInDec A T := {
    bag_in :> BagIn A T ;
    bag_in_dec :> forall a (t : T), Decidable (a \in t)
  }.

(** The class [In_remove_eq] is about removal of a subset of a set/map.
  This other typeclass is about removal of an element. **)
Class In_remove_elem {A T : Type} (Eq : LibRelation.binary A) {BI : BagIn A T} {BR : BagRemove T A} := {
    in_remove_elem : forall x y E, x \in E \- y <-> (x \in E /\ ~ Eq x y)
  }.

(** ** Properties **)

Section Properties.

Context {A B T D : Type}
  {BI : BagIn A T} {BE : BagEmpty T} {BB : BagBinds A B T} {BD : BagDom T D}
  {BR : BagRead A B T} {BRO : BagReadOption A B T}.

Class ReadOption_In_eq := {
    read_option_in_eq : forall a t, a \notin t -> read_option t a = None
  }.

Class ReadOption_Read_eq := {
    read_option_read_eq : forall a b t, read_option t a = Some b -> read t a = b
  }.

Class In_Binds_eq := {
    in_binds_eq : forall a t, a \in t <-> exists b, binds t a b
  }.

Class ReadOption_Binds_eq := {
    read_option_binds_eq : forall a b t, binds t a b <-> read_option t a = Some b
  }.

End Properties.


(** ** Conversions **)

Definition ReadOptionToRead A B T `{BagReadOption A B T} `{Inhab B} : BagRead A B T := {|
    read t a :=
      match read_option t a with
      | None => arbitrary
      | Some b => b
      end
  |}.

Instance ReadOptionToRead_ReadOption_Read_eq : forall A B T `{BagReadOption A B T} `{Inhab B},
  ReadOption_Read_eq (BR := ReadOptionToRead A B T).
Proof.
  constructors. introv E. simpl. rewrite~ E.
Qed.

Definition ReadOptionToIn A B T `{BagReadOption A B T} : BagIn A T := {|
    is_in a t :=
      istrue match read_option t a with
      | None => false
      | Some _ => true
      end
  |}.

Definition ReadOptionToInDec A B T `{BagReadOption A B T} : BagInDec A T := {|
    bag_in := ReadOptionToIn A B T ;
    bag_in_dec _ _ := bool_decidable _
  |}.

Instance ReadOptionToIn_ReadOption_In_eq : forall A B T `{BagReadOption A B T},
  ReadOption_In_eq (BI := ReadOptionToIn A B T).
Proof.
  constructors. unfold notin. simpl. introv N.
  destruct~ read_option. false* N.
Qed.

Definition ReadToReadOption A B T `{BagRead A B T} `{BagInDec A T} : BagReadOption A B T := {|
    read_option t a :=
      ifb a \in t then Some (read t a) else None
  |}.

Instance ReadToReadOption_ReadOption_Read_eq : forall A B T `{BagRead A B T} `{BagInDec A T},
  ReadOption_Read_eq (BRO := ReadToReadOption A B T).
Proof.
  constructors. simpl. introv E. cases_if; inverts~ E.
Qed.

Instance ReadToReadOption_ReadOption_In_eq : forall A B T `{BagRead A B T} `{BagInDec A T},
  ReadOption_In_eq (BRO := ReadToReadOption A B T).
Proof.
  constructors. simpl. introv E. cases_if as D; autos~.
  rewrite decide_spec in D. rew_istrue in D. false~ E.
Qed.

Definition ReadOptionToBinds A B T `{BagReadOption A B T} : BagBinds A B T := {|
    binds t a b :=
      read_option t a = Some b
  |}.

Instance ReadOptionToBinds_ReadOption_Binds_eq : forall A B T `{BagReadOption A B T},
  ReadOption_Binds_eq (BB := ReadOptionToBinds A B T).
Proof.
  constructors*.
Qed.

(* TODO: empty + update => single *)

(* TODO: class update vs read (eq and neq) *)


(** * Instanciation of heaps **)

Module HeapFromOrdered (X : OrderedType.OrderedType).

Export X.

(** ** Definitions and instance **)

Definition K := t.

Module Import Tree := FMapAVL.Make(X).

Definition t T := Tree.t T.

Instance read_option_inst V : BagReadOption K V (t V) := {|
    read_option h k := find k h
  |}.

Instance read_inst V `{Inhab V} : BagRead K V (t V) :=
  ReadOptionToRead K V _.

Instance in_inst V : BagIn K (t V) :=
  ReadOptionToIn K V _.

Instance in_dec_inst V : BagInDec K (t V) :=
  ReadOptionToInDec K V _.

Instance binds_inst V : BagBinds K V (t V) :=
  ReadOptionToBinds K V _.

Instance empty_inst V : BagEmpty (t V) := {|
    LibContainer.empty := Tree.empty V
  |}.

Instance update_inst V : BagUpdate K V (t V) := {|
    update h k v := add k v h
  |}.

(* Alternative name *)
Definition write {V} : t V -> K -> V -> t V := update.

Instance remove_inst V : BagRemove (t V) K := {|
    LibContainer.remove h k := Tree.remove k h
  |}.

Instance fold_inst V I : BagFold I (K -> V -> I) (t V) := {|
    LibContainer.fold m f h :=
      Tree.fold
        (fun k v acc => LibMonoid.monoid_oper m (f k v) acc)
        h
        (LibMonoid.monoid_neutral m)
  |}.

Instance card_inst V : BagCard (t V) := {|
    card := @cardinal _
  |}.

(* TODO: single, dom, incl *)

Instance in_empty_eq V : In_empty_eq (T := t V).
Proof. constructors*. Qed.

(** ** Lemmas **)

Lemma MapsTo_In : forall V (h : t V) k v,
  MapsTo k v h ->
  In k h.
Proof. introv M. constructors*. Qed.

Instance in_remove_elem V : In_remove_elem (T := t V) eq.
Proof.
  constructors. intros x y h. simpl. destruct (eq_dec x y) as [E|E].
  - symmetry in E. forwards nI: remove_1 h E. destruct find eqn: B.
    + forwards M1: find_2 B. forwards M2: remove_3 M1.
      forwards M3: find_1 M2. false nI. apply* MapsTo_In.
    + destruct (find x h) eqn: B'.
      * forwards M1: find_2 B'. split~. intros (_&N).
        forwards M2: remove_2 M1.
        { introv nE. apply N. symmetry. apply~ nE. }
        forwards E': find_1 M2. rewrite B in E'. inverts E'.
      * autos*.
  - destruct find eqn: B.
    + forwards M1: find_2 B. forwards M2: remove_3 M1.
      forwards M3: find_1 M2. rewrite* M3.
    + destruct (find x h) eqn: B'.
      * forwards M1: find_2 B'. split~. intros (_&N).
        forwards M2: remove_2 M1.
        { introv nE. apply N. symmetry. apply~ nE. }
        forwards E': find_1 M2. rewrite B in E'. inverts E'.
      * autos*.
Qed.

Instance in_binds_eq V : In_Binds_eq (T := t V).
Proof.
  constructors. intros k h. simpl. destruct find eqn: E.
  - autos*.
  - iff I; repeat inverts I as I.
Qed.

Lemma read_option_binds : forall V (h : t V) k v,
  read_option h k = Some v ->
  binds h k v.
Proof. autos~. Qed.

Lemma binds_indom : forall V (h : t V) k v,
  binds h k v ->
  k \in h.
Proof. simpl. introv E. rewrite~ E. Qed.

Lemma read_option_indom : forall V (h : t V) k v,
  read_option h k = Some v ->
  k \in h.
Proof. introv E. apply~ binds_indom. applys~ read_option_binds E. Qed.

Lemma indom_binds : forall V (h : t V) k,
  k \in h ->
  exists v, binds h k v.
Proof.
  simpl. introv I. destruct find; tryfalse. eexists. autos*.
Qed.

Lemma binds_read_option : forall V (h : t V) k v,
  binds h k v ->
  read_option h k = Some v.
Proof.
  introv B. rewrite read_option_binds_eq in B. autos~.
Qed.

Lemma indom_read_option : forall V (h : t V) k,
  k \in h ->
  exists v, read_option h k = Some v.
Proof.
  introv I. forwards (v&B): @indom_binds I.
  exists v. applys~ @binds_read_option B.
Qed.

Lemma read_option_write_eq : forall V (h : t V) k k' v,
  eq k k' ->
  read_option (write h k v) k' = Some v.
Proof.
  introv E. apply binds_read_option. simpl.
  applys~ find_1. applys~ add_1.
Qed.

Lemma not_indom_write : forall V (h : t V) k k' v',
  ~ eq k k' ->
  ~ k \in h ->
  ~ k \in (write h k' v').
Proof.
  simpl. introv D I1 I2. destruct find eqn:E1 in I1; tryfalse.
  destruct find eqn:E2 in I2; tryfalse.
  forwards M2: find_2 E2. forwards~ M1: add_3 M2.
  { introv E. apply D. symmetry. apply~ E. }
  forwards A: find_1 M1. rewrite E1 in A. inverts~ A.
Qed.

Lemma not_indom_read_option : forall V (h : t V) k,
  ~ k \in h ->
  read_option h k = None.
Proof.
  introv nI. simpls. destruct~ find. false*.
Qed.

Lemma read_option_write_neq : forall V (h : t V) k k' v,
  ~ eq k k' ->
  read_option (write h k v) k' = read_option h k'.
Proof.
  introv D. tests I: (k' \in h).
  - forwards (v'&E): indom_read_option I. simpls. rewrite E.
    apply read_option_binds in E. apply binds_read_option.
    simpls. forwards M: find_2 E. apply~ find_1. apply~ add_2.
  - forwards R: not_indom_read_option I. simpls. rewrite R.
    forwards~ I': not_indom_write k I.
    { introv E. apply D. symmetry. apply* E. }
    forwards R': not_indom_read_option I'. simpl in R'. rewrite~ R'.
Qed.

Lemma in_write : forall V (h : t V) k v,
  k \in write h k v.
Proof. introv. forwards E: read_option_write_eq eq_refl. simpls. rewrite~ E. Qed.

Lemma in_write_inv : forall V (h : t V) k k' v,
  k \in write h k' v ->
  ~ eq k k' ->
  k \in h.
Proof.
  introv I E. simpls. destruct find eqn: Ev in I; tryfalse.
  forwards M: find_2 Ev. forwards~ M': add_3 M. { lets*: eq_sym. }
  apply find_1 in M'. rewrite~ M'.
Qed.

Lemma read_option_eq : forall V (h : t V) k k',
  eq k k' ->
  read_option h k = read_option h k'.
Proof.
  introv E. simpls. destruct (find k h) as [v|] eqn: B1.
  - forwards M1: find_2 B1. forwards M2: MapsTo_1 E M1. forwards~ E2: find_1 M2.
  - destruct (find k' h) as [v'|] eqn: B2; autos~.
    forwards M2: find_2 B2. forwards~ M1: MapsTo_1 M2. { applys~ eq_sym E. }
    forwards E1: find_1 M1. rewrite~ B1 in E1.
Qed.

Lemma in_eq : forall V (h : t V) k k',
  eq k k' ->
  k \in h ->
  k' \in h.
Proof.
  introv E I. simpls. destruct (find k h) eqn: E1; tryfalse.
  forwards M: find_2 E1. forwards M': MapsTo_1 E M. forwards E2: find_1 M'. rewrite~ E2.
Qed.

Lemma binds_eq : forall V (h : t V) k k' v v',
  binds h k v ->
  binds h k' v' ->
  eq k k' ->
  v = v'.
Proof.
  introv B1 B2 E. rewrite read_option_binds_eq in B1, B2.
  rewrites >> read_option_eq E in B1. rewrite B1 in B2. inverts~ B2.
Qed.


(** ** A notion of equivalence for heaps. **)
Definition heap_equiv {V} (h1 h2 : t V) :=
  forall k1 k2 v,
    eq k1 k2 ->
    binds h1 k1 v <-> binds h2 k2 v.

Lemma heap_equiv_weaken_eq : forall V (h1 h2 : t V),
  heap_equiv h1 h2 ->
  (forall k v, binds h1 k v <-> binds h2 k v).
Proof. introv E. introv. apply E. reflexivity. Qed.

Lemma heap_equiv_refl : forall V (h : t V),
  heap_equiv h h.
Proof. introv E. do 2 rewrite read_option_binds_eq. rewrites* >> read_option_eq E. Qed.

Lemma heap_equiv_sym : forall V (h1 h2 : t V),
  heap_equiv h1 h2 ->
  heap_equiv h2 h1.
Proof. introv E. unfold heap_equiv in *. introv Ek. rewrite* E. applys~ eq_sym Ek. Qed.

Lemma heap_equiv_trans : forall V (h1 h2 h3 : t V),
  heap_equiv h1 h2 ->
  heap_equiv h2 h3 ->
  heap_equiv h1 h3.
Proof. introv E1 E2. unfold heap_equiv in *. introv Ek. rewrite* E1. apply~ eq_refl. Qed.

Lemma heap_equiv_binds_eq : forall V (h1 h2 : t V) k k' v,
  heap_equiv h1 h2 ->
  eq k k' ->
  binds h1 k v ->
  binds h2 k' v.
Proof. introv E Ek B. unfolds in E. rewrite* <- E. Qed.

Lemma heap_equiv_binds : forall V (h1 h2 : t V) k v,
  heap_equiv h1 h2 ->
  binds h1 k v ->
  binds h2 k v.
Proof. introv E Ek. applys~ heap_equiv_binds_eq E Ek. apply~ eq_refl. Qed.

Lemma heap_equiv_indom_eq : forall V (h1 h2 : t V) k k',
  heap_equiv h1 h2 ->
  eq k k' ->
  k \in h1 ->
  k' \in h2.
Proof.
  introv E Ek I. lets (v&B): @indom_binds I.
  forwards B': heap_equiv_binds E B. applys~ in_eq Ek. applys~ @binds_indom B'.
Qed.

Lemma heap_equiv_indom : forall V (h1 h2 : t V) k,
  heap_equiv h1 h2 ->
  k \in h1 ->
  k \in h2.
Proof. introv E Ek. applys~ heap_equiv_indom_eq E Ek. apply~ eq_refl. Qed.

Lemma heap_equiv_read_option : forall V (h1 h2 : t V) k,
  heap_equiv h1 h2 ->
  read_option h1 k = read_option h2 k.
Proof.
  introv E. tests I: (k \in h1).
  - forwards (v&B): @indom_binds I.
    rewrites >> (@binds_read_option) B. symmetry. apply binds_read_option.
    applys~ heap_equiv_binds E B.
  - do 2 rewrite~ @not_indom_read_option.
    introv I'. false I. applys~ heap_equiv_indom I'. applys~ heap_equiv_sym E.
Qed.

Lemma heap_equiv_read : forall V `{Inhab V} (h1 h2 : t V) k,
  heap_equiv h1 h2 ->
  k \in h1 ->
  read h1 k = read h2 k.
Proof.
  introv E I. forwards E1: heap_equiv_read_option k E.
  forwards (v&E2): indom_read_option I. rewrite E2 in E1. symmetry in E1.
  rewrite (read_option_read_eq _ _ _ E1). rewrite~ (read_option_read_eq _ _ _ E2).
Qed.

Lemma heap_equiv_write : forall V (h1 h2 : t V) k v,
  heap_equiv h1 h2 ->
  heap_equiv (write h1 k v) (write h2 k v).
Proof.
  introv E. unfold heap_equiv in *. intros k1 k2 v' Ek. do 2 rewrite read_option_binds_eq.
  forwards E': E Ek. do 2 rewrite read_option_binds_eq in E'. tests Ek': (eq k k1).
  - repeat rewrite* read_option_write_eq. applys~ eq_trans Ek.
  - repeat rewrite* read_option_write_neq. introv Ek2. false Ek'.
    applys~ eq_trans Ek2. applys~ eq_sym Ek.
Qed.

Lemma heap_equiv_write_write : forall V (h1 h2 : t V) k v v',
  heap_equiv h1 h2 ->
  heap_equiv (write (write h1 k v') k v) (write h2 k v).
Proof.
  introv E. unfold heap_equiv in *. intros k1 k2 v2 Ek. do 2 rewrite read_option_binds_eq.
  forwards E': E Ek. do 2 rewrite read_option_binds_eq in E'. tests Ek': (eq k k1).
  - repeat rewrite* read_option_write_eq. applys~ eq_trans Ek'.
  - repeat rewrite* read_option_write_neq. introv Ek2. false Ek'.
    applys~ eq_trans Ek2. applys~ eq_sym Ek.
Qed.

Lemma heap_equiv_write_swap : forall V (h1 h2 : t V) k1 k2 v1 v2,
  ~ eq k1 k2 ->
  heap_equiv h1 h2 ->
  heap_equiv (write (write h1 k1 v1) k2 v2) (write (write h2 k2 v2) k1 v1).
Proof.
  introv D E. unfold heap_equiv in *. intros ka kb v Ek. do 2 rewrite read_option_binds_eq.
  forwards E': E Ek. do 2 rewrite read_option_binds_eq in E'.
  lets: eq_sym. lets: eq_trans.
  tests: (eq k1 ka); tests: (eq k2 ka);
  repeat ((rewrite read_option_write_eq; [| solve [ autos* ] ])
          || (rewrite read_option_write_neq; [| solve [ autos* ] ])); autos*.
  false* D.
Qed.

End HeapFromOrdered.


(** * Building [OrderedType.OrderedType] from TLC. **)

Class Comparable_lt T := Build_Comparable_lt {
    lt : T -> T -> bool ;
    lt_trans : forall x y z : T, lt x y -> lt y z -> lt x z ;
    lt_not_eq : forall x y : T, lt x y -> ~ x = y ;
    lt_total : forall x y, lt x y \/ x = y \/ lt y x
  }.

Module Type ComparableLt.

Parameter t : Type.

Parameter comparable : Comparable t.
Parameter comparable_lt : Comparable_lt t.

End ComparableLt.

Module OrderedTypeFromComparable (X : ComparableLt) : OrderedType.OrderedType.

Include X.

Definition eq := @eq t.
Definition lt a b : Prop := @lt t comparable_lt a b.

Definition eq_refl := @eq_refl t.
Definition eq_sym := @eq_sym t.
Definition eq_trans x y z := @eq_trans t y x z.

Definition lt_trans := @lt_trans t comparable_lt.
Definition lt_not_eq := @lt_not_eq t comparable_lt.

Lemma compare : forall x y : t, OrderedType.Compare lt eq x y.
Proof.
  introv. destruct (@Heap.lt t comparable_lt x y) eqn: L.
  - applys~ OrderedType.LT.
  - destruct (@decide (x = y) (@LibExec.comparable _ comparable _ _)) eqn: E.
    + rewrite decide_spec in E. rew_bool_eq in E. applys~ OrderedType.EQ.
    + rewrite decide_spec in E. rew_bool_eq in *. applys OrderedType.GT.
      destruct (@lt_total _ comparable_lt x y) as [H|[H|H]]; tryfalse.
      autos~.
Defined.

Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
Proof.
  introv. applys~ decidable_sumbool comparable.
Defined.

End OrderedTypeFromComparable.

Module Heap (X : ComparableLt).
Module OrderedType := OrderedTypeFromComparable X.
Module Export Heap := HeapFromOrdered OrderedType.
Include Heap.
End Heap.

Module HeapNat := HeapFromOrdered Nat_as_OT.
Module HeapZ := HeapFromOrdered Z_as_OT.
Module HeapPos := HeapFromOrdered Positive_as_OT.
Module HeapBinN := HeapFromOrdered N_as_OT.
Module HeapAscii := HeapFromOrdered Ascii_as_OT.
Module HeapString := HeapFromOrdered String_as_OT.
