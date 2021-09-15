(** An instanciation of heaps.
  It is based on the AVL-tree implementation from the standard library. **)

From Coq Require Import FSets.FMapAVL.
From Lib Require Import LibExec.
From TLC Require Export LibTactics LibReflect LibContainer.


(** * Addition to LibContainer about read_option **)

(** ** Definitions **)

Class BagReadOption A B T := { read_option : T -> A -> option B }.

Class BagInDec A T := {
    bag_in :> BagIn A T ;
    bag_in_dec :> forall a (t : T), Decidable (a \in t)
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

Definition K := t.

Module Export Tree := FMapAVL.Make(X).

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
Definition write V : t V -> K -> V -> t V := update.

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

Lemma read_option_binds : forall V (h : t V) k v,
  read_option h k = Some v ->
  binds h k v.
Proof. autos~. Qed.

Lemma read_option_indom : forall V (h : t V) k v,
  read_option h k = Some v ->
  k \indom h.
Proof. introv E. forwards B: read_option_binds E. applys~ indom_of_binds. binds_indom B. Qed.

Lemma indom_read_option : forall V (h : heap K V) k,
  indom h k ->
  exists v, read_option h k = Some v.
Proof.
  introv I. forwards (v&B): @indom_binds I.
  exists v. applys~ @binds_read_option B.
Qed.

Lemma read_option_write_same : forall V (h : heap K V) k v,
  read_option (write h k v) k = Some v.
Proof. introv. apply binds_read_option. applys~ @binds_write_eq. Qed.

Lemma not_indom_write : forall K V (h : heap K V) k k' v',
  k <> k' ->
  ~ indom h k ->
  ~ indom (write h k' v') k.
Proof. introv D I1 I2. forwards~: @indom_write_inv I2. Qed.

Lemma read_option_write : forall V (h : heap K V) k k' v,
  k <> k' ->
  read_option (write h k v) k' = read_option h k'.
Proof.
  introv D. tests I: (indom h k').
   forwards (v'&E): indom_read_option I. rewrite E.
    apply read_option_binds in E. apply binds_read_option.
    applys~ @binds_write_neq E.
   rewrite (not_indom_read_option I). forwards I': not_indom_write I.
    introv E. apply D. symmetry. apply* E.
    rewrite~ (not_indom_read_option I').
Qed.

(** A notion of equivalence for heaps. **)
Definition heap_equiv K V (h1 h2 : heap K V) :=
  forall k v, binds h1 k v <-> binds h2 k v.

Lemma heap_equiv_refl : forall K V (h : heap K V),
  heap_equiv h h.
Proof. introv. unfolds. autos*. Qed.

Lemma heap_equiv_sym : forall K V (h1 h2 : heap K V),
  heap_equiv h1 h2 ->
  heap_equiv h2 h1.
Proof. introv E. unfolds heap_equiv. introv. rewrite* E. Qed.

Lemma heap_equiv_trans : forall K V (h1 h2 h3 : heap K V),
  heap_equiv h1 h2 ->
  heap_equiv h2 h3 ->
  heap_equiv h1 h3.
Proof. introv E1 E2. unfolds heap_equiv. introv. rewrite* E1. Qed.

Lemma heap_equiv_binds : forall K V (h1 h2 : heap K V) k v,
  heap_equiv h1 h2 ->
  binds h1 k v ->
  binds h2 k v.
Proof. introv E B. unfolds in E. rewrite* <- E. Qed.

Lemma heap_equiv_indom : forall K V (h1 h2 : heap K V) k,
  heap_equiv h1 h2 ->
  indom h1 k ->
  indom h2 k.
Proof.
  introv E I. lets (v&B): @indom_binds I.
  forwards B': heap_equiv_binds E B. applys~ @binds_indom B'.
Qed.

Lemma heap_equiv_read : forall V `{Inhab V} (h1 h2 : heap K V) k,
  heap_equiv h1 h2 ->
  indom h1 k ->
  read h1 k = read h2 k.
Proof.
  introv E I. forwards (v&B): @indom_binds I.
  rewrites >> binds_read B. symmetry. apply binds_read.
  applys~ heap_equiv_binds E B.
Qed.

Lemma heap_equiv_read_option : forall V (h1 h2 : heap K V) k,
  heap_equiv h1 h2 ->
  read_option h1 k = read_option h2 k.
Proof.
  introv E. tests I: (indom h1 k).
  - forwards (v&B): @indom_binds I.
    rewrites >> (@binds_read_option) B. symmetry. apply binds_read_option.
    applys~ heap_equiv_binds E B.
  - do 2 rewrite~ @not_indom_read_option.
    introv I'. false I. applys~ heap_equiv_indom I'. applys~ heap_equiv_sym E.
Qed.

Lemma heap_equiv_write : forall K V (h1 h2 : heap K V) k v,
  heap_equiv h1 h2 ->
  heap_equiv (write h1 k v) (write h2 k v).
Proof.
  introv E. unfolds heap_equiv. iff B;
    (forwards [(?&?)|(D&B')]: @binds_write_inv B;
     [ substs; apply binds_write_eq
     | apply~ @binds_write_neq; applys~ heap_equiv_binds B'; apply~ heap_equiv_sym ]).
Qed.

Lemma heap_equiv_write_write : forall K V (h1 h2 : heap K V) k v v',
  heap_equiv h1 h2 ->
  heap_equiv (write (write h1 k v') k v) (write h2 k v).
Proof.
  introv E. unfolds heap_equiv. iff B;
    (forwards [(?&?)|(D&B')]: @binds_write_inv B;
     [ substs; apply binds_write_eq
     | repeat apply~ @binds_write_neq ]).
  - forwards~ B'': @binds_write_neq_inv B'. applys~ heap_equiv_binds B''.
  - applys~ heap_equiv_binds B'. apply* heap_equiv_sym.
Qed.

Lemma heap_equiv_write_swap : forall K V (h1 h2 : heap K V) k1 k2 v1 v2,
  k1 <> k2 ->
  heap_equiv h1 h2 ->
  heap_equiv (write (write h1 k1 v1) k2 v2) (write (write h2 k2 v2) k1 v1).
Proof.
  introv D E. unfolds heap_equiv. iff B;
    repeat (match goal with
    | B : binds (write _ _ _) _ _ |- _ =>
      let D' := fresh "D" in
      let B' := fresh "B" in
      forwards [(?&?)|(D'&B')]: @binds_write_inv (rm B)
    | |- binds (write _ _ _) _ _ =>
      apply~ @binds_write_eq || apply~ @binds_write_neq
    end; substs; tryfalse~); apply~ E.
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
