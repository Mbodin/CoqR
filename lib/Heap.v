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
  {BI : BagIn A T} {BE : BagEmpty T} {BR : BagRead A B T} {BRO : BagReadOption A B T} {BD : BagDom T D}.

Class ReadOption_In_eq := {
    read_option_in_eq : forall a t, a \notin t -> read_option t a = None
  }.

Class ReadOption_Read_eq := {
    read_option_read_eq : forall a b t, read_option a t = Some b -> read a t = b
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
      match read_option t a with
      | None => False
      | Some _ => True
      end
  |}.

Instance ReadOptionToIn_ReadOption_In_eq : forall A B T `{BagReadOption A B T},
  ReadOption_In_eq (BI := ReadOptionToIn A B T).
Proof.
  constructors. unfold notin. simpl. introv. destruct* read_option.
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


(** * Instanciation of heaps **)

Module HeapFromOrdered (X : OrderedType.OrderedType).

Export X.

Definition K := t.

Module Export Tree := FMapAVL.Make(X).

Instance read_option_inst V : BagReadOption K V (t V) := {|
    read_option t a := find a t
  |}.

Instance read_inst V `{Inhab V} : BagRead K V (t V) :=
  ReadOptionToRead K V _.

Instance in_inst V : BagIn K (t V) :=
  ReadOptionToIn K V _.

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

Module Heap (X : ComparableLt) := HeapFromOrdered (OrderedTypeFromComparable (X)).
