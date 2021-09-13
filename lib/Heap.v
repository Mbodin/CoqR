(** An instanciation of heaps.
  It is based on the AVL-tree implementation from the standard library. **)

From Coq Require Import FSets.FMapAVL.
From Lib Require Import LibExec.
From TLC Require Export LibContainer.

Class Comparable_lt T := {
    lt : T -> T -> bool ;
    lt_trans : forall x y z : T, lt x y -> lt y z -> lt x z ;
    lt_not_eq : forall x y : T, lt x y -> ~ x = y
  }.

Section Heap.

Variable K : Type.
Hypothesis K_comparable : Comparable K.

Module K_OrderedType : OrderedType.OrderedType. (* Doesn’t work: once module-based, one has to stay module based. *)

   Parameter eq : t -> t -> Prop.
   Parameter lt : t -> t -> Prop.
   Parameter eq_refl : forall x : t, eq x x.
   Parameter eq_sym : forall x y : t, eq x y -> eq y x.
   Parameter eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
   Parameter lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
   Parameter lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
   Parameter compare : forall x y : t, OrderedType.Compare lt eq x y.
   Parameter eq_dec : forall x y : t, {eq x y} + {~ eq x y}.

Definition Tree X :=
  FMapAVL.Make(X).

Definition heap K V := FMapAVL .tree
