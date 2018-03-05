(** This file aims at interfacing with Flocq. **)

(* Note: Any check on the content of this file would be greatly appreciated. *)

(* LATER: Use file Fappli_IEEE_extra.v of Compcert/lib/? I need to set up a license for this
  (either GPL or something compatible with the INRIA non-commercial license). *)

Require Import Common TLC.LibInt.
Require Import Flocq.Appli.Fappli_IEEE Flocq.Appli.Fappli_IEEE_bits.


Definition double : Type := Fappli_IEEE.full_float.


(* Warning: this is using the Leibniz equality, not the usual “equality operator” on floats. *)
Instance double_comparable : Comparable double.
  prove_comparable_simple_inductive.
Defined.


Definition int_to_double (i : int) : double :=
  (* FIXME: Fappli_IEEE.binary_normalize 53 1024 eq_refl eq_refl Fappli_IEEE.mode_NE i 0 false. *)
  match i with
  | Z0 => Fappli_IEEE.F754_zero false
  | Zpos p => Fappli_IEEE.F754_finite false p 0
  | Zneg p => Fappli_IEEE.F754_finite true p 0
  end.

Definition double_to_int d : option int :=
  match d with
  | F754_zero _ => Some 0
  | F754_infinity _ => None
  | F754_nan _ _ => None
  | F754_finite s p _ => Some (if s then Zneg p else Zpos p)
  end.

Definition double_to_int_zero d :=
  match double_to_int d with
  | Some v => v
  | None => 0
  end.


Definition is_zero (x : double) :=
  decide (x = Fappli_IEEE.F754_zero false \/ x = Fappli_IEEE.F754_zero true).

Parameter opp : double -> double. (* TODO: use Flocq. *)
Parameter fabs : double -> double. (* TODO: use Flocq. *) (* FIXME: Why is [abs] refused as a name here? *)
Parameter add : double -> double -> double. (* TODO: use Flocq. *)
Parameter sub : double -> double -> double. (* TODO: use Flocq. *)
Parameter mult : double -> double -> double. (* TODO: use Flocq. *)
Parameter div : double -> double -> double. (* TODO: use Flocq. *)

Parameter floor : double -> double. (* FIXME: what to do with these? *)
Parameter ceil : double -> double. (* FIXME: what to do with these? *)
Parameter sqrt : double -> double. (* FIXME: what to do with these? *)
Parameter exp : double -> double. (* FIXME: what to do with these? *)
Parameter expm1 : double -> double. (* FIXME: what to do with these? *)
Parameter log : double -> double. (* FIXME: what to do with these? *)
Parameter logm1 : double -> double. (* FIXME: what to do with these? *)
Parameter log1p : double -> double. (* FIXME: what to do with these? *)
Parameter cos : double -> double. (* FIXME: what to do with these? *)
Parameter sin : double -> double. (* FIXME: what to do with these? *)
Parameter tan : double -> double. (* FIXME: what to do with these? *)
Parameter acos : double -> double. (* FIXME: what to do with these? *)
Parameter asin : double -> double. (* FIXME: what to do with these? *)
Parameter atan : double -> double. (* FIXME: what to do with these? *)
Parameter cosh : double -> double. (* FIXME: what to do with these? *)
Parameter sinh : double -> double. (* FIXME: what to do with these? *)
Parameter tanh : double -> double. (* FIXME: what to do with these? *)

Definition posInf := Fappli_IEEE.F754_infinity false : double.
Definition negInf := Fappli_IEEE.F754_infinity true : double.

Definition NaN : double := Fappli_IEEE.F754_nan false 1.
  (* FIXME: refine (Fappli_IEEE.B754_nan _ _ false (exist _ 1%positive _)). reflexivity.*)

Definition NaN1954 : double :=
  (** This is defined in R (in main/arithmetic.c, function R_ValueOfNA) as the raw bit
    conversion from the two-integer word whose first component is 0x7ff00000 (that is,
    2146435072) and the second 1954. **)
  (* FIXME: Fappli_IEEE_bits.b64_of_bits (2146435072 + 1954 * 2 ^ 32).*)
  Fappli_IEEE.F754_nan true 1954.

Definition isNaN : double -> bool := Fappli_IEEE.is_nan_FF.

Definition getNaNData x :=
  match x with
  | Fappli_IEEE.F754_nan _ i => Some i
  | _ => None
  end.

Definition FLT_EPSILON := Fappli_IEEE.F754_finite false 2 (-24).

Parameter ge : double -> double -> bool. (* TODO: use Flocq. *)
Parameter le : double -> double -> bool. (* TODO: use Flocq. *)
Parameter gt : double -> double -> bool. (* TODO: use Flocq. *)
Parameter lt : double -> double -> bool. (* TODO: use Flocq. *)

Global Instance Ge_double : Ge double := Build_Ge ge.
Global Instance Le_double : Le double := Build_Le le.
Global Instance Gt_double : Gt double := Build_Gt gt.
Global Instance Lt_double : Lt double := Build_Lt lt.

Global Instance ge_double_Decidable : forall x1 x2 : double,
    Decidable (x1 >= x2).
  intros. refine (decidable_make _ (decide := ge x1 x2) _).
  skip. (* Admitted. *)
Defined.

Global Instance le_double_Decidable : forall x1 x2 : double,
    Decidable (x1 <= x2).
  intros. refine (decidable_make _ (decide := le x1 x2) _).
  skip. (* Admitted. *)
Defined.

Global Instance gt_double_Decidable : forall x1 x2 : double,
    Decidable (x1 > x2).
  intros. refine (decidable_make _ (decide := gt x1 x2) _).
  skip. (* Admitted. *)
Defined.

Global Instance lt_double_Decidable : forall x1 x2 : double,
    Decidable (x1 < x2).
  intros. refine (decidable_make _ (decide := lt x1 x2) _).
  skip. (* Admitted. *)
Defined.
