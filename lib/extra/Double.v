(** This file aims at interfacing with Flocq. **)

(* Any check would be greatly appreciated. *)

(* LATER: Use file Fappli_IEEE_extra.v of Compcert/lib/? I need to set up a license for this
  (either GPL or something compatible with the INRIA non-commercial license). *)

Require Import Shared TLC.LibInt.
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
  | Zpos p => Fappli_IEEE.F754_finite false p 64
  | Zneg p => Fappli_IEEE.F754_finite true p 64
  end.

Definition is_zero (x : double) :=
  decide (x = Fappli_IEEE.F754_zero false \/ x = Fappli_IEEE.F754_zero true).

Parameter opp : double -> double. (* TODO: use Flocq. *)
Parameter add : double -> double -> double. (* TODO: use Flocq. *)
Parameter sub : double -> double -> double. (* TODO: use Flocq. *)
Parameter mult : double -> double -> double. (* TODO: use Flocq. *)
Parameter div : double -> double -> double. (* TODO: use Flocq. *)

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
