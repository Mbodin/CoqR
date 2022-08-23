(** Result.
  This file describes the [result] monad. **)

(* Copyright © 2022 Martin Bodin

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

From CoqR Require Import Result.
From ITree Require Export ITree.

Import EventMonad.
Import ITree.Eq.Eqit.

(** * Notations *)

Declare Scope result_scope.

Module ResultNotations.

Delimit Scope result_scope with res.

Notation "c >>= f" :=
  (@EventMonad.bind _ _ _ _ c%res f%res)
  (at level 58, left associativity) : result_scope.

Notation "f =<< c" :=
  (@EventMonad.bind _ _ _ _ c%res f%res)
  (at level 61, right associativity) : result_scope.

Notation "f >=> g" :=
  (@rcompose _ _ _ _ _ f g)
  (at level 61, right associativity) : result_scope.

Notation "e1 ;; e2" :=
  (@EventMonad.bind _ _ _ _ e1%res (fun _ => e2%res))
  (at level 61, right associativity) : result_scope.

Notation "'let*' p ':=' c1 'in' c2" :=
  (@EventMonad.bind _ _ _ _ c1%res (fun p => c2%res))
  (at level 61, p as pattern, c1 at next level, right associativity) : result_scope.
  
Notation "x <- c1 ;; c2" :=
  (@EventMonad.bind _ _ _ _ c1%res (fun x => c2%res))
  (at level 61, c1 at next level, right associativity) : result_scope.

Notation "' pat <- c1 ;; c2" :=
  (@EventMonad.bind _ _ _ _ c1%res (fun x => match x with pat => c2%res end))
  (at level 61, pat pattern, c1 at next level, right associativity) : result_scope.

Notation "` v" :=
  (@EventMonad.ret _ v)
  (at level 10, v at next level, no associativity) : result_scope.

Notation "'return' v" :=
  (@EventMonad.ret _ v)
  (at level 10, v at next level, no associativity) : result_scope.

End ResultNotations.

Import ResultNotations.
Open Scope result_scope.


(** * Boolean Operations *)

Definition mR_lift [A B] (op : A -> B)
  d (b : result d A) : result d B :=
  ltac:(simplify_term (
    b <- b ;;
    return (op b))).

Lemma mR_lift2_value : forall A B C (op : A -> B -> C) a b,
  (mR_lift2 op _ _ (`a) (`b))%res ≅ return (op a b).
Proof. intros. tau_steps. reflexivity. Qed.

Definition mR_lift2 [A B C] (op : A -> B -> C)
    d1 d2 (b1 : result d1 A) (b2 : result d2 B) : result _ C :=
  b1 <- b1 ;;
  b2 <- b2 ;;
  return (op b1 b2).

Lemma mR_lift2_value : forall A B C (op : A -> B -> C) a b,
  (mR_lift2 op _ _ (`a) (`b))%res ≅ return (op a b).
Proof. intros. tau_steps. reflexivity. Qed.

Section Booleans.

Open Scope bool_scope.

Set Printing All.

Definition mR_and := mR_lift andb.

Notation "a && b" := (mR_and _ _ a b) (at level 40, left associativity) : result_scope.

Definition mR_or := mR_lift orb.

Infix "'||" := mR_or (at level 50, left associativity) : result_scope.

Notation "'! b" := (mR_neg b) (at level 35, right associativity).

Lemma mR_neg_bool : forall b : bool,
  '! b ≅ (negb b : mR_bool).
Proof. intros. tau_steps. reflexivity. Qed.

Definition mR_decide P `{Decidable P} : mR_bool := decide P.
Arguments mR_decide P {_}.

Notation "''decide' P" := (mR_decide P) (at level 70, no associativity).

Definition mR_eq_SEXP : mR_SEXP -> mR_SEXP -> mR_bool := @mR_eq _ _.

Infix "'==" := mR_eq (at level 70, no associativity).

Notation "a '!= b" := ('! (a '== b)) (at level 70, no associativity).

Notation "'ifc' b 'then' v1 'else' v2" :=
  (x <- (b : mR_bool) ;; if x then v1 else v2)
  (at level 200, right associativity) : type_scope.
*)
