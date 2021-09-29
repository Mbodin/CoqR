(** Core.CUtil.
  The function names in this file correspond to the function names
  in the file main/util.c. **)

(* Copyright © 2018 Martin Bodin

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

Set Implicit Arguments.
From Coq Require Import Ascii.
From CoqR Require Import Loops.
From CoqR.core Require Import CRinternals CRinlinedfuns.

Section Parameterised.

Variable runs : runs_type.

Definition int_to_double := Double.int_to_double : int -> double.

Local Coercion int_to_double : Z >-> double.


Definition truenames : list string :=
  ["T"; "True"; "TRUE"; "true"]%string.

Definition StringTrue name :=
  decide (Mem name truenames).

Definition falsenames : list string :=
  ["F"; "False"; "FALSE"; "false"]%string.

Definition StringFalse name :=
  decide (Mem name falsenames).

Definition isspace c :=
  decide (Mem c [" " ; "009" (** '\t' **) ; "010" (** '\n' **) ; "011" (** '\v' **) ; "012" (** '\f' **) ; "013" (** '\r' **)]%char).

Definition isBlankString s :=
  decide (Forall (fun c => isspace c) (string_to_list s)).

Definition TypeTable : list (string * SExpType) := [
    ("NULL", NilSxp) ;
    ("symbol", SymSxp) ;
    ("pairlist", ListSxp) ;
    ("closure", CloSxp) ;
    ("environment", EnvSxp) ;
    ("promise", PromSxp) ;
    ("language", LangSxp) ;
    ("special", SpecialSxp) ;
    ("builtin", BuiltinSxp) ;
    ("char", CharSxp) ;
    ("logical", LglSxp) ;
    ("integer", IntSxp) ;
    ("double", RealSxp) ;
    ("complex", CplxSxp) ;
    ("character", StrSxp) ;
    ("...", DotSxp) ;
    ("any", AnySxp) ;
    ("expression", ExprSxp) ;
    ("list", VecSxp) ;
    ("externalptr", ExtptrSxp) ;
    ("bytecode", BcodeSxp) ;
    ("weakref", WeakrefSxp) ;
    ("raw", RawSxp) ;
    ("S4", S4Sxp) ;
    ("numeric", RealSxp) ;
    ("name", SymSxp)
  ]%string.

Fixpoint str2type_loop s i (l : list (string * SExpType))  :=
  match l return SExpType with
  | nil =>
    (** In the original C code, the interpreter returned [(SEXPTYPE) -1].
     Given that [SEXPTYPE] are in C stored on 5 bits, we should thus return
     [31], which is the number associated to the [FreeSxp] constructor. **)
    FreeSxp
  | (str, t) :: l' =>
    ifb s = str then t
    else str2type_loop s (i + 1)%Z l'
end.

Definition str2type (s : string) : SExpType :=
  str2type_loop s 0 TypeTable.

Fixpoint findTypeInTypeTable_loop t i (l : list (string * SExpType)) :=
  match l return int with
  | nil => (-1)%Z
  | (str, t') :: l =>
    ifb t = t' then i
    else findTypeInTypeTable_loop t (1 + i)%Z l
  end.

Definition findTypeInTypeTable t : int :=
  findTypeInTypeTable_loop t 0 TypeTable.

End Parameterised.

