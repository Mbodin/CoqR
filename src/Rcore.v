(** Rcore.
  Describes how R evaluates expressions.
  The content of this file is the Coq equivalent of functions from R source code.
  Note that only relevant definitions are translated here. Some are just
  reinterpreted in Coq without following the original algorithm of the
  C source. See report for more details. **)

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
From Lib Require Import Double.
From CoqR Require Export Loops.


(** * Interpreter functions **)

(** We recall from RinternalsAux.v that we write [p_] for the object
  referenced by the pointer [p], and [p_f] for the field [f] of it. **)

From CoqR.core Require Export Conflicts.
From CoqR.core Require Export CRmath.
From CoqR.core Require Export CRinternals.
From CoqR.core Require Export CDefn.
From CoqR.core Require Export CMemory.
From CoqR.core Require Export CRinlinedfuns.
From CoqR.core Require Export CBuiltin.
From CoqR.core Require Export CDuplicate.
From CoqR.core Require Export CDstruct.
From CoqR.core Require Export CEval.
From CoqR.core Require Export CArithmetic.
From CoqR.core Require Export CUtil.
From CoqR.core Require Export CPrintutils.
From CoqR.core Require Export CEnvir.
From CoqR.core Require Export CNames.
From CoqR.core Require Export CSysutils.
From CoqR.core Require Export CGram.
From CoqR.core Require Export CContext.
From CoqR.core Require Export CMatch.
From CoqR.core Require Export CAltrep.
From CoqR.core Require Export CCoerce.
From CoqR.core Require Export CAttrib.
From CoqR.core Require Export CObjects.
From CoqR.core Require Export CArray.
From CoqR.core Require Export CLogic.
From CoqR.core Require Export CSubscript.
From CoqR.core Require Export CSubassign.

(** Evaluates the expression in the global environment. **)
Definition eval_global globals runs e :=
  add%stack "eval_global" in
  eval globals runs e (read_globals globals R_GlobalEnv).

Optimize Heap.
