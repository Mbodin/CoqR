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
Require Import Ascii Double.
Require Export Loops.


(** * Interpreter functions **)

(** We recall from RinternalsAux.v that we write [p_] for the object
  referenced by the pointer [p], and [p_f] for the field [f] of it. **)

Require Export Conflicts.
Require Export CRmath.
Require Export CRinternals.
Require Export CDefn.
Require Export CMemory.
Require Export CRinlinedfuns.
Require Export CBuiltin.
Require Export CDuplicate.
Require Export CDstruct.
Require Export CEval.
Require Export CArithmetic.
Require Export CUtil.
Require Export CPrintutils.
Require Export CEnvir.
Require Export CNames.
Require Export CSysutils.
Require Export CGram.
Require Export CContext.
Require Export CMatch.
Require Export CAltrep.
Require Export CCoerce.
Require Export CAttrib.
Require Export CObjects.

(** Evaluates the expression in the global environment. **)
Definition eval_global globals runs S e :=
  add%stack "eval_global" in
  eval globals runs S e (read_globals globals R_GlobalEnv).

Optimize Heap.
