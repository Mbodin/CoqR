(** Invariants.
  Contains the proofs of some invariants respected by the functions
  defined in Rcore, Rinit, and Rfeatures. **)

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

Require Import Rcore RfeaturesAux Rinit.
Require Export Invariants.

(** * General Lemmae **)

(** If runs returns a result, then adding fuel does not change it. **)
Lemma runs_while_loop_fuel_conserve : forall A globals n n' S (a : A) expr body,
    n <= n' ->
    ~ bottom_result (runs_while_loop (runs n globals) S a expr body) ->
    runs_while_loop (runs n' globals) S a expr body = runs_while_loop (runs n globals) S a expr body.
Proof.
  introv I B. repeat rewrite <- runs_proj_while_loop_eq in *. gen n' S a. induction n; introv I B.
  - false~ B.
  - destruct n'; try solve [ math ]. simpls. unfolds while_loop. repeat rewrite <- runs_proj_while_loop_eq.
    destruct expr; simpls~; tryfalse~. cases_if~.
    destruct body; simpls~; tryfalse~. rewrite~ IHn. math.
Qed.

(* Slow version
Lemma runs_while_loop_fuel_conserve : forall A globals n n' S (a : A) expr body,
    n <= n' ->
    ~ bottom_result (runs_while_loop (runs n globals) S a expr body) ->
    runs_while_loop (runs n' globals) S a expr body = runs_while_loop (runs n globals) S a expr body.
Proof.
  introv I B. gen n' S a. induction n; introv I B.
  - false~ B.
  - destruct n'; try solve [ math ]. simpls. unfolds while_loop. repeat rewrite <- runs_proj_while_loop_eq.
    destruct expr; simpls~; tryfalse~. cases_if~.
    destruct body; simpls~; tryfalse~. rewrite~ IHn. math.
Qed.
*)

(* TODO: put these lemmae in RfeaturesAux.v.
   In RfeaturesAux, we can change the tactic to work on all projections
   by only unfolding everything in aux1 (no simplifications), then do a
   simplification between the two auxn.
   We will then be able to automate the lemmae above, without them taking
   too much time to compile. *)

(** * Lemmae about Rinit.v **)

(* TODO *)

(* I think that it would be easy to use tactics to check that [setup_Rmainloop]
  is indeed of the form [result_success S globals] or something like that. *)

(** It would be nice to prove that the read-eval-print-loop can not
  return a [result_impossible]. **)

