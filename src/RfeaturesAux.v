(** RfeaturesAux.
  Contains useful lemmae about [runs]. **)

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

Require Export MonadTactics Rfeatures.


(** * Projections of [runs] **)

(** As-is, [runs] is a large definition and [simpl] can take a while if
  there is a [runs] to unfold in the context.  We would sometimes want
  to only consider a simpler definition of [runs] containing only the
  interesting projection. **)

(** ** Tactics **)

(** All these definitions follow a similar pattern.
  We thus automate their definitions using tactics. **)

(** Get the expected type of the replacement projection. **)
Ltac get_type_projection proj :=
  match type of proj with
  | runs_type -> ?t => exact (nat -> Globals -> t)
  end.

(** Defines the projection for the cases where the function behind
  the projection is a simple recursive loop. **)
Ltac compute_simple_projection proj L :=
  let globals := fresh "globals" in
  let max_step := fresh "max_step" in
  let IHmax_step := fresh "IH" max_step in
  intros max_step globals;
  induction max_step as [|max_step IHmax_step];
  [ let r := eval simpl in (proj (runs 0 globals)) in exact r
  | let r := eval simpl in (proj (runs (S max_step) globals)) in
    let r :=
      match r with
      | context [ ?f globals (runs max_step globals) ] =>
        let r := eval unfold f in r in
        r
      | context [ ?f (runs max_step globals) ] =>
        let r := eval unfold f in r in
        r
      end in
    let rec unfold_hints L r :=
      match L with
      | nil => r
      | boxer ?f :: ?L' =>
        let r := eval unfold f in r in
        unfold_hints L' r
      end in
    let L := list_boxer_of L in
    let r := unfold_hints L r in
    let rec rewrite_internals r :=
      match r with
      | context C [ proj (runs max_step globals) ] =>
        let r := context C[IHmax_step] in
        rewrite_internals r
      | context C [ proj globals (runs max_step globals) ] =>
        let r := context C[IHmax_step] in
        rewrite_internals r
      | _ => r
      end in
    let r := rewrite_internals r in
    exact r ].

(** Solves the equality when the function behind the projection
  is a simple recursive loop. **)
Ltac solve_eq_simple_projection :=
  let globals := fresh "globals" in
  let max_step := fresh "max_step" in
  let IHmax_step := fresh "IH" max_step in
  intros max_step globals; induction max_step as [|max_step IHmax_step];
  [ reflexivity
  | simpl; repeat rewrite <- IHmax_step; reflexivity ].

(** ** [runs_while_loop] **)

Definition runs_proj_while_loop : ltac:(get_type_projection runs_while_loop).
  compute_simple_projection runs_while_loop >>.
Defined.

Lemma runs_proj_while_loop_eq : forall max_step globals,
  runs_while_loop (runs max_step globals) = runs_proj_while_loop max_step globals.
Proof. solve_eq_simple_projection. Qed.

(** ** [runs_set_longjump] **)

Definition runs_proj_set_longjump : ltac:(get_type_projection runs_set_longjump).
  compute_simple_projection runs_set_longjump >>.
Defined.

Lemma runs_proj_set_longjump_eq : forall max_step globals,
  runs_set_longjump (runs max_step globals) = runs_proj_set_longjump max_step globals.
Proof. solve_eq_simple_projection. Qed.

(** ** [runs_R_cycle_detected] **)

Definition runs_proj_R_cycle_detected : ltac:(get_type_projection runs_R_cycle_detected).
  compute_simple_projection runs_R_cycle_detected >>.
Defined.

Lemma runs_proj_R_cycle_detected_eq : forall max_step globals,
  runs_R_cycle_detected (runs max_step globals) = runs_proj_R_cycle_detected max_step globals.
Proof. solve_eq_simple_projection. Qed.

(** ** [runs_eval] **)

Definition runs_proj_eval : ltac:(get_type_projection runs_eval).
  compute_simple_projection runs_eval >>.
Defined.

Lemma runs_proj_eval_eq : forall max_step globals,
  runs_eval (runs max_step globals) = runs_proj_eval max_step globals.
Proof. solve_eq_simple_projection. Qed.

(** ** [runs_getAttrib] **)

Definition runs_proj_getAttrib : ltac:(get_type_projection runs_getAttrib).
  compute_simple_projection runs_getAttrib >> getAttrib0.
Defined.

Lemma runs_proj_getAttrib_eq : forall max_step globals,
  runs_getAttrib (runs max_step globals) = runs_proj_getAttrib max_step globals.
Proof. solve_eq_simple_projection. Qed.

(** ** [runs_setAttrib] **)

Definition runs_proj_setAttrib : ltac:(get_type_projection runs_setAttrib).
  compute_simple_projection runs_setAttrib >>.
Defined.

Lemma runs_proj_setAttrib_eq : forall max_step globals,
  runs_setAttrib (runs max_step globals) = runs_proj_setAttrib max_step globals.
Proof. solve_eq_simple_projection. Qed.

(** ** [runs_duplicate1] **)

Definition runs_proj_duplicate1 : ltac:(get_type_projection runs_duplicate1).
  compute_simple_projection runs_duplicate1 >>.
Defined.

Lemma runs_proj_duplicate1_eq : forall max_step globals,
  runs_duplicate1 (runs max_step globals) = runs_proj_duplicate1 max_step globals.
Proof. solve_eq_simple_projection. Qed.

(** ** [runs_stripAttrib] **)

Definition runs_proj_stripAttrib : ltac:(get_type_projection runs_stripAttrib).
  compute_simple_projection runs_stripAttrib >>.
Defined.

Lemma runs_proj_stripAttrib_eq : forall max_step globals,
  runs_stripAttrib (runs max_step globals) = runs_proj_stripAttrib max_step globals.
Proof. solve_eq_simple_projection. Qed.

(** ** [runs_evalseq] **)

Definition runs_proj_evalseq : ltac:(get_type_projection runs_evalseq).
  compute_simple_projection runs_evalseq >>.
Defined.

Lemma runs_proj_evalseq_eq : forall max_step globals,
  runs_evalseq (runs max_step globals) = runs_proj_evalseq max_step globals.
Proof. solve_eq_simple_projection. Qed.

(** ** [runs_R_isMissing] **)

Definition runs_proj_R_isMissing : ltac:(get_type_projection runs_R_isMissing).
  compute_simple_projection runs_R_isMissing >>.
Defined.

(*
Lemma runs_proj_R_isMissing_eq : forall max_step globals,
  runs_R_isMissing (runs max_step globals) = runs_proj_R_isMissing max_step globals.
Proof. solve_eq_simple_projection. (* FIXME: Stack overflow *) Qed.
 *)

(** ** [runs_AnswerType] **)

Definition runs_proj_AnswerType : ltac:(get_type_projection runs_AnswerType).
  compute_simple_projection runs_AnswerType >>.
Defined.

Lemma runs_proj_AnswerType_eq : forall max_step globals,
  runs_AnswerType (runs max_step globals) = runs_proj_AnswerType max_step globals.
Proof. solve_eq_simple_projection. Qed.

(** ** [runs_ListAnswer] **)

Definition runs_proj_ListAnswer : ltac:(get_type_projection runs_ListAnswer).
  compute_simple_projection runs_ListAnswer >>.
Defined.

Lemma runs_proj_ListAnswer_eq : forall max_step globals,
  runs_ListAnswer (runs max_step globals) = runs_proj_ListAnswer max_step globals.
Proof. solve_eq_simple_projection. Qed.

(** ** [runs_StringAnswer] **)

Definition runs_proj_StringAnswer : ltac:(get_type_projection runs_StringAnswer).
  compute_simple_projection runs_StringAnswer >>.
Defined.

Lemma runs_proj_StringAnswer_eq : forall max_step globals,
  runs_StringAnswer (runs max_step globals) = runs_proj_StringAnswer max_step globals.
Proof. solve_eq_simple_projection. Qed.

(** ** [runs_LogicalAnswer] **)

Definition runs_proj_LogicalAnswer : ltac:(get_type_projection runs_LogicalAnswer).
  compute_simple_projection runs_LogicalAnswer >>.
Defined.

Lemma runs_proj_LogicalAnswer_eq : forall max_step globals,
  runs_LogicalAnswer (runs max_step globals) = runs_proj_LogicalAnswer max_step globals.
Proof. solve_eq_simple_projection. Qed.

(** ** [runs_IntegerAnswer] **)

Definition runs_proj_IntegerAnswer : ltac:(get_type_projection runs_IntegerAnswer).
  compute_simple_projection runs_IntegerAnswer >>.
Defined.

Lemma runs_proj_IntegerAnswer_eq : forall max_step globals,
  runs_IntegerAnswer (runs max_step globals) = runs_proj_IntegerAnswer max_step globals.
Proof. solve_eq_simple_projection. Qed.

(** ** [runs_RealAnswer] **)

Definition runs_proj_RealAnswer : ltac:(get_type_projection runs_RealAnswer).
  compute_simple_projection runs_RealAnswer >>.
Defined.

Lemma runs_proj_RealAnswer_eq : forall max_step globals,
  runs_RealAnswer (runs max_step globals) = runs_proj_RealAnswer max_step globals.
Proof. solve_eq_simple_projection. Qed.

(** ** [runs_ComplexAnswer] **)

Definition runs_proj_ComplexAnswer : ltac:(get_type_projection runs_ComplexAnswer).
  compute_simple_projection runs_ComplexAnswer >>.
Defined.

Lemma runs_proj_ComplexAnswer_eq : forall max_step globals,
  runs_ComplexAnswer (runs max_step globals) = runs_proj_ComplexAnswer max_step globals.
Proof. solve_eq_simple_projection. Qed.

(** ** [runs_RawAnswer] **)

Definition runs_proj_RawAnswer : ltac:(get_type_projection runs_RawAnswer).
  compute_simple_projection runs_RawAnswer >>.
Defined.

Lemma runs_proj_RawAnswer_eq : forall max_step globals,
  runs_RawAnswer (runs max_step globals) = runs_proj_RawAnswer max_step globals.
Proof. solve_eq_simple_projection. Qed.

(** ** [runs_R_FunTab] **)

(** Not yet applicable **)


(** * [runs] is constant with enough fuel **)

(** If runs returns a result, then adding fuel does not change it. **)

(** ** [runs_while_loop] **)

Lemma runs_while_loop_fuel_conserve : forall A globals n n' S (a : A) expr body,
    n <= n' ->
    ~ bottom_result (runs_while_loop (runs n globals) S a expr body) ->
    runs_while_loop (runs n' globals) S a expr body = runs_while_loop (runs n globals) S a expr body.
Proof.
  introv I B. repeat rewrite runs_proj_while_loop_eq in *. gen n' S a expr body. induction n; introv I B.
  - false~ B.
  - destruct n'; try solve [ math ]. simpls.
    destruct expr; simpls~; tryfalse~. cases_if~.
    destruct body; simpls~; tryfalse~. rewrite~ IHn. math.
Qed.

(** ** [runs_set_longjump] **)

Lemma runs_set_longjump_fuel_conserve : forall A globals n n' S c m cont,
    n <= n' ->
    ~ bottom_result (runs_set_longjump (runs n globals) S c m cont : result A) ->
    runs_set_longjump (runs n' globals) S c m cont = runs_set_longjump (runs n globals) S c m cont.
Proof.
  introv I B. repeat rewrite runs_proj_set_longjump_eq in *. gen n' S c m cont. induction n; introv I B.
  - false~ B.
  - destruct n'; try solve [ math ]. simpls.
    destruct cont; simpls~; tryfalse~. cases_if~. rewrite~ IHn. math.
Qed.

(** ** [runs_R_cycle_detected] **)

(** This is quite a heavy proof for now. **)

(** ** [runs_eval] **)

(** This is quite a heavy proof for now. **)

(** ** [runs_getAttrib] **)

(** This is quite a heavy proof for now. **)

(** ** [runs_setAttrib] **)

(** This is quite a heavy proof for now. **)

(** ** [runs_duplicate1] **)

(** This is quite a heavy proof for now. **)

(** ** [runs_stripAttrib] **)

Lemma runs_stripAttrib_fuel_conserve : forall globals n n' S tag lst,
    n <= n' ->
    ~ bottom_result (runs_stripAttrib (runs n globals) S tag lst) ->
    runs_stripAttrib (runs n' globals) S tag lst = runs_stripAttrib (runs n globals) S tag lst.
Proof.
  introv I B. repeat rewrite runs_proj_stripAttrib_eq in *. gen n' S tag lst. induction n; introv I B.
  - false~ B.
  - destruct n'; try solve [ math ]. simpls. cases_if~.
    simplifyR. destruct read_SExp; simpls~; tryfalse~.
    unfolds if_is_list. destruct get_NonVector; simpls~. destruct get_listSxp; simpls~. cases_if~.
    + rewrite~ IHn.
      * math.
      * destruct~ runs_proj_stripAttrib.
    + rewrite~ IHn.
      * math.
      * destruct~ runs_proj_stripAttrib.
Qed.

(** This is quite a heavy proof for now. **)

(** ** [runs_evalseq] **)

(** This is quite a heavy proof for now. **)

(** ** [runs_R_isMissing] **)

(** This is quite a heavy proof for now. **)

(** ** [runs_AnswerType] **)

(** This is quite a heavy proof for now. **)

(** ** [runs_ListAnswer] **)

(** This is quite a heavy proof for now. **)

(** ** [runs_StringAnswer] **)

(** This is quite a heavy proof for now. **)

(** ** [runs_LogicalAnswer] **)

(** This is quite a heavy proof for now. **)

(** ** [runs_IntegerAnswer] **)

(** This is quite a heavy proof for now. **)

(** ** [runs_RealAnswer] **)

(** This is quite a heavy proof for now. **)

(** ** [runs_ComplexAnswer] **)

(** This is quite a heavy proof for now. **)

(** ** [runs_RawAnswer] **)

(** This is quite a heavy proof for now. **)

(** ** [runs_R_FunTab] **)

(** Not yet applicable **)

