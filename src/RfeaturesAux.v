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

Require Export Rfeatures.


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
Ltac compute_simple_projection proj :=
  let globals := fresh "globals" in
  let max_step := fresh "max_step" in
  let IHmax_step := fresh "IH" max_step in
  intros max_step globals;
  induction max_step as [|max_step IHmax_step];
  [ let r := eval simpl in (proj (runs 0 globals)) in exact r
  | let r := eval simpl in (proj (runs (S max_step) globals)) in
    let rec aux1 r :=
      match r with
      | context [ ?f (runs max_step globals) ] =>
        lazymatch f with
        | proj => fail
        | ?f' globals =>
          let r := eval unfold f' in r in
          let r := eval simpl in r in
          aux1 r
        | _ _ => fail
        | _ =>
          let r := eval unfold f in r in
          let r := eval simpl in r in
          aux1 r
        end
      | _ => r
      end in
    let r := aux1 r in
    let rec aux2 r :=
      match r with
      | context C [ proj (runs max_step globals) ] =>
        let r := context C[IHmax_step] in
        aux2 r
      | context C [ proj globals (runs max_step globals) ] =>
        let r := context C[IHmax_step] in
        aux2 r
      | _ => r
      end in
    let r := aux2 r in
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
  compute_simple_projection runs_while_loop.
Defined.

Lemma runs_proj_while_loop_eq : forall max_step globals,
  runs_while_loop (runs max_step globals) = runs_proj_while_loop max_step globals.
Proof. solve_eq_simple_projection. Qed.

(** ** [runs_set_longjump] **)

Definition runs_proj_set_longjump : ltac:(get_type_projection runs_set_longjump).
  compute_simple_projection runs_set_longjump.
Defined.

Lemma runs_proj_set_longjump_eq : forall max_step globals,
  runs_set_longjump (runs max_step globals) = runs_proj_set_longjump max_step globals.
Proof. solve_eq_simple_projection. Qed.

(** ** [runs_R_cycle_detected] **)

Definition runs_proj_R_cycle_detected : ltac:(get_type_projection runs_R_cycle_detected).
  compute_simple_projection runs_R_cycle_detected.
Defined.

Lemma runs_proj_R_cycle_detected_eq : forall max_step globals,
  runs_R_cycle_detected (runs max_step globals) = runs_proj_R_cycle_detected max_step globals.
Proof. solve_eq_simple_projection. Qed.

(** ** [runs_eval] **)

(** Unfortunately, this cases uses other functions, making it difficult to produce such a definition. **)

(** ** [runs_getAttrib] **)

(** Unfortunately, this cases uses other functions, making it difficult to produce such a definition. **)

(** ** [runs_setAttrib] **)

(** Unfortunately, this cases uses other functions, making it difficult to produce such a definition. **)

(** ** [runs_duplicate1] **)

(** Unfortunately, this cases uses other functions, making it difficult to produce such a definition. **)

(** ** [runs_stripAttrib] **)

Definition runs_proj_stripAttrib : ltac:(get_type_projection runs_stripAttrib).
  compute_simple_projection runs_stripAttrib.
Defined.

Lemma runs_proj_stripAttrib_eq : forall max_step globals,
  runs_stripAttrib (runs max_step globals) = runs_proj_stripAttrib max_step globals.
Proof. solve_eq_simple_projection. Qed.

(** ** [runs_evalseq] **)

(** Unfortunately, this cases uses other functions, making it difficult to produce such a definition. **)

(** ** [runs_R_isMissing] **)

(** Unfortunately, this cases uses other functions, making it difficult to produce such a definition. **)

(** ** [runs_AnswerType] **)

(** Unfortunately, this cases uses other functions, making it difficult to produce such a definition. **)

(** ** [runs_ListAnswer] **)

Definition runs_proj_ListAnswer : ltac:(get_type_projection runs_ListAnswer).
  compute_simple_projection runs_ListAnswer.
Defined.

Lemma runs_proj_ListAnswer_eq : forall max_step globals,
  runs_ListAnswer (runs max_step globals) = runs_proj_ListAnswer max_step globals.
Proof. solve_eq_simple_projection. Qed.

(** ** [runs_StringAnswer] **)

(** Unfortunately, this cases uses other functions, making it difficult to produce such a definition. **)

(** ** [runs_LogicalAnswer] **)

Definition runs_proj_LogicalAnswer : ltac:(get_type_projection runs_LogicalAnswer).
  compute_simple_projection runs_LogicalAnswer.
Defined.

Lemma runs_proj_LogicalAnswer_eq : forall max_step globals,
  runs_LogicalAnswer (runs max_step globals) = runs_proj_LogicalAnswer max_step globals.
Proof. solve_eq_simple_projection. Qed.

(** ** [runs_IntegerAnswer] **)

Definition runs_proj_IntegerAnswer : ltac:(get_type_projection runs_IntegerAnswer).
  compute_simple_projection runs_IntegerAnswer.
Defined.

Lemma runs_proj_IntegerAnswer_eq : forall max_step globals,
  runs_IntegerAnswer (runs max_step globals) = runs_proj_IntegerAnswer max_step globals.
Proof. solve_eq_simple_projection. Qed.

(** ** [runs_RealAnswer] **)

Definition runs_proj_RealAnswer : ltac:(get_type_projection runs_RealAnswer).
  compute_simple_projection runs_RealAnswer.
Defined.

Lemma runs_proj_RealAnswer_eq : forall max_step globals,
  runs_RealAnswer (runs max_step globals) = runs_proj_RealAnswer max_step globals.
Proof. solve_eq_simple_projection. Qed.

(** ** [runs_ComplexAnswer] **)

Definition runs_proj_ComplexAnswer : ltac:(get_type_projection runs_ComplexAnswer).
  compute_simple_projection runs_ComplexAnswer.
Defined.

Lemma runs_proj_ComplexAnswer_eq : forall max_step globals,
  runs_ComplexAnswer (runs max_step globals) = runs_proj_ComplexAnswer max_step globals.
Proof. solve_eq_simple_projection. Qed.

(** ** [runs_RawAnswer] **)

Definition runs_proj_RawAnswer : ltac:(get_type_projection runs_RawAnswer).
  compute_simple_projection runs_RawAnswer.
Defined.

Lemma runs_proj_RawAnswer_eq : forall max_step globals,
  runs_RawAnswer (runs max_step globals) = runs_proj_RawAnswer max_step globals.
Proof. solve_eq_simple_projection. Qed.

(** ** [runs_R_FunTab] **)

Definition runs_proj_R_FunTab : ltac:(get_type_projection runs_R_FunTab).
  compute_simple_projection runs_R_FunTab.
Defined.

Lemma runs_proj_R_FunTab_eq : forall max_step globals,
  runs_R_FunTab (runs max_step globals) = runs_proj_R_FunTab max_step globals.
Proof. solve_eq_simple_projection. Qed.

