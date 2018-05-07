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
Require Export InvariantsTactics.
Require Import Paco.paco.


Section Parameterised.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Hypothesis runs_while_loop_result : forall A (P_success : _ -> _ -> Prop) P_error P_longjump
    S (a : A) (expr stat : _ -> A -> _),
  P_success S a ->
  (forall S a,
    P_success S a ->
    result_prop (fun S (b : bool) =>
        P_success S a
        /\ (b -> result_prop P_success P_error P_longjump (stat S a)))
      P_error P_longjump (expr S a)) ->
  result_prop P_success P_error P_longjump (runs_while_loop runs S a expr stat).


(** * Lemmae about Rcore.v **)

Lemma read_R_FunTab_result : forall S n,
  (* FIXME: n < ArrayList.length ?? -> *)
  result_prop (fun S' _ => S' = S) (fun _ => False) (fun _ _ _ => False)
    (read_R_FunTab runs S n).
Proof.
  introv. unfolds read_R_FunTab. computeR.
  skip. (* TODO *)
Qed.

Lemma PRIMARITY_result : forall S x,
  safe_state S ->
  safe_pointer S x ->
  may_have_types S ([SpecialSxp; BuiltinSxp]) x ->
  result_prop (fun S' _ => S' = S) (fun _ => False) (fun _ _ _ => False)
    (PRIMARITY runs S x).
Proof.
  introv OKS OKx Tx. unfolds PRIMARITY. computeR.
  skip. (* TODO: cutR read_R_FunTab_result. *)
Qed.

Lemma PRIMINTERNAL_result : forall S x,
  safe_state S ->
  safe_pointer S x ->
  may_have_types S ([SpecialSxp; BuiltinSxp]) x ->
  result_prop (fun S' _ => S' = S) (fun _ => False) (fun _ _ _ => False)
    (PRIMINTERNAL runs S x).
Admitted. (* TODO *)

Lemma R_length_result : forall S s,
  safe_state S ->
  safe_pointer S s ->
  result_prop (fun S' _ => S' = S) (fun _ => False) (fun _ _ _ => False)
    (R_length globals runs S s).
Proof.
  introv OKS OKs. unfolds R_length. computeR.
  forwards Ts: bound_may_have_types S s.
  { solve_premises_smart. }
  unfolds all_SExpTypes.
  explode_list Ts; (cutR TYPEOF_result;
    [ apply Ts
    | lets (E&C): (rm P); substs; simpl; autos~ ]).
Admitted. (* TODO *)

(** * Lemmae about Rfeatures.v **)

Lemma Rf_checkArityCall_result : forall S op args call,
  safe_state S ->
  safe_pointer S op ->
  may_have_types S ([SpecialSxp; BuiltinSxp]) op ->
  safe_pointer S args ->
  safe_pointer S call ->
  result_prop (fun S' _ => S' = S) safe_state (fun _ _ _ => False)
    (Rf_checkArityCall globals runs S op args call).
Proof.
  introv OKS OKop Top OKargs OKcall. unfolds Rf_checkArityCall. computeR.
  cutR PRIMARITY_result. substs.
  cutR R_length_result. substs. cases_if.
  - computeR. cutR PRIMINTERNAL_result.
    substs. cases_if; simpl; autos~.
  - simpl. autos~.
Qed.

Lemma BodyHasBraces_result : forall S body,
  result_prop (fun S' _ => S' = S) (fun _ => False) (fun _ _ _ => False)
    (BodyHasBraces globals S body).
Proof.
  introv. unfolds BodyHasBraces. computeR.
  skip. (* TODO *)
Qed.

Lemma do_while_result : forall S call op args rho,
  safe_state S ->
  safe_globals S globals ->
  safe_pointer S call ->
  safe_pointer S op ->
  may_have_types S ([SpecialSxp; BuiltinSxp]) op ->
  safe_pointer S args ->
  may_have_types S ([NilSxp; ListSxp]) args ->
  safe_pointer S rho ->
  result_prop (fun S nil =>
      safe_state S /\ safe_pointer S nil /\ nil = R_NilValue)
    (fun S => safe_state S) (fun _ _ _ => False)
    (do_while globals runs S call op args rho).
Proof.
  introv OKS OKg OKcall OKop Top OKargs Targs OKrho. unfolds do_while. computeR.
  cutR Rf_checkArityCall_result. substs. computeR.
  unfolds list_cdrval. unfold_shape_pointer_one S cdr. computeR.
  cutR BodyHasBraces_result. substs.
  unfolds begincontext.
  match goal with |- context [ state_with_context _ ?cptr' ] => sets_eq cptr: cptr' end.
  sets_eq S': (state_with_context S cptr).
  computeR. cutR safe_state.
  - cases_if; skip. (* TODO *)
  - skip. (* TODO: lacks hypothesis about [runs_set_longjump]. *)
  - skip. (* TODO: Something is wrong here… *)
Qed.

(** * Lemmae about Rinit.v **)

Lemma InitConnections_result : forall S,
  safe_state S ->
  safe_state (InitConnections S).
Proof.
  introv OKS. unfold InitConnections.
  destruct S. unfolds update_R_Connections. unfolds update_R_OutputCon. simpl. constructors.
  - (** no_null_pointer_entry_point **)
    introv NE E. applys~ no_null_pointer_entry_point OKS NE.
    destruct~ e. rewrite <- E. simpl. fequals. applys~ move_along_context_path_same_contexts.
  - (** safe_entry_points **)
    introv E NN. forwards OKp: safe_entry_points OKS e NN.
    + destruct~ e. simpls. erewrite move_along_context_path_same_contexts; [ apply E | .. ]; reflexivity.
    + applys~ safe_pointer_same_memory OKp.
  - (** only_one_nil **)
    introv M1 M2. applys only_one_nil OKS; apply* may_have_types_same_memory.
Qed.

(** The function [init_R_NilValue] allocates a new [NilSxp]: we have
  to suppose that this is the first we ever allocated for the
  invariant to hold. **)
Lemma init_R_NilValue_result : forall S,
  safe_state S ->
  (forall p, ~ may_have_types S ([NilSxp]) p) ->
  result_prop (fun S NilValue => safe_state S /\ safe_pointer S NilValue)
    (fun _ => False) (fun _ _ _ => False) (init_R_NilValue S).
Proof.
  introv OKS N. unfold init_R_NilValue. computeR.
  asserts Ep: (forall p', may_have_types S2 ([NilSxp]) p' -> p = p').
  { introv M. tests Dp: (p = p'); [ autos~ |].
    false N p'.
    forwards~ M1: may_have_types_write_SExp_inv ES2 M.
    forwards~ M2: may_have_types_write_SExp_inv ES0 M1.
    forwards~ M3: conserve_old_binding_may_have_types_inv C M2.
    lets (p_&E'&_): may_have_types_bound M2.
    rewrites~ >> alloc_read_SExp_neq ES1 in E'.
    applys read_bound E'. }
  asserts OKp: (safe_pointer S2 p).
  { pcofix IH. pfold. constructors.
    - (** pointer_bound **)
      applys~ read_bound E.
    - (** no_null_pointer_along_path_step **)
      destruct s; introv NE M; unfolds in M; rewrite E in M; simpl in M; inverts M.
      + solve_premises_smart.
      + destruct s; simpl; solve_premises_smart.
    - (** safe_pointer_along_path_step **)
      destruct s; introv M D'; unfolds in M; rewrite E in M; simpl in M; inverts~ M.
      destruct s; simpls~.
    - (** safe_SExpRec_read **)
      introv E'. rewrite E in E'. inverts E'. constructors.
      + (** SExpType_corresponds_to_datatype **)
        simpl. constructors; solve_premises_smart.
      + (** SExpRec_header **)
        constructors; simpl.
        * (** safe_attrib **)
          autos~.
        * (** attrib_list **)
          apply~ list_type_nil. solve_premises_smart. }
  simpl. splits~. constructors.
  - (** no_null_pointer_entry_point **)
    introv. rewrites~ >> move_along_entry_point_write_SExp ES2.
    rewrites~ >> move_along_entry_point_write_SExp ES0.
    rewrites~ >> move_along_entry_point_alloc_SExp ES1.
    applys~ no_null_pointer_entry_point OKS.
  - (** safe_entry_points **)
    introv M Dp0. rewrites~ >> move_along_entry_point_write_SExp ES2 in M.
    rewrites~ >> move_along_entry_point_write_SExp ES0 in M.
    rewrites~ >> move_along_entry_point_alloc_SExp ES1 in M.
    forwards~ OKp0: safe_entry_points OKS M Dp0.
    apply (conserve_old_binding_safe_pointer C) in OKp0.
    tests Dp: (p0 = p).
    * apply OKp.
    * forwards~ OKp0': safe_entry_points M.
      applys conserve_old_binding_safe_pointer OKp0'.
      forwards (S1'&A1&E1): alloc_SExp_write_SExp_eq ES1 ES0.
      forwards (S2'&ES2'&E2): write_SExp_equiv_exists E1 ES2.
      forwards (S3'&A3&E3): alloc_SExp_write_SExp_eq A1 ES2'.
      applys conserve_old_binding_trans S3'.
      -- applys alloc_SExp_conserve_old_binding A3.
      -- applys state_equiv_conserve_old_binding.
         applys state_equiv_sym. applys state_equiv_trans E2 E3.
  - (** only_one_nil **)
    introv M1 M2. rewrites~ <- >> Ep M1.
Qed.

End Parameterised.

(** * Closing the loop **)

Lemma runs_while_loop_result : forall n globals
    A (P_success : _ -> _ -> Prop) P_error P_longjump
    S (a : A) (expr stat : _ -> A -> _),
  P_success S a ->
  (forall S a,
    P_success S a ->
    result_prop (fun S (b : bool) =>
        P_success S a
        /\ (b -> result_prop P_success P_error P_longjump (stat S a)))
      P_error P_longjump (expr S a)) ->
  result_prop P_success P_error P_longjump (runs_while_loop (runs n globals) S a expr stat).
Proof.
  introv OKS OKexpr. rewrite runs_proj_while_loop_eq.
  gen S a. induction n; introv OKS.
  - simpls~.
  - simpl. computeR. forwards Rexpr: OKexpr OKS. destruct expr eqn: E; autos~.
    lets (OKS'&OKstat): (rm Rexpr). computeR. cases_if.
    + destruct stat eqn: E'; autos~. computeR. apply~ IHn. apply~ OKstat.
    + apply~ OKS'.
Qed.

