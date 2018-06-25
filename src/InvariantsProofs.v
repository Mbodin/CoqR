(** InvariantsProofs.
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

Require Import Rcore.
Require Import RfeaturesAux.
Require Import Rinit.
Require Import InvariantsAux InvariantsTactics.
Require Import Paco.paco.


Section Parameterised.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Hypothesis runs_max_step : exists max_step, runs = Rfeatures.runs max_step globals.

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

Lemma while_loop_result : forall A (P_success : _ -> _ -> Prop) P_error P_longjump
    S (a : A) (expr stat : _ -> A -> _),
  P_success S a ->
  (forall S a,
    P_success S a ->
    result_prop (fun S (b : bool) =>
        P_success S a
        /\ (b -> result_prop P_success P_error P_longjump (stat S a)))
      P_error P_longjump (expr S a)) ->
  result_prop P_success P_error P_longjump (while_loop runs S a expr stat).
Proof.
  introv OKa OKexpr. unfolds while_loop. computeR.
  forwards Rexpr: OKexpr OKa. destruct expr eqn: E; autos~.
  lets (OKS'&OKstat): (rm Rexpr). computeR. cases_if.
  - destruct stat eqn: E'; autos~. computeR.
    applys~ runs_while_loop_result OKstat.
  - apply~ OKS'.
Qed.


(** * Lemmae about Rcore.v **)

Lemma read_R_FunTab_result : forall S n,
  safe_offset n ->
  result_prop (fun S' _ => S' = S) (fun _ => False) (fun _ _ _ => False)
    (read_R_FunTab runs S n).
Proof.
  introv OKn. unfolds in OKn.
  forwards (max_step&Eruns): runs_max_step. rewrite Eruns in *.
  unfolds read_R_FunTab. computeR.
  forwards OKn': (rm OKn) max_step globals S. destruct Rfeatures.runs.
  destruct runs_R_FunTab eqn: E'; simpls; autos~. cases_if; simpl; autos*.
Qed.

Lemma PRIMARITY_result : forall S x,
  safe_pointer S x ->
  may_have_types S ([SpecialSxp; BuiltinSxp]) x ->
  result_prop (fun S' _ => S' = S) (fun _ => False) (fun _ _ _ => False)
    (PRIMARITY runs S x).
Proof. introv OKx Tx. unfolds PRIMARITY. computeR. cutR read_R_FunTab_result. Qed.

Lemma PRIMINTERNAL_result : forall S x,
  safe_pointer S x ->
  may_have_types S ([SpecialSxp; BuiltinSxp]) x ->
  result_prop (fun S' _ => S' = S) (fun _ => False) (fun _ _ _ => False)
    (PRIMINTERNAL runs S x).
Proof. introv OKx Tx. unfolds PRIMINTERNAL. computeR. cutR read_R_FunTab_result. Qed.

Lemma isLanguage_result : forall S (s : SEXP),
  safe_pointer S s ->
  result_prop (fun S' (il : bool) =>
       S' = S /\ (il <-> s = R_NilValue \/ may_have_types S ([LangSxp]) s))
    (fun _ => False) (fun _ _ _ => False)
    (isLanguage globals S s).
Proof.
  introv OKs. unfolds isLanguage. computeR.
  rewrite safe_pointer_rewrite in OKs. forwards (s_&R&_): pointer_bound OKs.
  forwards*: read_SExp_may_have_types_read_exact R.
  cutR TYPEOF_result; [ eassumption |]. lets (?&?): (rm P). substs. simpl. splits~.
  rew_refl. iff [EN|EL]; autos~.
  - rewrite EL in *. autos~.
  - right. applys~ may_have_types_merge_singl EL.
Qed.

Lemma R_length_result : forall S s,
  safe_state S ->
  safe_globals S globals ->
  safe_pointer S s ->
  result_prop (fun S' _ => S' = S) (fun _ => False) (fun _ _ _ => False)
    (R_length globals runs S s).
Proof.
  introv OKS OKg OKs. unfolds R_length. computeR.
  forwards Ts: bound_may_have_types S s.
  { solve_premises_smart. }
  unfolds all_SExpTypes. explode_list Ts; (cutR TYPEOF_result;
      [ apply Ts
      | lets (E&C): (rm P); substs; simpl; autos~ ]);
    computeR; try solve_premises_smart.
  - cutR (fun S' (si : _ * nat) =>
      let (s, i) := si in
        S' = S /\ safe_pointer S s
        /\ may_have_types S ([NilSxp; ListSxp]) s).
    + apply~ while_loop_result.
      * splits~; solve_premises_smart.
      * introv. destruct a. introv (?&OKs'&Ts').
        substs. simpl. splits~. introv D. rew_refl in D. lets (D1&D2): (rm D).
        explode_list Ts'.
        -- false D2. applys~ only_one_nil OKS. solve_premises_smart.
        -- computeR. simpls. splits~; solve_premises_smart.
    + destruct a. lets (?&OKs'&Ts'): (rm P). substs. simpl. reflexivity.
  - cutR (fun S' (si : _ * nat) =>
      let (s, i) := si in
        S' = S /\ safe_pointer S s
        /\ may_have_types S ([NilSxp; ListSxp; LangSxp]) s).
    + apply~ while_loop_result.
      * splits~; solve_premises_smart.
      * introv. destruct a. introv (?&OKs'&Ts').
        substs. simpl. splits~. introv D. rew_refl in D. lets (D1&D2): (rm D).
        explode_list Ts'.
        -- false D2. applys~ only_one_nil OKS. solve_premises_smart.
        -- computeR. simpls. splits~; solve_premises_smart.
        -- computeR. simpls. splits~; solve_premises_smart.
    + destruct a. lets (?&OKs'&Ts'): (rm P). substs. simpl. reflexivity.
  - cutR (fun S' (si : _ * nat) =>
      let (s, i) := si in
        S' = S /\ safe_pointer S s
        /\ may_have_types S ([NilSxp; ListSxp; DotSxp]) s).
    + apply~ while_loop_result.
      * splits~; solve_premises_smart.
      * introv. destruct a. introv (?&OKs'&Ts').
        substs. simpl. splits~. introv D. rew_refl in D. lets (D1&D2): (rm D).
        explode_list Ts'.
        -- false D2. applys~ only_one_nil OKS. solve_premises_smart.
        -- computeR. simpls. splits~; solve_premises_smart.
        -- computeR. simpls. splits~; solve_premises_smart.
    + destruct a. lets (?&OKs'&Ts'): (rm P). substs. simpl. reflexivity.
  - destruct s0_; tryfalse; simpl; autos~.
  Optimize Proof.
Qed.

(** For now, we only provide this simplified version.
  A more general version would accept the types [NilSxp] and [ListSxp]
  for the arguments [namelist] and [valuelist]. **) (* FIXME: Is it easy to generalize? *)
Lemma NewEnvironment_result : forall S namelist valuelist rho,
  safe_state S ->
  safe_globals S globals ->
  safe_pointer S namelist ->
  may_have_types S ([NilSxp]) namelist ->
  safe_pointer S valuelist ->
  may_have_types S ([NilSxp]) valuelist ->
  safe_pointer S rho ->
  may_have_types S ([NilSxp; EnvSxp]) rho ->
  result_prop (fun S' newrho =>
      conserve_old_bindings S S'
      /\ safe_state S'
      /\ safe_pointer S' newrho
      /\ may_have_types S' ([EnvSxp]) newrho)
    (fun _ => False) (fun _ _ _ => False)
    (NewEnvironment globals runs S namelist valuelist rho).
Proof.
  introv OKS OKg OKnamelist Tnamelist OKvaluelist Tvaluelist OKrho Trho.
  asserts OKenv: (safe_SExpRec S (make_SExpRec_env R_NilValue valuelist rho)).
  { unfolds @id. constructors.
    - (** SExpType_corresponds_to_datatype **)
      simpl. constructors; solve_premises_smart.
    - (** SExpRec_header **)
      constructors; simpl.
      + (** safe_attrib **)
        applys~ globals_not_NULL_safe. solve_premises_smart.
      + (** attrib_list **)
        apply~ list_type_nil. apply~ OKg. }
  unfolds NewEnvironment. computeR.
  asserts OKS0: (safe_state S0).
  { applys~ alloc_SExp_safe_state OKS ES1. solve_premises_smart. }
  cutR (fun S' => S' = S0).
  - unfolds while_loop. simplifyR. cases_if as D'.
    + fold_bool. rew_refl in D'. lets (D'1&D'2): (rm D'). false D'1.
      applys~ only_one_nil S0; solve_premises_smart.
    + reflexivity.
  - destruct a. simpl. substs. splits~; try solve_premises_smart. pfold. constructors.
    + (** pointer_bound **)
      solve_premises_smart.
    + (** no_null_pointer_along_path_step **)
      destruct s; introv NE M; unfolds in M; rewrite E in M; simpl in M; inverts M as M.
      * destruct s; inverts M; try solve_premises_smart.
        destruct s; simpl; solve_premises_smart.
      * destruct s; inverts M; try solve_premises_smart.
        destruct s; simpl; solve_premises_smart.
    + (** safe_pointer_along_path_step **)
      destruct s; introv M D'; unfolds in M; rewrite E in M; simpl in M; inverts M as M.
      * destruct s; inverts M; try solve_premises_smart.
        destruct s; simpl; solve_premises_smart.
      * destruct s; inverts M; try solve_premises_smart.
        destruct s; simpl; solve_premises_smart.
    + (** safe_SExpRec_read **)
      introv E'. rewrite E in E'. inverts E'. solve_premises_smart.
  Optimize Proof.
Qed.

Lemma PRINTNAME_result : forall S x,
  safe_state S ->
  safe_pointer S x ->
  may_have_types S ([SymSxp]) x ->
  result_prop (fun S' name =>
      conserve_old_bindings S S'
      /\ safe_state S'
      /\ safe_pointer S' name
      /\ may_have_types S' ([CharSxp]) name)
    (fun _ => False) (fun _ _ _ => False)
    (PRINTNAME S x).
Proof.
  introv OKS OKx Tx. unfolds PRINTNAME. computeR.
  simpl. splits; try solve_premises_smart.
Qed.

Lemma install_result : forall S name_,
  safe_state S ->
  safe_globals S globals ->
  result_prop (fun S' sym =>
      conserve_old_bindings S S'
      /\ safe_state S'
      /\ safe_pointer S' sym
      /\ may_have_types S' ([SymSxp]) sym)
    (fun _ => False) (fun _ _ _ => False)
    (install globals runs S name_).
Proof.
  introv OKS OKg. unfolds install. computeR.
  set (Pret := fun S' ret =>
    match ret with
    | normal_result tt =>
      conserve_old_bindings S S' /\ safe_state S'
    | return_result sym =>
      conserve_old_bindings S S' /\ safe_state S' /\
      safe_pointer S' sym /\ may_have_types S' ([SymSxp]) sym
    end). cutR Pret.
  - forwards L: safe_SymbolTable OKS. unfolds in L.
    sets_eq ll: ([ListSxp]). sets_eq lcar: ([SymSxp]). sets_eq ltag: ([NilSxp]).
    sets_eq sbt: (R_SymbolTable S). asserts OKsbt: (safe_pointer S sbt).
    { substs. solve_premises_smart. }
    clear EQsbt. induction L using list_type_ind.
    + computeR. forwards* Ep: only_one_nil OKS R_NilValue_may_have_types.
      rewrite <- Ep. rewrite fold_left_listSxp_nil. simpl.
      splits; solve_premises_smart.
    + substs. rewrite fold_left_listSxp_cons.
      * computeR. cutR Pret.
        -- cutR PRINTNAME_result.
           ++ solve_premises_smart.
           ++ lets (C&OKS0&OKa&Ta): (rm P). skip. (* TODO *)
        -- skip. (* TODO: This is not the same for [apply IHL]. *)
      * introv E. substs. forwards (Nv&Ev&Tv): R_NilValue_may_have_types OKg.
        unfolds Globals.read_globals. rewrite Ev in *. skip. (* [Tv] vs [H] and [H1]. *)
  - skip.
  Optimize Proof.
Qed.


(** * Lemmae about Rfeatures.v **)

Lemma Rf_checkArityCall_result : forall S op args call,
  safe_state S ->
  safe_globals S globals ->
  safe_pointer S op ->
  may_have_types S ([SpecialSxp; BuiltinSxp]) op ->
  safe_pointer S args ->
  safe_pointer S call ->
  result_prop (fun S' _ => S' = S) safe_state (fun _ _ _ => False)
    (Rf_checkArityCall globals runs S op args call).
Proof.
  introv OKS OKg OKop Top OKargs OKcall. unfolds Rf_checkArityCall. computeR.
  cutR PRIMARITY_result. substs.
  cutR R_length_result. substs. cases_if.
  - computeR. cutR PRIMINTERNAL_result.
    substs. cases_if; simpl; autos~.
  - simpl. autos~.
  Optimize Proof.
Qed.

Lemma BodyHasBraces_result : forall S body,
  safe_state S ->
  safe_globals S globals ->
  safe_pointer S body ->
  result_prop (fun S' _ => S' = S) (fun _ => False) (fun _ _ _ => False)
    (BodyHasBraces globals S body).
Proof.
  introv OKS OKg OKbody. unfolds BodyHasBraces. computeR.
  cutR isLanguage_result. lets (?&(I&_)): (rm P). substs. cases_if.
  - forwards~ [EN|EL]: (rm I); substs.
    + forwards~ T: R_NilValue_may_have_types OKg. fold read_globals in T. computeR.
      solve_premises_smart.
    + computeR. solve_premises_smart.
  - simpl. autos~.
Qed.

(* This lemmae is about [do_while_result], which can call arbitrary R code.
  We leave this proof for when the whole of our interpreter will have been
  proven holding our invariants. (* FIXME
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
  unfolds list_cdrval. unfold_shape_pointer_one S cdr. computeR. fold read_globals.
  cutR BodyHasBraces_result; try solve_premises_smart. substs.
  unfolds begincontext.
  match goal with |- context [ state_with_context _ ?cptr' ] => sets_eq cptr: cptr' end.
  sets_eq S': (state_with_context S cptr). computeR. cutR safe_state.
  - cases_if as C; fold_bool; rew_refl in C.
    + skip. (* TODO: while. *)
    + computeR. skip. (* TODO: endcontext. *)
  - skip. (* TODO: lacks hypothesis about [runs_set_longjump]. *)
  - skip. (* TODO: Something is wrong here… *)
  Optimize Proof.
Qed.
*) *)


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
  - (** safe_SymbolTable **)
    simpl. applys~ list_type_same_memory (safe_SymbolTable OKS).
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
  introv OKS N. unfold init_R_NilValue.
  forwards L: safe_SymbolTable OKS. computeR.
  asserts Ep: (forall p', may_have_types S2 ([NilSxp]) p' -> p = p').
  { introv M. tests Dp: (p = p'); [ autos~ |].
    false N p'.
    forwards~ M1: may_have_types_write_SExp_inv ES2 M.
    forwards~ M2: may_have_types_write_SExp_inv ES0 M1.
    forwards~ M3: conserve_old_bindings_may_have_types_inv C M2.
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
  asserts C': (conserve_old_bindings S S2).
  { forwards (S2'&ES2'&S2E): write_SExp_write_SExp_eq ES0 ES2.
    forwards (S3&ES3&S3E): alloc_SExp_write_SExp_eq ES1 ES2'.
    applys conserve_old_bindings_trans S3.
    - solve_premises_smart.
    - apply state_equiv_conserve_old_bindings. apply state_equiv_sym.
      applys state_equiv_trans S2E S3E. }
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
    apply (conserve_old_bindings_safe_pointer C) in OKp0.
    tests Dp: (p0 = p).
    * apply OKp.
    * forwards~ OKp0': safe_entry_points M.
      applys conserve_old_bindings_safe_pointer OKp0'.
      forwards (S1'&A1&E1): alloc_SExp_write_SExp_eq ES1 ES0.
      forwards (S2'&ES2'&E2): write_SExp_equiv_exists E1 ES2.
      forwards (S3'&A3&E3): alloc_SExp_write_SExp_eq A1 ES2'.
      applys conserve_old_bindings_trans S3'.
      -- applys alloc_SExp_conserve_old_bindings A3.
      -- applys state_equiv_conserve_old_bindings.
         applys state_equiv_sym. applys state_equiv_trans E2 E3.
  - (** only_one_nil **)
    introv M1 M2. rewrites~ <- >> Ep M1.
  - (** safe_SymbolTable **)
    applys~ conserve_old_bindings_list_type C'.
    asserts_rewrite (R_SymbolTable S2 = R_SymbolTable S).
    { rewrites* >> state_same_except_for_memory_R_SymbolTable.
      forwards (S2'&ES2'&S2E): write_SExp_write_SExp_eq ES0 ES2.
      forwards (S3&ES3&S3E): alloc_SExp_write_SExp_eq ES1 ES2'.
      applys state_same_except_for_memory_trans S2E.
      applys state_same_except_for_memory_trans S3E.
      apply state_same_except_for_memory_sym.
      applys alloc_SExp_state_same_except_for_memory ES3. }
    applys safe_SymbolTable OKS.
  Optimize Proof.
Qed.

Lemma InitMemory_result : forall S,
  safe_state S ->
  safe_globals S globals ->
  result_prop (fun S (res : _ * _ * _) =>
    let '(TrueValue, FalseValue, LogicalNAValue) := res in
    safe_state S
    /\ safe_pointer S TrueValue
    /\ safe_pointer S FalseValue
    /\ safe_pointer S LogicalNAValue)
    (fun _ => False) (fun _ _ _ => False) (InitMemory globals S).
Proof.
  introv OKS OKg. unfolds InitMemory. unfolds mkTrue, mkFalse, alloc_vector_lgl.
  computeR. simpl. splits~.
  - pfold. constructors.
    + (** pointer_bound **)
      solve_premises_smart.
    + (** no_null_pointer_along_path_step **)
      destruct s; introv NE M; unfolds in M; rewrite E in M; simpl in M; inverts M.
      solve_premises_smart.
    + (** safe_pointer_along_path_step **)
      destruct s; introv M D'; unfolds in M; rewrite E in M; simpl in M; inverts~ M.
      left. pfold. solve_premises_smart.
    + (** safe_SExpRec_read **)
      introv E'. rewrite E in E'. inverts E'. solve_premises_smart.
  - pfold. constructors.
    + (** pointer_bound **)
      solve_premises_smart.
    + (** no_null_pointer_along_path_step **)
      destruct s; introv NE M; unfolds in M; rewrite E0 in M; simpl in M; inverts M.
      solve_premises_smart.
    + (** safe_pointer_along_path_step **)
      destruct s; introv M D'; unfolds in M; rewrite E0 in M; simpl in M; inverts~ M.
      left. pfold. solve_premises_smart.
    + (** safe_SExpRec_read **)
      introv E'. rewrite E0 in E'. inverts E'. solve_premises_smart.
  - pfold. constructors.
    + (** pointer_bound **)
      solve_premises_smart.
    + (** no_null_pointer_along_path_step **)
      destruct s; introv NE M; unfolds in M; rewrite E1 in M; simpl in M; inverts M.
      solve_premises_smart.
    + (** safe_pointer_along_path_step **)
      destruct s; introv M D'; unfolds in M; rewrite E1 in M; simpl in M; inverts~ M.
      left. pfold. solve_premises_smart.
    + (** safe_SExpRec_read **)
      introv E'. rewrite E1 in E'. inverts E'. solve_premises_smart.
  Optimize Proof.
Qed.

Lemma InitBaseEnv_result : forall S,
  safe_state S ->
  safe_globals S globals ->
  result_prop (fun S (res : _ * _) =>
    let (EmptyEnv, BaseEnv) := res in
    safe_state S
    /\ safe_pointer S EmptyEnv
    /\ safe_pointer S BaseEnv)
    (fun _ => False) (fun _ _ _ => False) (InitBaseEnv globals runs S).
Proof.
  introv OKS OKg. unfolds InitBaseEnv. computeR.
  cutR NewEnvironment_result; try solve_premises_smart.
  lets (C&OKS0&OKrho&Trho): (rm P). transition_conserve S S0.
  cutR NewEnvironment_result; try solve_premises_smart.
  lets (C'&OKS1&OKrho'&Trho'): (rm P). transition_conserve S0 S1.
  simpl. splits~.
  Optimize Proof.
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
  introv OKa OKexpr. rewrite runs_proj_while_loop_eq.
  gen S a. induction n; introv OKa.
  - simpls~.
  - simpl. computeR. forwards Rexpr: OKexpr OKa. destruct expr eqn: E; autos~.
    lets (OKa'&OKstat): (rm Rexpr). computeR. cases_if.
    + destruct stat eqn: E'; autos~. computeR. apply~ IHn. apply~ OKstat.
    + apply~ OKa'.
Qed.

