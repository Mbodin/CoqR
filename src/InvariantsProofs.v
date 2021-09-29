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

From CoqR Require Import Rcore.
From CoqR Require Import RfeaturesAux.
From CoqR Require Import Rinit.
From CoqR Require Import InvariantsAux InvariantsTactics.
From Paco Require Import paco.


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
    S (a : A) expr stat,
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

Lemma fold_left_listSxp_gen_result : forall A S (a : A) l iterate l_t l_car l_tag
    (P_success : _ -> _ -> Prop) P_error P_longjump Pheader Pcar Ptag,
  safe_state S ->
  safe_globals S globals ->
  P_success S a ->
  list_type_such_that Pheader Pcar Ptag S l_t l_car l_tag l ->
  (forall (S : state) a l l_ l_header (l_list : ListSxp_struct),
    P_success S a ->
    safe_state S ->
    safe_globals S globals ->
    read_SExp S l = Some l_ ->
    l_ = make_NonVector_SExpRec l_header l_list ->
    list_type_head_such_that (list_type_such_that Pheader Pcar Ptag)
      Pheader Pcar Ptag S l_t l_car l_tag l_ ->
    result_prop (fun S a => safe_state S /\ safe_globals S globals
        /\ P_success S a
        /\ list_type_such_that Pheader Pcar Ptag S l_t l_car l_tag (list_cdrval l_list))
      P_error P_longjump (iterate S a l l_ l_list)) ->
  result_prop P_success P_error P_longjump
    (fold_left_listSxp_gen runs globals S l a iterate).
Proof.
  introv OKS OKg OKa L OKiterate. unfolds fold_left_listSxp_gen.
  cutR (fun S (la : SEXP * A) =>
          safe_state S /\ safe_globals S globals
          /\ list_type_such_that Pheader Pcar Ptag S l_t l_car l_tag (fst la)
          /\ P_success S (snd la)).
  - apply while_loop_result.
    + splits~.
    + clear - OKiterate. introv (OKS&OKg&L&OKa). destruct a as (l&a).
      unfolds @fst. unfolds @snd. simpl. splits~.
      introv D. rew_refl in D. inverts L as L.
      * false D. applys~ only_one_nil OKS. apply~ R_NilValue_may_have_types.
      * inverts L as (El&L). destruct L as (h&car&cdr&tag&Ex&Tx&Hh&Tcar&Hcar&L&Ttag&Htag).
        computeR. substs. computeR.
        cutR (fun S a => safe_state S /\ safe_globals S globals
          /\ P_success S a
          /\ list_type_such_that Pheader Pcar Ptag S l_t l_car l_tag cdr).
        -- apply~ OKiterate. constructors. exists* car cdr tag.
        -- lets (OKS0&OKg0&P'&L'): (rm P). simpl. splits~.
  - destruct a0. apply P.
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
  unfolds all_SExpTypes. explode_list_smart Ts; (cutR TYPEOF_result;
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
        explode_list_smart Ts'.
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
        explode_list_smart Ts'.
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
        explode_list_smart Ts'.
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
      /\ safe_globals S' globals
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

Lemma CHAR_result : forall S x,
  safe_state S ->
  safe_pointer S x ->
  may_have_types S ([CharSxp]) x ->
  result_prop (fun S' _ => S' = S) (fun _ => False) (fun _ _ _ => False)
    (CHAR S x).
Proof. introv OKS OKx Tx. unfolds CHAR. computeR. simpl. reflexivity. Qed.

Lemma iSDDName_result : forall S x,
  safe_state S ->
  safe_pointer S x ->
  may_have_types S ([CharSxp]) x ->
  result_prop (fun S' _ => S' = S) (fun _ => False) (fun _ _ _ => False)
    (iSDDName S x).
Proof.
  introv OKS OKx Tx. unfolds iSDDName. computeR.
  cutR CHAR_result. substs. cases_if; simpl; autos~.
Qed.

Lemma mkSYMSXP_result : forall S name value,
  safe_state S ->
  safe_globals S globals ->
  safe_pointer S name ->
  may_have_types S ([CharSxp]) name ->
  safe_pointer S value ->
  result_prop (fun S' sym =>
      conserve_old_bindings S S'
      /\ safe_state S'
      /\ safe_globals S' globals
      /\ safe_pointer S' sym
      /\ may_have_types S' ([SymSxp]) sym)
    (fun _ => False) (fun _ _ _ => False)
    (mkSYMSXP globals S name value).
Proof.
  introv OKS OKg OKname Tname OKvalue. unfolds mkSYMSXP. computeR.
  cutR iSDDName_result. substs. computeR.
  unfolds SET_DDVAL. cutR (fun S' (_ : unit) =>
      conserve_old_bindings S S'
      /\ safe_state S'
      /\ safe_globals S' globals
      /\ safe_pointer S' p
      /\ may_have_types S' ([SymSxp]) p).
  - apply add_stack_result. applys~ map_gp_result OKg.
    + applys~ read_bound E.
    + introv OKS' OKg' E' W. rewrite E in E'. inverts E'. simpl. splits~.
      * forwards (S2&ES2&EqS2): alloc_SExp_write_SExp_eq ES1 W.
        applys conserve_old_bindings_trans S2; solve_premises_smart.
      * applys~ map_gp_aux_safe_pointer W.
        rewrite safe_pointer_rewrite. constructors.
        -- (** pointer_bound **)
           applys* read_bound E.
        -- (** no_null_pointer_along_path_step **)
           introv NE M. unfolds in M. rewrite E in M. simpl in M.
           destruct s; inverts M.
           ++ solve_premises_smart.
           ++ destruct s; simpl; solve_premises_smart.
        -- (** safe_pointer_along_path_step **)
           introv M D'. unfolds in M. rewrite E in M. simpl in M.
           destruct s; inverts M.
           ++ solve_premises_smart.
           ++ destruct s; simpl; solve_premises_smart.
        -- (** safe_SExpRec_read **)
           introv R. rewrite E in R. inverts R. solve_premises_smart.
      * eexists. splits.
        -- applys read_write_SExp_eq W.
        -- simpl. Mem_solve.
  - introv (C1&OKS1'&OKg1&OKp&T1). simpl. splits~.
Qed.

Lemma install_result : forall S name_,
  safe_state S ->
  safe_globals S globals ->
  result_prop (fun S' sym =>
      safe_state S'
      /\ safe_globals S' globals
      /\ safe_pointer S' sym
      /\ may_have_types S' ([SymSxp]) sym)
    (fun _ => name_ = ""%string) (fun _ _ _ => False)
    (install globals runs S name_).
Proof.
  introv OKS OKg. unfolds install. computeR.
  set (Pret := fun S' ret =>
    match ret with
    | normal_result tt =>
      conserve_old_bindings S S' /\ safe_state S'
    | return_result sym =>
      safe_state S' /\ safe_globals S' globals
      /\ safe_pointer S' sym /\ may_have_types S' ([SymSxp]) sym
    end). cutR Pret.
  - forwards L: safe_SymbolTable OKS. unfolds fold_left_listSxp.
    applys~ fold_left_listSxp_gen_result L.
    + simpl. splits; solve_premises_smart.
    + introv Preta OKS0 OKg0 El El_ L'.
      destruct L' as (h&car&cdr&tag&Ex&Tx&Hh&Tcar&Hcar&L'&Ttag&Htag).
      rewrite Ex in El_. inverts El_. unfolds in Preta. destruct a as [()|sym].
      * lets (C&OKS0'): (rm Preta). computeR. cutR PRINTNAME_result.
        -- applys~ conserve_old_bindings_safe_pointer C.
        -- lets (C'&OKS1&OKa&Ta): (rm P).
           forwards C1: conserve_old_bindings_trans C C'.
           cutR CHAR_result. substs. cases_if; simpl.
           ++ repeat splits~.
              ** applys~ conserve_old_bindings_safe_globals OKg.
              ** applys~ conserve_old_bindings_safe_globals OKg.
              ** applys~ conserve_old_bindings_safe_pointer Hcar.
              ** applys~ conserve_old_bindings_may_have_types Tcar.
              ** applys~ conserve_old_bindings_list_type L'.
           ++ repeat splits~.
              ** applys~ conserve_old_bindings_safe_globals OKg.
              ** applys~ conserve_old_bindings_list_type L'.
      * simpl. lets (C&OKS0'&OKsym&Tsym): (rm Preta). splits; try solve_premises_smart.
  - destruct a. lets (C&OKs0): (rm P). cases_if as C0.
    + fold_bool. rew_refl in C0. apply~ C0.
    + unfolds mkChar. unfolds alloc_vector_char. computeR.
      match type of E with
      | read_SExp _ _ = Some ?p_ =>
        asserts OKp_: (safe_SExpRec S0 p_)
      end.
      { applys~ make_SExpRec_char_safe.
        - applys~ globals_not_NULL_safe; try solve_premises_smart.
          applys~ conserve_old_bindings_safe_globals OKg.
        - applys list_type_nil R_NilValue_may_have_types.
          applys~ conserve_old_bindings_safe_globals OKg. }
      cutR mkSYMSXP_result; try solve_premises_smart.
      * applys alloc_SExp_safe_state ES0; try solve_premises_smart.
      * applys~ conserve_old_bindings_safe_globals OKg.
        applys~ conserve_old_bindings_trans C C1.
      * rewrite safe_pointer_rewrite. constructors.
        -- (** pointer_bound **)
           solve_premises_smart.
        -- (** no_null_pointer_along_path_step **)
           destruct s; introv NE M; unfolds in M; rewrite E in M; simpl in M; inverts M as M.
           solve_premises_smart.
        -- (** safe_pointer_along_path_step **)
           destruct s; introv M D'; unfolds in M; rewrite E in M; simpl in M; inverts M as M.
           applys globals_not_NULL_safe; try solve_premises_smart.
           applys~ conserve_old_bindings_safe_globals OKg.
           applys~ conserve_old_bindings_trans C C1.
        -- (** safe_SExpRec_read **)
           introv E'. rewrite E' in E. inverts~ E.
           applys~ conserve_old_bindings_safe_SExpRec OKp_.
      * applys~ globals_not_NULL_safe.
        -- applys~ conserve_old_bindings_safe_globals OKg.
           applys~ conserve_old_bindings_trans C C1.
        -- solve_premises_smart.
      * lets (C12&OKS2&OKg2&OKa&Ta): (rm P). destruct CONS as (S3&SymbolTable) eqn: ECONS.
        forwards~ (OKS'&OKg'&OKl'&Ll'&C'): CONS_safe ECONS;
          try apply~ safe_SymbolTable; try solve_premises_smart.
        simpl. splits~.
        -- constructors.
           ++ (** no_null_pointer_entry_point **)
              introv NE M. destruct e; try solve [ applys~ no_null_pointer_entry_point OKS' NE ].
              ** applys~ no_null_pointer_entry_point OKS' NE.
                 simpl. erewrite move_along_context_path_same_contexts; try apply M; reflexivity.
              ** inverts M. solve_premises_smart.
           ++ (** safe_entry_points **)
              introv M D'. applys~ safe_pointer_same_memory S3. destruct e.
              ** simpl in M. erewrite move_along_context_path_same_contexts with (S2 := S3) in M; autos~.
                 applys~ safe_entry_points OKS' (Econtext c c0).
              ** inverts~ M.
              ** inverts M. applys~ safe_entry_points OKS' EReturnedValue.
              ** applys~ safe_entry_points OKS' (EasymSymbol n) D'.
           ++ (** only_one_nil **)
              apply OKS'.
           ++ (** safe_SymbolTable **)
              simpl. simpl_list_union. applys~ list_type_safe_same_memory Ll'.
        -- applys~ same_memory_safe_globals OKg'.
        -- applys~ safe_pointer_same_memory S3.
           applys~ conserve_old_bindings_safe_pointer OKa.
        -- applys~ may_have_types_same_memory S3.
           applys~ conserve_old_bindings_may_have_types Ta.
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
    simpl. applys~ list_type_safe_same_memory (safe_SymbolTable OKS).
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
    forwards L': safe_SymbolTable OKS.
    asserts_rewrite (R_SymbolTable S2 = R_SymbolTable S).
    { rewrites* >> state_same_except_for_memory_R_SymbolTable.
      forwards (S2'&ES2'&S2E): write_SExp_write_SExp_eq ES0 ES2.
      forwards (S3&ES3&S3E): alloc_SExp_write_SExp_eq ES1 ES2'.
      applys state_same_except_for_memory_trans S2E.
      applys state_same_except_for_memory_trans S3E.
      apply state_same_except_for_memory_sym.
      applys alloc_SExp_state_same_except_for_memory ES3. }
    applys~ conserve_old_bindings_list_type_safe L'.
  Optimize Proof.
Qed.

Lemma InitMemory_result : forall S,
  safe_state S ->
  safe_globals S globals ->
  result_prop (fun S' (res : _ * _ * _) =>
    let '(TrueValue, FalseValue, LogicalNAValue) := res in
    safe_state S' /\ safe_globals S' globals
    /\ safe_pointer S' TrueValue
    /\ safe_pointer S' FalseValue
    /\ safe_pointer S' LogicalNAValue)
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
  result_prop (fun S' (res : _ * _) =>
    let (EmptyEnv, BaseEnv) := res in
    safe_state S' /\ safe_globals S' globals
    /\ safe_pointer S' EmptyEnv
    /\ safe_pointer S' BaseEnv)
    (fun _ => False) (fun _ _ _ => False) (InitBaseEnv globals runs S).
Proof.
  introv OKS OKg. unfolds InitBaseEnv. computeR.
  cutR NewEnvironment_result; try solve_premises_smart.
  lets (C&OKS0&OKrho&OKa&Trho): (rm P). transition_conserve S S0.
  cutR NewEnvironment_result; try solve_premises_smart.
  lets (C'&OKS1&OKrho'&OKa'&Trho'): (rm P). transition_conserve S0 S1.
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

