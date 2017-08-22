(** Globals.
  * Lists all global variables used in the C source code of R,
  * that are initialised, then never changed. **)


Require Export RinternalsAux.


(** Global variables that are initialised once, then treated as
  constants.  They are initialised in the file Rinit.v. **)
Record Globals := make_Globals {
    R_AsCharacterSymbol : SExpRec_pointer ;
    R_BaseEnv : SExpRec_pointer ;
    R_BaseNamespaceName : SExpRec_pointer ;
    R_BaseNamespace : SExpRec_pointer ;
    R_BaseSymbol : SExpRec_pointer ;
    R_BraceSymbol : SExpRec_pointer ;
    R_Bracket2Symbol : SExpRec_pointer ;
    R_BracketSymbol : SExpRec_pointer ;
    R_ClassSymbol : SExpRec_pointer ;
    R_ColonSymbol : SExpRec_pointer ;
    R_CommentSymbol : SExpRec_pointer ;
    R_ConnIdSymbol : SExpRec_pointer ;
    R_DevicesSymbol : SExpRec_pointer ;
    R_DeviceSymbol : SExpRec_pointer ;
    R_DimNamesSymbol : SExpRec_pointer ;
    R_DimSymbol : SExpRec_pointer ;
    R_DollarSymbol : SExpRec_pointer ;
    R_dot_Class : SExpRec_pointer ;
    R_dot_defined : SExpRec_pointer ;
    R_DotEnvSymbol : SExpRec_pointer ;
    R_dot_GenericCallEnv : SExpRec_pointer ;
    R_dot_GenericDefEnv : SExpRec_pointer ;
    R_dot_Generic : SExpRec_pointer ;
    R_dot_Group : SExpRec_pointer ;
    R_dot_Method : SExpRec_pointer ;
    R_dot_Methods : SExpRec_pointer ;
    R_dot_packageName : SExpRec_pointer ;
    R_DotsSymbol : SExpRec_pointer ;
    R_dot_target : SExpRec_pointer ;
    R_DoubleColonSymbol : SExpRec_pointer ;
    R_DropSymbol : SExpRec_pointer ;
    R_EmptyEnv : SExpRec_pointer ;
    R_ExactSymbol : SExpRec_pointer ;
    R_FalseValue : SExpRec_pointer ;
    R_GlobalEnv : SExpRec_pointer ;
    R_LevelsSymbol : SExpRec_pointer ;
    R_LogicalNAValue : SExpRec_pointer ;
    R_MethodsNamespace : SExpRec_pointer ;
    R_MissingArg : SExpRec_pointer ;
    R_ModeSymbol : SExpRec_pointer ;
    R_NamespaceEnvSymbol : SExpRec_pointer ;
    R_NamespaceRegistry : SExpRec_pointer ;
    R_NamespaceSymbol : SExpRec_pointer ;
    R_NamesSymbol : SExpRec_pointer ;
    R_NameSymbol  : SExpRec_pointer ;
    R_NaRmSymbol : SExpRec_pointer ;
    R_NilValue : SExpRec_pointer ;
    R_PackageSymbol : SExpRec_pointer ;
    R_PreviousSymbol : SExpRec_pointer ;
    R_QuoteSymbol : SExpRec_pointer ;
    R_RecursiveSymbol : SExpRec_pointer ;
    R_RowNamesSymbol : SExpRec_pointer ;
    R_SeedsSymbol : SExpRec_pointer ;
    R_SortListSymbol : SExpRec_pointer ;
    R_SourceSymbol : SExpRec_pointer ;
    R_SpecSymbol : SExpRec_pointer ;
    R_SrcfileSymbol : SExpRec_pointer ;
    R_SrcrefSymbol : SExpRec_pointer ;
    R_TmpvalSymbol : SExpRec_pointer ;
    R_TripleColonSymbol : SExpRec_pointer ;
    R_TrueValue : SExpRec_pointer ;
    R_TspSymbol : SExpRec_pointer ;
    R_UnboundValue : SExpRec_pointer ;
    R_UseNamesSymbol : SExpRec_pointer ;
    R_WholeSrcrefSymbol : SExpRec_pointer ;
  }.


(** We are going to update structures of type [Globals] a lot of time
 * in Module Rinit. There is unfortunately no [{o with f := v}] syntax
 * in Coq. As we are going to need it (as it helps avoid mistakes in
 * this particular case), we implement a specialised version in Ltac. **)

(** Here follows a list of all the projections of [Globals]. **)
Definition Globals_projections :=
  [ R_AsCharacterSymbol ;
    R_BaseEnv ;
    R_BaseNamespaceName ;
    R_BaseNamespace ;
    R_BaseSymbol ;
    R_BraceSymbol ;
    R_Bracket2Symbol ;
    R_BracketSymbol ;
    R_ClassSymbol ;
    R_ColonSymbol ;
    R_CommentSymbol ;
    R_ConnIdSymbol ;
    R_DevicesSymbol ;
    R_DeviceSymbol ;
    R_DimNamesSymbol ;
    R_DimSymbol ;
    R_DollarSymbol ;
    R_dot_Class ;
    R_dot_defined ;
    R_DotEnvSymbol ;
    R_dot_GenericCallEnv ;
    R_dot_GenericDefEnv ;
    R_dot_Generic ;
    R_dot_Group ;
    R_dot_Method ;
    R_dot_Methods ;
    R_dot_packageName ;
    R_DotsSymbol ;
    R_dot_target ;
    R_DoubleColonSymbol ;
    R_DropSymbol ;
    R_EmptyEnv ;
    R_ExactSymbol ;
    R_FalseValue ;
    R_GlobalEnv ;
    R_LevelsSymbol ;
    R_LogicalNAValue ;
    R_MethodsNamespace ;
    R_MissingArg ;
    R_ModeSymbol ;
    R_NamespaceEnvSymbol ;
    R_NamespaceRegistry ;
    R_NamespaceSymbol ;
    R_NamesSymbol ;
    R_NameSymbol  ;
    R_NaRmSymbol ;
    R_NilValue ;
    R_PackageSymbol ;
    R_PreviousSymbol ;
    R_QuoteSymbol ;
    R_RecursiveSymbol ;
    R_RowNamesSymbol ;
    R_SeedsSymbol ;
    R_SortListSymbol ;
    R_SourceSymbol ;
    R_SpecSymbol ;
    R_SrcfileSymbol ;
    R_SrcrefSymbol ;
    R_TmpvalSymbol ;
    R_TripleColonSymbol ;
    R_TrueValue ;
    R_TspSymbol ;
    R_UnboundValue ;
    R_UseNamesSymbol ;
    R_WholeSrcrefSymbol ].

(** No projection is missing in [Globals_projections]. **)
Lemma Globals_projections_all : forall g g',
  (forall C, Mem C Globals_projections -> C g = C g') ->
  g = g'.
Proof.
  introv F. destruct g, g'.
  let rec t l :=
    match l with
    | nil => reflexivity
    | ?C :: ?l' =>
      forwards E: F C;
      [ repeat constructors
      | simpl in E; rewrite E; clear E ];
      t l'
    end in
  let l := eval unfold Globals_projections in Globals_projections in
  t l.
Qed.


(** The following property translates the [{o with f := v}] syntax from
 * OCaml as a property. Intuitively, we have
 * [globals_with g [(C1, p1);... ; (Cn, pn)] g'] if and only if
 * [g' = {g with C1 := p1, ..., Cn := pn}]. **)
Record globals_with g (L : list ((Globals -> SExpRec_pointer) * SExpRec_pointer)) g' := {
    globals_with_in : forall C p,
      Mem (C, p) L ->
      C g' = p ;
    globals_with_out : forall C,
      (forall p, ~ Mem (C, p) L) ->
      Mem C Globals_projections ->
      C g' = C g ;
  }.

Lemma globals_with_empty : forall g g',
  globals_with g nil g' <-> g = g'.
Proof.
  iff G.
  - apply Globals_projections_all. introv M.
    symmetry. applys~ globals_with_out G. introv M'. inverts M'.
  - constructors.
    + introv M. inverts M.
    + introv F M. rewrite~ G.
Qed.

Lemma globals_with_transitive : forall g1 g2 g3 L1 L2 L1',
  globals_with g1 L1 g2 ->
  (forall C v, Mem (C, v) L1 -> Mem C Globals_projections) ->
  globals_with g2 L2 g3 ->
  Filter (fun C_v => ~ exists v, Mem (fst C_v, v) L2) L1 = L1' ->
  globals_with g1 (L1' ++ L2) g3.
Proof.
  introv G1 I G2 F. rewrite <- F. clear F. constructors.
  - introv M. rewrite Mem_app_or_eq in M. inverts M as M.
    + forwards (M'&NE): Filter_Mem_inv M.
      erewrite globals_with_out with (g := g2).
      * erewrite globals_with_in.
        -- reflexivity.
        -- apply G1.
        -- autos~.
      * apply G2.
      * rew_logic~ in NE.
      * applys I M'.
    + erewrite globals_with_in.
      * reflexivity.
      * apply G2.
      * autos~.
  - introv NM M. erewrite globals_with_out with (g := g2).
    + erewrite globals_with_out with (g := g1).
      * reflexivity.
      * apply~ G1.
      * introv M1. eapply NM. rewrite Mem_app_or_eq. left. applys Filter_Mem M1.
        introv (v&M2). false NM. rewrite Mem_app_or_eq. right*.
      * autos~.
    + apply G2.
    + introv M'. false NM. rewrite Mem_app_or_eq. right*.
    + autos~.
Qed.

Lemma globals_with_transitive_step : forall g1 g2 g3 C1 v1 L2,
  globals_with g1 [(C1, v1)] g2 ->
  Mem C1 Globals_projections ->
  (forall v, ~ Mem (C1, v) L2) ->
  globals_with g2 L2 g3 ->
  globals_with g1 ((C1, v1) :: L2) g3.
Proof.
  introv G1 M F G2. forwards~ G: globals_with_transitive G1 G2.
  - introv M'. inverts M' as M'.
    + autos~.
    + inverts M'.
  - rewrite Filter_cons in G. rewrite Filter_nil in G. cases_if as I.
    + apply G.
    + lets (v&MI): (rm I). false* F.
Qed.


(** Solves a goal of the form [{g' | globals_with g L g'}] with an instanciated [L]. **)
Ltac solve_globals_with :=
  let g := fresh "g" in
  refine (let g := make_Globals in _); repeat refine (let g := g _ in _);
  exists g; constructors;
  [ let M := fresh "M" in introv M;
    repeat (inverts M as M; [ simpl; reflexivity |]); inverts M
  | let NM := fresh "NM" in introv NM;
    let M := fresh "M" in introv M;
    repeat (inverts M as M; [ try solve [ simpl; reflexivity
                                        | false NM; repeat constructors ] |]); inverts M ].

(** The following tactics builds a term [g'] such that [globals_with g L g']. **)
Ltac build_globals_with g L :=
  let g' := fresh "g" in
  exact (proj1_sig (ltac:(solve_globals_with) : { g' | globals_with g L g' })).

Delimit Scope globals_scope with globals.

(** Hidding the tactic under a readable notation. **)
Notation "'{{!' g 'with' L '!}}'" :=
  (ltac:(build_globals_with g L)) : globals_scope.

Open Scope globals.

(** A dummy element of [Globals], in which all fields are mapped to [NULL]. **)
Definition empty_globals : Globals.
  refine (proj1_sig (P := fun g => forall C, Mem C Globals_projections -> C g = NULL) _).
  refine (let g := make_Globals in _). repeat refine (let g := g _ in _). exists g.
  introv M. repeat (inverts M as M; [simpl; reflexivity|]). inverts M.
Defined.

Lemma empty_globals_projections : forall C,
  Mem C Globals_projections ->
  C empty_globals = NULL.
Proof.
  introv M. repeat (inverts M as M; [ reflexivity |]). inverts M.
Qed.

(** Solves a goal of the form [No_duplicates L], where [L] is a list
 * of projections of [Globals]. **)
Ltac prove_no_duplicate_projections :=
  let M := fresh "M" in let E := fresh "E" in
  repeat (apply No_duplicates_cons;
    [ abstract
        (introv M; repeat (inverts M as M; [
           match type of M with ?C1 = ?C2 =>
             set (g := {{! empty_globals with [(C1, proj1_sig dummy_not_NULL)] !}});
             asserts E: (C1 g = C2 g); [ rewrite M; reflexivity | inverts E ]
           end |]);
         inverts M)
    |]); apply No_duplicates_nil.

(** No projection appears twice in [Globals_projections]. **)
Lemma No_duplicates_Globals_projections : No_duplicates Globals_projections.
Proof.
  prove_no_duplicate_projections.
Qed.


(** The notation [{{! g with L !}}] is useful. Unfortunately, it is actually a
 * tactic, and only works if the list [L] is known at extraction time. There
 * exists a place in the module Rinit in which the list [L] is computed at
 * execution time (its projections are however known before, but it would make
 * the definition less readable that way). We here propose need something else
 * to deal with such list: having a computable equivalent of [{{! g with L !}}].
 * Note that as [{{! g with L !}}] is faster at execution time, it is still
 * preferable when possible. **)

Definition Globals_with (g : Globals) (C : Globals -> SExpRec_pointer) (v : SExpRec_pointer) :
    Mem C Globals_projections ->
    { g' | globals_with g [(C, v)] g' }.
  introv M0. lets M: M0. lets ND: No_duplicates_Globals_projections.
  repeat match type of M with
    | Mem _ [?C0] =>
      let E := fresh "E" in
      asserts E: (C = C0);
      [ inverts M as M; [ reflexivity | inverts M ]
      | clear M; rewrite E; solve_globals_with ]
    | Mem _ ?l =>
      let M1 := fresh "M" in
      (forwards M1: divide_list_Mem M; [ apply surjective_pairing |]);
      let ND1 := fresh "ND" in let ND2 := fresh "ND" in
      (forwards (ND1&ND2): divide_list_No_duplicates ND; [ reflexivity |]);
      let g' := fresh "g" in
      set (g' :=
        let L := map (fun C => (C, proj1_sig dummy_not_NULL)) (fst (divide_list l)) in
        ltac:(solve_globals_with) : { g' | globals_with empty_globals L g' });
      let E := fresh "E" in
      destruct (decide (C (proj1_sig g') = NULL)) eqn: E; fold_bool; rew_refl in E;
      [ (* [true] case: we are in the second list. *)
        asserts M': (Mem C (snd (divide_list l)));
        [ inverts M1 as M1;
          [ erewrite globals_with_in with (p := proj1_sig dummy_not_NULL) in E;
            [ false~ (proj2_sig dummy_not_NULL)
            | apply (proj2_sig g')
            | apply Mem_map with (f := fun C => (C, proj1_sig dummy_not_NULL)); apply M1 ]
          | eassumption ]
        | clear ND ND1 M; rename M' into M; rename ND2 into ND ]
      | (* [false] case: we are in the first list. *)
        asserts M': (Mem C (fst (divide_list l)));
        [ inverts M1 as M1;
          [ eassumption
          | erewrite globals_with_out in E;
            [ rewrite empty_globals_projections in E; [ false~ E | apply M0 ]
            | apply (proj2_sig g')
            | let MA := fresh "M" in let M2 := fresh "M" in let E' := fresh "E" in
              introv MA; forwards (?&M2&E'): Mem_map_inv (rm MA); inverts E';
              applys divide_list_Mem_No_duplicates M ND M2 M1; reflexivity
            | apply M0 ]
        ]
        | clear ND ND2 M; rename M' into M; rename ND1 into ND ]
      ];
      clear M1 E g'; simpl in M
  end.
Defined.

Definition Globals_with_list (g : Globals) (L : list ((Globals -> SExpRec_pointer) * SExpRec_pointer)) :
    (forall C v, Mem (C, v) L -> Mem C Globals_projections) ->
    No_duplicates (map fst L) ->
    { g' | globals_with g L g' }.
  introv F ND. gen g. induction L; introv.
  - exists g. rewrite~ globals_with_empty.
  - destruct a as [C v]. asserts M: (Mem C Globals_projections).
    + apply~ F.
    + forwards IHg: IHL (proj1_sig (Globals_with g C v M)).
      * introv M'. apply~ F. apply* Mem_next.
      * inverts~ ND.
      * exists (proj1_sig IHg). apply~ globals_with_transitive_step.
        -- refine (proj2_sig (Globals_with _ _ _ M)).
        -- introv M'. rew_list in ND. inverts ND as NM ND. false NM.
           applys Mem_map M'.
        -- apply~ proj2_sig.
Defined.

(** We can now prove a notation for this function. **)
Notation "'{{' g 'with' L 'using' F ',' ND '}}'" :=
  (Globals_with_list g L F ND) : globals_scope.


