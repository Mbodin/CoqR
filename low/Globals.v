(** Globals.
  * Lists all global variables used in the C source code of R,
  * that are initialised, then never changed. **)


Require Export RinternalsAux.


(** Global variables that are initialised once, then treated as
  constants.  They are initialised in the file Rinit.v. **)
Record Globals := make_Globals {
    R_NilValue : SExpRec_pointer ;

    R_EmptyEnv : SExpRec_pointer ;
    R_BaseEnv : SExpRec_pointer ;
    R_GlobalEnv : SExpRec_pointer ;
    R_BaseNamespace : SExpRec_pointer ;
    R_BaseNamespaceName : SExpRec_pointer ;
    R_BaseSymbol : SExpRec_pointer ;
    R_NamespaceRegistry : SExpRec_pointer ;
    R_NamespaceSymbol : SExpRec_pointer ;
    R_MethodsNamespace : SExpRec_pointer ;

    R_TrueValue : SExpRec_pointer ;
    R_FalseValue : SExpRec_pointer ;
    R_LogicalNAValue : SExpRec_pointer ;

    R_UnboundValue : SExpRec_pointer ;
    R_MissingArg : SExpRec_pointer ;
    R_DotsSymbol : SExpRec_pointer ;
    R_QuoteSymbol : SExpRec_pointer ;

    R_ClassSymbol : SExpRec_pointer ;
    R_RowNamesSymbol : SExpRec_pointer
  }.


(** We are going to update structures of type [Globals] a lot of time
 * in Module Rinit. There is unfortunately no [{o with f := v}] syntax
 * in Coq. As we are going to need it (as it helps avoid mistakes in
 * this particular case), we implement a specialised version in Ltac. **)

(** Here follows a list of all the constructors of [Globals]. **)
Definition Globals_constructors :=
  [ R_NilValue ;
    R_EmptyEnv ;
    R_BaseEnv ;
    R_GlobalEnv ;
    R_BaseNamespace ;
    R_BaseNamespaceName ;
    R_BaseSymbol ;
    R_NamespaceRegistry ;
    R_NamespaceSymbol ;
    R_MethodsNamespace ;
    R_TrueValue ;
    R_FalseValue ;
    R_LogicalNAValue ;
    R_UnboundValue ;
    R_MissingArg ;
    R_DotsSymbol ;
    R_QuoteSymbol ;
    R_ClassSymbol ;
    R_RowNamesSymbol ].

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
      Mem C Globals_constructors ->
      C g' = C g ;
  }.

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
  refine (proj1_sig (P := fun g => forall C, Mem C Globals_constructors -> C g = NULL) _).
  refine (let g := make_Globals in _). repeat refine (let g := g _ in _). exists g.
  introv M. repeat (inverts M as M; [simpl; reflexivity|]). inverts M.
Defined.

Lemma empty_globals_constructors : forall C,
  Mem C Globals_constructors ->
  C empty_globals = NULL.
Proof.
  introv M. repeat (inverts M as M; [ reflexivity |]). inverts M.
Qed.

(** A dummy pointer different than [NULL]. **)
Definition dummy_not_NULL : { p : SExpRec_pointer | p <> NULL }.
  exists (Some arbitrary : SExpRec_pointer). discriminate.
Defined.

Lemma No_duplicates_Globals_constructors : No_duplicates Globals_constructors.
Proof.
  repeat constructors;
  abstract
    (introv M; repeat (inverts M as M; [
       match type of M with ?C1 = ?C2 =>
         set (g := {{! empty_globals with [(C1, proj1_sig dummy_not_NULL)] !}});
         asserts E: (C1 g = C2 g); [ rewrite M; reflexivity | inverts E ]
       end |]);
     inverts M).
Qed.

(** The notation [{{! g with L !}}] is useful. Unfortunately, it is actually a
 * tactic, and only works if the list [L] is known at extraction time. There
 * exists a place in the module Rinit in which the list [L] is computed at
 * execution time (its constructors are however known before, but it would make
 * the definition less readable that way). We here propose need something else
 * to deal with such list: having a computable equivalent of [{{! g with L !}}].
 * Note that as [{{! g with L !}}] is faster at execution time, it is still
 * preferable when possible. **)

Definition Globals_with (g : Globals) (C : Globals -> SExpRec_pointer) (v : SExpRec_pointer) :
    Mem C Globals_constructors ->
    { g' | globals_with g [(C, v)] g' }.
  introv M0. lets M: M0. lets ND: No_duplicates_Globals_constructors.
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
      destruct (C (proj1_sig g')) eqn: E;
      [ (* [Some] case: we are in the first list. *)
        asserts M': (Mem C (fst (divide_list l)));
        [ inverts M1 as M1;
          [ eassumption
          | erewrite globals_with_out in E;
            [ rewrite empty_globals_constructors in E; [ inverts E | apply M0 ]
            | apply (proj2_sig g')
            | let MA := fresh "M" in let M2 := fresh "M" in let E' := fresh "E" in
              introv MA; forwards (?&M2&E'): Mem_map_inv (rm MA); inverts E';
              applys divide_list_Mem_No_duplicates M ND M2 M1; reflexivity
            | apply M0 ]
        ]
        | clear ND ND2 M; rename M' into M; rename ND1 into ND ]
      | (* [None] case: we are in the second list. *)
        asserts M': (Mem C (snd (divide_list l))) ;
        [ inverts M1 as M1;
          [ erewrite globals_with_in with (p := proj1_sig dummy_not_NULL) in E;
            [ inverts E
            | apply (proj2_sig g')
            | apply Mem_map with (f := fun C => (C, proj1_sig dummy_not_NULL)); apply M1 ]
          | eassumption ]
        | clear ND ND1 M; rename M' into M; rename ND2 into ND ]
      ];
      clear M1 E g'; simpl in M
  end.
Defined.

Lemma Globals_constructors_all : forall g g',
  (forall C, Mem C Globals_constructors -> C g = C g') ->
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
  let l := eval unfold Globals_constructors in Globals_constructors in
  t l.
Qed.

Lemma globals_with_empty : forall g g',
  globals_with g nil g' <-> g = g'.
Proof.
  iff G.
  - apply Globals_constructors_all. introv M.
    symmetry. applys~ globals_with_out G. introv M'. inverts M'.
  - constructors.
    + introv M. inverts M.
    + introv F M. rewrite~ G.
Qed.

Lemma globals_with_transitive : forall g1 g2 g3 L1 L2 L1',
  globals_with g1 L1 g2 ->
  (forall C v, Mem (C, v) L1 -> Mem C Globals_constructors) ->
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
  Mem C1 Globals_constructors ->
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

Definition Globals_with_list (g : Globals) (L : list ((Globals -> SExpRec_pointer) * SExpRec_pointer)) :
    (forall C v, Mem (C, v) L -> Mem C Globals_constructors) ->
    No_duplicates (map fst L) ->
    { g' | globals_with g L g' }.
  introv F ND. gen g. induction L; introv.
  - exists g. rewrite~ globals_with_empty.
  - destruct a as [C v]. asserts M: (Mem C Globals_constructors).
    + apply~ F.
    + forwards IHg: IHL (proj1_sig (Globals_with g C v M)).
      * introv M'. apply~ F. apply* Mem_next.
      * inverts~ ND.
      * exists (proj1_sig (Globals_with (proj1_sig IHg) C v M)).
        apply~ globals_with_transitive_step.
        -- refine (proj2_sig (Globals_with _ _ _ _)). apply~ F.
        -- introv M'. rew_list in ND. inverts ND as NM ND. false NM.
           applys Mem_map M'.
        -- refine (proj2_sig (Globals_with _ _ _ _)).
Defined.

