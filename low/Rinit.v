(** Rinit.
 * Initialises global variables. **)

Set Implicit Arguments.
Require Export Reval.


(** * Initialising Functions **)

Section Globals.

Variable globals : Globals.

Let R_NilValue := R_NilValue globals.

Let R_EmptyEnv := R_EmptyEnv globals.
Let R_BaseEnv := R_BaseEnv globals.
Let R_GlobalEnv := R_GlobalEnv globals.
Let R_BaseNamespace := R_BaseNamespace globals.
Let R_BaseNamespaceName := R_BaseNamespaceName globals.
Let R_BaseSymbol := R_BaseSymbol globals.
Let R_NamespaceRegistry := R_NamespaceRegistry globals.
Let R_NamespaceSymbol := R_NamespaceSymbol globals.
Let R_MethodsNamespace := R_MethodsNamespace globals.

Let R_TrueValue := R_TrueValue globals.
Let R_FalseValue := R_FalseValue globals.
Let R_LogicalNAValue := R_LogicalNAValue globals.

Let R_UnboundValue := R_UnboundValue globals.
Let R_MissingArg := R_MissingArg globals.
Let R_DotsSymbol := R_DotsSymbol globals.
Let R_QuoteSymbol := R_QuoteSymbol globals.

Let R_ClassSymbol := R_ClassSymbol globals.
Let R_RowNamesSymbol := R_RowNamesSymbol globals.

Variable runs : runs_type.


(** ** Functions **)

(** All the functions of this section are called from [setup_Rmainloop].
 * Each sets some global variables. We implement these functions by
 * returning the corresponding values. **)

(** A special part of [InitMemory] about [R_NilValue], from main/memory.c **)
Definition init_R_NilValue S :=
  let nil_obj := {|
      NonVector_SExpRec_header := make_SExpRecHeader (build_SxpInfo NilSxp) NULL ;
      NonVector_SExpRec_data := {|
          list_carval := NULL ;
          list_cdrval := NULL ;
          list_tagval := NULL
      |}
    |} in
  let (S, R_NilValue) := alloc_SExp S nil_obj in
  let nil_obj := {|
      NonVector_SExpRec_header := make_SExpRecHeader (build_SxpInfo NilSxp) R_NilValue ;
      NonVector_SExpRec_data := {|
          list_carval := R_NilValue ;
          list_cdrval := R_NilValue ;
          list_tagval := R_NilValue
      |}
    |} in
  write%defined R_NilValue := nil_obj using S in
  map%pointer R_NilValue with set_named_plural using S in
  result_success S R_NilValue.

(** The second part of [InitMemory], from main/memory.c **)
Definition InitMemory S :=
  let%success R_NilValue :=
    init_R_NilValue S using S in
  let (S, R_TrueValue) := mkTrue globals S in
  let (S, R_FalseValue) := mkFalse globals S in
  let (S, R_LogicalNAValue) := alloc_vector_lgl globals S [NA_LOGICAL] in
  result_success S (R_NilValue, R_TrueValue, R_FalseValue, R_LogicalNAValue).

(** [InitBaseEnv], from main/envir.c **)
Definition InitBaseEnv S :=
  let%success R_EmptyEnv :=
    NewEnvironment globals runs S R_NilValue R_NilValue R_NilValue using S in
  let%success R_BaseEnv :=
    NewEnvironment globals runs S R_NilValue R_NilValue R_EmptyEnv using S in
  result_success S (R_EmptyEnv, R_BaseEnv).


(* TODO: Explain in the repport that in R, to speed up calculus, symbols are
 * represented by unique pointers. This means that comparison is simple: it
 * is just comparing the pointers. But this means that each pointer needs
 * to be installed using the [install] function, and that parsing must look
 * in the symbol table. *)

(** [SymbolShortcuts], from main/names.c **)
Definition SymbolShortcuts S :=
  let L := [
      (* TODO *)
      (R_DotsSymbol, "...")
      (* TODO *)
    ]%string in
  fold_left (fun sym_str st =>
    let%success L' := st using S in
    let (sym, str) := sym_str : _ * _ in
    let%success p :=
      install globals runs S str using S in
    result_success S ((sym, p) :: L')) (result_success S nil) L.

(** [InitNames], from main/names.c **)
Definition InitNames S :=
  let%success R_UnboundValue := mkSymMarker globals S R_NilValue using S in
  let (S, str) := mkChar globals S "" in
  let%success R_MissingArg := mkSymMarker globals S str using S in
  (* Some ignored global values: [R_InBCInterpreter], [R_RestartToken],
   * [R_CurrentExpression], [NA_STRING], [R_BlankString], [R_BlankScalarString]. *)
  let R_SymbolTable :=
    (** We do not model the full hash table for symbols.
      * Instead, we consider that it spans over only one
      * cell. **) (* TODO: Write about this in the report. *)
    R_NilValue in
  let S := update_R_SymbolTable S R_SymbolTable in
  let%success L :=
    SymbolShortcuts S using S in
  (* TODO *)
  result_success S (R_UnboundValue, R_MissingArg, L).

(** [InitGlobalEnv], from main/envir.c **)
Definition InitGlobalEnv S :=
  let%success R_NamespaceSymbol :=
     install globals runs S ".__NAMESPACE__." using S in
  let%success R_GlobalEnv :=
    NewEnvironment globals runs S R_NilValue R_NilValue R_BaseEnv using S in
  let R_MethodsNamespace := R_GlobalEnv in
  let%success R_BaseNamespace :=
    NewEnvironment globals runs S R_NilValue R_NilValue R_GlobalEnv using S in
  let%success BaseNamespaceEnvSym :=
    install globals runs S ".BaseNamespaceEnv" using S in
  read%sym BaseNamespaceEnvSym_, BaseNamespaceEnvSym_sym :=
    BaseNamespaceEnvSym using S in
  let BaseNamespaceEnvSym_sym := {|
      sym_pname := sym_pname BaseNamespaceEnvSym_sym ;
      sym_value := R_BaseNamespace ;
      sym_internal := sym_internal BaseNamespaceEnvSym_sym
    |} in
  let BaseNamespaceEnvSym_ := {|
      NonVector_SExpRec_header := NonVector_SExpRec_header BaseNamespaceEnvSym_ ;
      NonVector_SExpRec_data := BaseNamespaceEnvSym_sym
    |} in
  write%defined BaseNamespaceEnvSym := BaseNamespaceEnvSym_ using S in
  let%success R_BaseNamespaceName :=
    let (S, str) :=
      mkChar globals S "base" in
    ScalarString globals S str using S in
  let%success R_NamespaceRegistry :=
    NewEnvironment globals runs S R_NilValue R_NilValue R_NilValue using S in
  let%success _ :=
    defineVar globals runs S R_BaseSymbol R_BaseNamespace R_NamespaceRegistry using S in
  result_success S (R_NamespaceSymbol, R_GlobalEnv, R_MethodsNamespace, R_BaseNamespace, R_BaseNamespaceName, R_NamespaceRegistry).

(** [InitOptions], from main/options.c **)
(* FIXME: Do we want to model it? *)
(*Definition InitOptions runs S :=
  TODO.*)

(** [InitTypeTables], from main/util.c **)
(* FIXME: Do we want to model it? *)
(*Definition InitTypeTables runs S :=
  TODO.*)

(** [InitS3DefaulTypes], from main/attrib.c **)
(* FIXME: Do we want to model it? *)
(*Definition InitS3DefaulTypes runs S :=
  TODO.*)

(** A special part of [setup_Rmainloop] about [R_Toplevel], from main/main.c **)
Definition init_R_Toplevel S :=
  let%success (R_EmptyEnv, R_BaseEnv) :=
    InitBaseEnv S using S in
  result_success S {|
      nextcontext := None ;
      callflag := Ctxt_TopLevel ;
      promargs := R_NilValue ;
      callfun := R_NilValue ;
      sysparent := R_BaseEnv ;
      call := R_NilValue ;
      cloenv := R_BaseEnv ;
      conexit := R_NilValue
    |}.

End Globals.

(** ** [setup_Rmainloop] **)

(** We can now close the initialising loop. **)

(** We are going to update structures of type [Globals] a lot of time
 * in this section. There is unfortunately no [{o with f := v}] syntax
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

(** A dummy element of [Globals], in which all fields are mapped to [NULL]. **)
Definition empty_globals : Globals.
  refine (proj1_sig (P := fun g => forall C, Mem C Globals_constructors -> C g = NULL) _).
  refine (let g := make_Globals in _). repeat refine (let g := g _ in _). exists g.
  introv M. repeat (inverts M as M; [simpl; reflexivity|]). inverts M.
Defined.

Notation "'{' g 'with' L '}'" :=
  (ltac:(build_globals_with g L)).

(** The functions above are all called in the C version of [setup_Rmainloop],
  * in main/main.c.
  * In C, each of these functions modify some global variables.
  * In Coq, we have to build intermediate [Globals] structures,
  * accounting for the various changes.
  * The definition of this function is tricky, as we are using [runs], whose
  * value depends on global variables. We are thus taking as argument the
  * [max_step] argument from [runs], and recomputing it at each step with
  * the updated [globals]. **)
Definition setup_Rmainloop max_step S : result Globals :=
  let globals := empty_globals in
  let%success (NilValue, TrueValue, FalseValue, LogicalNAValue) :=
    InitMemory globals S using S in
  let globals := { globals with [(R_NilValue, NilValue) ;
                                 (R_TrueValue, TrueValue) ;
                                 (R_FalseValue, FalseValue) ;
                                 (R_LogicalNAValue, LogicalNAValue)] } in
  let%success (EmptyEnv, BaseEnv) :=
    InitBaseEnv globals (runs globals max_step) S using S in
  let globals := { globals with [(R_EmptyEnv, EmptyEnv) ;
                                 (R_BaseEnv, BaseEnv)] } in
  let%success (UnboundValue, MissingArg, L) :=
    InitNames globals (runs globals max_step) S using S in
  let globals := { globals with [(R_UnboundValue, UnboundValue) ;
                                 (R_MissingArg, MissingArg)] } in
  -- (*let globals := { globals with L } in*) (* TODO: This just does not work,
                                                 the tactic looping forever. *)
     (* Maybe if we inline [SymbolShortcuts] here? We would need to get the [unfold]
        and [simpl] rights to make it work. *)
  let%success (NamespaceSymbol, GlobalEnv, MethodsNamespace, BaseNamespace,
      BaseNamespaceName, NamespaceRegistry) :=
    InitGlobalEnv globals (runs globals max_step) S using S in
  let globals := { globals with [(R_NamespaceSymbol, NamespaceSymbol) ;
                                 (R_GlobalEnv, GlobalEnv) ;
                                 (R_MethodsNamespace, MethodsNamespace) ;
                                 (R_BaseNamespace, BaseNamespace) ;
                                 (R_BaseNamespaceName, BaseNamespaceName) ;
                                 (R_NamespaceRegistry, NamespaceRegistry)] } in
  (* TODO [InitOptions] *)
  (* TODO [InitTypeTables] *)
  (* TODO [InitS3DefaulTypes] *)
  let%success R_Toplevel :=
    init_R_Toplevel globals (runs globals max_step) S using S in
  let S := {|
      state_memory := S ;
      state_context := R_Toplevel ;
      R_SymbolTable := R_SymbolTable S
    |} in
  (* TODO: Check. *)
  result_success S globals.


(** * Initial State and Memory **)

(** An empty (and dummy) context **)
Definition empty_context := {|
     nextcontext := None ;
     callflag := Ctxt_TopLevel ;
     promargs := NULL ;
     callfun := NULL ;
     sysparent := NULL ;
     call := NULL ;
     cloenv := NULL ;
     conexit := NULL
  |}.

Definition empty_state := {|
    state_memory := empty_memory ;
    state_context := empty_context ;
    R_SymbolTable := NULL
  |}.


(* I think that it would be easy to use tactics to check that [setup_Rmainloop]
 * is indeed of the form [result_success S globals] or something like that. *)



(** * Installing Symbols **)

(* TODO: [SymbolSHortcuts] from main/names.c. We need a nice way to represent it. *)


(** * Extraction **)

(* TODO: Move to another file. *)

Extraction Language Ocaml.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

(* TODO: Clean. *)
(* As classical logic statements are now unused, they should not be extracted
   (otherwise, useless errors will be launched). *)
Extraction Inline (*epsilon epsilon_def*) classicT arbitrary indefinite_description (*Inhab_witness*) Fix isTrue.

Extraction "low.ml" setup_Rmainloop empty_state.

(** * Proofs **)

(* TODO: move to another file, like Rinvariant.v. *)

(* TODO *)

(** It would be nice to prove that the read-eval-print-loop can not
 * return a [result_impossible]. **)

(** If runs returns a result, then adding fuel does not change it. **)

(** The property we want to eventually prove is that if [eval] returns
 * a result, then the C function eval does similarly. **)

