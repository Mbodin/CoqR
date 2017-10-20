(** Rinit.
 * Initialises global variables. **)

Set Implicit Arguments.
Require Export Rfeatures.


(** * Initialising Functions **)

Section Globals.

Variable globals : Globals.

Let read_globals : GlobalVariable -> SExpRec_pointer := globals.

Local Coercion read_globals : GlobalVariable >-> SExpRec_pointer.

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

(* TODO: Explain in the report that in R, to speed up calculus, symbols are
 * represented by unique pointers. This means that comparison is simple: it
 * is just comparing the pointers. But this means that each pointer needs
 * to be installed using the [install] function, and that parsing must look
 * in the symbol table. *)

(** [SymbolShortcuts], from main/names.c **)
Definition SymbolShortcuts S :=
  let decl v n := (v, n) : GlobalVariable * string in
  let L := [
      decl R_Bracket2Symbol "[[" ;
      decl R_BracketSymbol "[" ;
      decl R_BraceSymbol "{" ;
      decl R_ClassSymbol "class" ;
      decl R_DeviceSymbol ".Device" ;
      decl R_DimNamesSymbol "dimnames" ;
      decl R_DimSymbol "dim" ;
      decl R_DollarSymbol "$" ;
      decl R_DotsSymbol "..." ;
      decl R_DropSymbol "drop" ;
      decl R_LastvalueSymbol ".Last.value" ;
      decl R_LevelsSymbol "levels" ;
      decl R_ModeSymbol "mode" ;
      decl R_NameSymbol  "name" ;
      decl R_NamesSymbol "names" ;
      decl R_NaRmSymbol "na.rm" ;
      decl R_PackageSymbol "package" ;
      decl R_PreviousSymbol "previous" ;
      decl R_QuoteSymbol "quote" ;
      decl R_RowNamesSymbol "row.names" ;
      decl R_SeedsSymbol ".Random.seed" ;
      decl R_SortListSymbol "sort.list" ;
      decl R_SourceSymbol "source" ;
      decl R_TspSymbol "tsp" ;
      decl R_CommentSymbol "comment" ;
      decl R_DotEnvSymbol ".Environment" ;
      decl R_ExactSymbol "exact" ;
      decl R_RecursiveSymbol "recursive" ;
      decl R_SrcfileSymbol "srcfile" ;
      decl R_SrcrefSymbol "srcref" ;
      decl R_WholeSrcrefSymbol "wholeSrcref" ;
      decl R_TmpvalSymbol "*tmp*" ;
      decl R_UseNamesSymbol "use.names" ;
      decl R_ColonSymbol ":" ;
      decl R_DoubleColonSymbol "::" ;
      decl R_TripleColonSymbol ":::" ;
      decl R_ConnIdSymbol "conn_id" ;
      decl R_DevicesSymbol ".Devices" ;
      decl R_BaseSymbol "base" ;
      decl R_SpecSymbol "spec" ;
      decl R_NamespaceEnvSymbol ".__NAMESPACE__." ;
      decl R_AsCharacterSymbol "as.character" ;
      decl R_dot_Generic ".Generic" ;
      decl R_dot_Method ".Method" ;
      decl R_dot_Methods ".Methods" ;
      decl R_dot_defined ".defined" ;
      decl R_dot_target ".target" ;
      decl R_dot_Group ".Group" ;
      decl R_dot_Class ".Class" ;
      decl R_dot_GenericCallEnv ".GenericCallEnv" ;
      decl R_dot_GenericDefEnv ".GenericDefEnv" ;
      decl R_dot_packageName ".packageName"
    ]%string in
  fold_left (fun sym_str st =>
    let%success L' := st using S in
    let (sym, str) := sym_str : _ * _ in
    let%success p :=
      install globals runs S str using S in
    result_success S ((sym, p) :: L')) (result_success S nil) L.

(** The beginning of [InitNames], from main/names.c **)
Definition InitNames_shorcuts S :=
  let%success R_UnboundValue := mkSymMarker globals S R_NilValue using S in
  let (S, str) := mkChar globals S "" in
  let%success R_MissingArg := mkSymMarker globals S str using S in
  (* Some ignored global values: [R_InBCInterpreter], [R_RestartToken],
   * [R_CurrentExpression] *)
  (* TODO: [NA_STRING], [R_BlankString], [R_BlankScalarString]. *)
  let R_SymbolTable := R_NilValue in
  let S := update_R_SymbolTable S R_SymbolTable in
  let%success L :=
     SymbolShortcuts S using S in
  result_success S (R_UnboundValue, R_MissingArg, L).

(** The initialisation of [mkPRIMSXP_PrimCache], done in C in [mkPRIMSXP],
 * from main/dstruct.c called from [InitNames] from main/names.c **)
Definition mkPRIMSXP_init max_step S :=
  let%defined R_FunTab := R_FunTab globals runs max_step using S in
  let FunTabSize := length R_FunTab in
  let (S, primCache) :=
    alloc_vector_vec globals S (repeat (R_NilValue : SExpRec_pointer) FunTabSize) in
  result_success S primCache.

(** The end of [InitNames], from main/names.c **)
Definition InitNames_install max_step S :=
  let%defined R_FunTab := R_FunTab globals runs max_step using S in
  let%success _ :=
    fold_left (fun c r =>
        let%success i := r using S in
        let%success _ :=
          installFunTab globals runs (Some R_FunTab) S c i using S in
        result_success S (1 + i)) (result_success S 0) R_FunTab using S in
  (* TODO *)
  result_success S tt.

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

(** This section concludes the initialisation. **)

(** The functions above are all called in the C version of [setup_Rmainloop],
  * in main/main.c.
  * In C, each of these functions modify some global variables.
  * In Coq, we have to build intermediate [Globals] structures,
  * accounting for the various changes.
  * The definition of this function is tricky, as we are using [runs], whose
  * value depends on global variables. We are thus taking as argument the
  * [max_step] argument from [runs], and recomputing it at each step with
  * the updated [globals]. **)
  (* TODO: This function. *)
Definition setup_Rmainloop max_step S : result Globals :=
  let decl x p := (x, p) : GlobalVariable * SExpRec_pointer in
  let globals := empty_globals in
  let%success (NilValue, TrueValue, FalseValue, LogicalNAValue) :=
    InitMemory globals S using S in
  let globals := {{ globals with [ decl R_NilValue NilValue ;
                                   decl R_TrueValue TrueValue ;
                                   decl R_FalseValue FalseValue ;
                                   decl R_LogicalNAValue LogicalNAValue ] }} in
  let%success (EmptyEnv, BaseEnv) :=
    InitBaseEnv globals (runs globals max_step) S using S in
  let globals := {{ globals with [ decl R_EmptyEnv EmptyEnv ;
                                   decl R_BaseEnv BaseEnv ] }} in
  let%success (UnboundValue, MissingArg, L) :=
    InitNames_shorcuts globals (runs globals max_step) S using S in
  let globals := {{ globals with [ decl R_UnboundValue UnboundValue ;
                                   decl R_MissingArg MissingArg] ++ L }} in
  let%success primCache :=
    mkPRIMSXP_init globals (runs globals max_step) max_step S using S in
  let globals := {{ globals with [ decl mkPRIMSXP_primCache primCache ] }} in
  let%success _ :=
    InitNames_install globals (runs globals max_step) max_step S using S in
  let%success (NamespaceSymbol, GlobalEnv, MethodsNamespace, BaseNamespace,
      BaseNamespaceName, NamespaceRegistry) :=
    InitGlobalEnv globals (runs globals max_step) S using S in
  let globals := {{ globals with [ decl R_NamespaceSymbol NamespaceSymbol ;
                                   decl R_GlobalEnv GlobalEnv ;
                                   decl R_MethodsNamespace MethodsNamespace ;
                                   decl R_BaseNamespace BaseNamespace ;
                                   decl R_BaseNamespaceName BaseNamespaceName ;
                                   decl R_NamespaceRegistry NamespaceRegistry] }} in
  (* TODO [InitOptions] *)
  (* TODO [InitTypeTables] *)
  (* TODO [InitS3DefaulTypes] *)
  let%success R_Toplevel :=
    init_R_Toplevel globals (runs globals max_step) S using S in
  let S := {|
      state_memory := S ;
      state_context := R_Toplevel ;
      R_ExitContext := None ;
      R_SymbolTable := R_SymbolTable S
    |} in
  let globals := flatten_Globals globals in (* Removing the now useless closures. *)
  result_success S globals.


(** * Initial State and Memory **)

(** The state defined in this section is the state of the program before running
  [setup_Rmainloop]. **)

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

(** An empty (and dummy) state **)
Definition empty_state := {|
    state_memory := empty_memory ;
    state_context := empty_context ;
    R_ExitContext := None ;
    R_SymbolTable := NULL
  |}.

