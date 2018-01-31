(** Rinit.
  Initialises global variables. **)

Set Implicit Arguments.
Require Export Rfeatures.


(** * Initialising Functions **)

Section Globals.

Variable globals : Globals.

Let read_globals := read_globals globals.

Local Coercion read_globals : GlobalVariable >-> SExpRec_pointer.

Variable runs : runs_type.


(** ** Functions **)

(** All the functions of this section are called from [setup_Rmainloop].
  Each sets some global variables. We implement these functions by
  returning the corresponding values. **)

(** [InitConnections], from main/connections.c **)
Definition InitConnections S :=
  let stdin := newterminal "stdin" "r" in
  let stdout :=
    let c := newterminal "stdout" "w" in
    let c := Rconnection_with_print c stdout_print in
    let c := Rconnection_with_fflush c stdout_flush in
    c in
  let stderr :=
    let c := newterminal "stderr" "w" in
    let c := Rconnection_with_print c stderr_print in
    let c := Rconnection_with_fflush c stderr_flush in
    c in
  let S := update_R_Connections S [stdin ; stdout ; stderr] in
  let S := update_R_OutputCon S 1 in
  S.

(** A special part of [InitMemory] about [R_NilValue], from main/memory.c **)
Definition init_R_NilValue S :=
  let nil_obj := {|
      NonVector_SExpRec_header := make_SExpRecHeader (build_SxpInfo NilSxp false) NULL ;
      NonVector_SExpRec_data := {|
          list_carval := NULL ;
          list_cdrval := NULL ;
          list_tagval := NULL
      |}
    |} in
  let (S, R_NilValue) := alloc_SExp S nil_obj in
  let nil_obj := {|
      NonVector_SExpRec_header := make_SExpRecHeader (build_SxpInfo NilSxp false) R_NilValue ;
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
  let (S, R_TrueValue) := mkTrue globals S in
  let (S, R_FalseValue) := mkFalse globals S in
  let (S, R_LogicalNAValue) := alloc_vector_lgl globals S (ArrayList.from_list [NA_LOGICAL]) in
  result_success S (R_TrueValue, R_FalseValue, R_LogicalNAValue).

(** [InitBaseEnv], from main/envir.c **)
Definition InitBaseEnv S :=
  let%success R_EmptyEnv :=
    NewEnvironment globals runs S R_NilValue R_NilValue R_NilValue using S in
  let%success R_BaseEnv :=
    NewEnvironment globals runs S R_NilValue R_NilValue R_EmptyEnv using S in
  result_success S (R_EmptyEnv, R_BaseEnv).

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
  do%success L' := nil
  for sym_str in%list L do
    let (sym, str) := sym_str : _ * _ in
    let%success p :=
      install globals runs S str using S in
    result_success S ((sym, p) :: L') using S in
  result_success S (LibList.rev L'). (* The table has been reversed during the loop. *)

(** The beginning of [InitNames], from main/names.c **)
Definition InitNames_shorcuts S :=
  let%success R_UnboundValue := mkSymMarker globals S R_NilValue using S in
  let (S, str) := mkChar globals S "" in
  let%success R_MissingArg := mkSymMarker globals S str using S in
  let (S, str) := mkChar globals S "" in
  let%success R_RestartToken := mkSymMarker globals S str using S in
  (** Some ignored global values: [R_InBCInterpreter], [R_CurrentExpression] **)
  let (S, NA_STRING) := alloc_vector_char globals S (ArrayList.from_list (string_to_list "NA")) in
  run%success SET_CACHED S NA_STRING true using S in
  let (S, R_BlankString) := mkChar globals S "" in
  let%success R_BlankScalarString := ScalarString globals S R_BlankString using S in
  let R_SymbolTable := R_NilValue in
  let S := update_R_SymbolTable S R_SymbolTable in
  let%success L :=
     SymbolShortcuts S using S in
  result_success S (R_UnboundValue, R_MissingArg, R_RestartToken, NA_STRING, R_BlankString, R_BlankScalarString, L).

(** The initialisation of [mkPRIMSXP_PrimCache], done in C in [mkPRIMSXP],
  from main/dstruct.c called from [InitNames] from main/names.c **)
Definition mkPRIMSXP_init S :=
  let%success R_FunTab := get_R_FunTab runs S using S in
  let FunTabSize := ArrayList.length R_FunTab in
  let (S, primCache) :=
    alloc_vector_vec globals S (ArrayList.from_list (repeat (R_NilValue : SExpRec_pointer) FunTabSize)) in
  result_success S primCache.

(** The end of [InitNames], from main/names.c **)
Definition InitNames_install S :=
  let%success R_FunTab := get_R_FunTab runs S using S in
  do%success i := 0
  for c in%array R_FunTab do
    run%success installFunTab globals runs S c i using S in
    result_success S (1 + i) using S in
  do%success for c in%list Spec_name do
    let%success sym := install globals runs S c using S in
    SET_SPECIAL_SYMBOL S sym true using S in
  result_skip S.

(** Called from [InitNames], defined in main/eval.c **)
Definition R_initAssignSymbols S :=
  do%success for c in%list asym do
    let%success sym := install globals runs S c using S in
    (* TODO: Store the result into [asymSymbol]. *)
    result_skip S using S in
  (* TODO *)
  result_skip S.

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
  run%success
    defineVar globals runs S R_BaseSymbol R_BaseNamespace R_NamespaceRegistry using S in
  result_success S (R_NamespaceSymbol, R_GlobalEnv, R_MethodsNamespace, R_BaseNamespace,
                    R_BaseNamespaceName, R_NamespaceRegistry).

(** [InitOptions], from main/options.c **)
(* FIXME: Do we want to model it? *)
(*Definition InitOptions runs S :=
  result_not_implemented.*)

(** [TypeTable], from main/util.c **)
Definition TypeTable : list (string * SExpType) := [
    ("NULL", NilSxp) ;
    ("symbol", SymSxp) ;
    ("pairlist", ListSxp) ;
    ("closure", CloSxp) ;
    ("environment", EnvSxp) ;
    ("promise", PromSxp) ;
    ("language", LangSxp) ;
    ("special", SpecialSxp) ;
    ("builtin", BuiltinSxp) ;
    ("char", CharSxp) ;
    ("logical", LglSxp) ;
    ("integer", IntSxp) ;
    ("double", RealSxp) ;
    ("complex", CplxSxp) ;
    ("character", StrSxp) ;
    ("...", DotSxp) ;
    ("any", AnySxp) ;
    ("expression", ExprSxp) ;
    ("list", VecSxp) ;
    ("externalptr", ExtptrSxp) ;
    ("bytecode", BcodeSxp) ;
    ("weakref", WeakrefSxp) ;
    ("raw", RawSxp) ;
    ("S4", S4Sxp) ;
    ("numeric", RealSxp) ;
    ("name", SymSxp)
  ]%string.

(** [findTypeInTypeTable], from main/util.c **)
Fixpoint findTypeInTypeTable_loop t i (l : list (string * SExpType)) :=
  match l return int with
  | nil => (-1)%Z
  | (str, t') :: l =>
    ifb t = t' then i
    else findTypeInTypeTable_loop t (1 + i)%Z l
  end.

Definition findTypeInTypeTable t :=
  findTypeInTypeTable_loop t 0 TypeTable.

(** [InitTypeTables], from main/util.c **)
Definition InitTypeTables S :=
  do%success L := nil
  for type from 0 to MAX_NUM_SEXPTYPE - 1 do
    match nat_to_SExpType type with
    | Some type =>
      let j := findTypeInTypeTable type in
      ifb (j <> -1)%Z then
        match nth_option (Z.to_nat j) TypeTable with
        | Some (cstr, _) =>
          let (S, rchar) := mkChar globals S cstr in
          let%success rstr := ScalarString globals S rchar using S in
          map%pointer rstr with set_named_plural using S in
          let%success rsym := install globals runs S cstr using S in
          result_success S (make_Type2Table_type cstr rchar rstr rsym :: L)
        | None => result_impossible S "[InitTypeTables] Out of bound."
        end
      else result_success S (make_Type2Table_type "" NULL NULL NULL :: L)
    | None =>
      result_success S (make_Type2Table_type "" NULL NULL NULL :: L)
    end using S in
  let table := LibList.rev L in (* The table has been computed backward. *)
  result_success S (ArrayList.from_list table).

(** [InitS3DefaulTypes], from main/attrib.c **)
(* FIXME: Do we want to model it? *)
(*Definition InitS3DefaulTypes runs S :=
  result_not_implemented.*)

(** A special part of [setup_Rmainloop] about [R_Toplevel], from main/main.c **)
Definition init_R_Toplevel S :=
  let%success (R_EmptyEnv, R_BaseEnv) :=
    InitBaseEnv S using S in
  result_success S {|
      context_nextcontext := None ;
      context_cjmpbuf := 1 ;
      context_callflag := Ctxt_TopLevel ;
      context_promargs := R_NilValue ;
      context_callfun := R_NilValue ;
      context_sysparent := R_BaseEnv ;
      context_call := R_NilValue ;
      context_cloenv := R_BaseEnv ;
      context_conexit := R_NilValue ;
      context_returnValue := NULL ;
      context_jumptarget := None ;
      context_jumpmask := empty_context_type
    |}.

End Globals.


(** ** [setup_Rmainloop] **)

(** This section concludes the initialisation. **)

(** The functions above are all called in the C version of [setup_Rmainloop],
  in main/main.c.
  In C, each of these functions modify some global variables.
  In Coq, we have to build intermediate [Globals] structures,
  accounting for the various changes.
  The definition of this function is tricky, as we are using [runs], whose
  value depends on global variables. We are thus taking as argument the
  [max_step] argument from [runs], and recomputing it at each step with
  the updated [globals]. **)
Definition setup_Rmainloop max_step S : result Globals :=
  let decl x p := (x, p) : GlobalVariable * SExpRec_pointer in
  let globals := empty_Globals in
  let S := InitConnections S in
  let%success NilValue :=
    init_R_NilValue S using S in
  let globals := {{ globals with [ decl R_NilValue NilValue ] }} in
  let%success (TrueValue, FalseValue, LogicalNAValue) :=
    InitMemory globals S using S in
  let globals := {{ globals with [ decl R_TrueValue TrueValue ;
                                   decl R_FalseValue FalseValue ;
                                   decl R_LogicalNAValue LogicalNAValue ] }} in
  let%success (EmptyEnv, BaseEnv) :=
    InitBaseEnv globals (runs max_step globals) S using S in
  let globals := {{ globals with [ decl R_EmptyEnv EmptyEnv ;
                                   decl R_BaseEnv BaseEnv ] }} in
  let%success (UnboundValue, MissingArg, RestartToken, NA_string, BlankString, BlankScalarString, L) :=
    InitNames_shorcuts globals (runs max_step globals) S using S in
  let globals := {{ globals with [ decl R_UnboundValue UnboundValue ;
                                   decl R_MissingArg MissingArg ;
                                   decl R_RestartToken RestartToken ;
                                   decl NA_STRING NA_string ;
                                   decl R_BlankString BlankString ;
                                   decl R_BlankScalarString BlankScalarString ] ++ L }} in
  let%success primCache :=
    mkPRIMSXP_init globals (runs max_step globals) S using S in
  let globals := {{ globals with [ decl mkPRIMSXP_primCache primCache ] }} in
  run%success
    InitNames_install globals (runs max_step globals) S using S in
  run%success
    R_initAssignSymbols globals (runs max_step globals) S using S in
  (* TODO: [initializeDDVALSymbols], [R_initialize_bcode], [R_init_altrep]. *)
  let%success (NamespaceSymbol, GlobalEnv, MethodsNamespace, BaseNamespace,
      BaseNamespaceName, NamespaceRegistry) :=
    InitGlobalEnv globals (runs max_step globals) S using S in
  let globals := {{ globals with [ decl R_NamespaceSymbol NamespaceSymbol ;
                                   decl R_GlobalEnv GlobalEnv ;
                                   decl R_MethodsNamespace MethodsNamespace ;
                                   decl R_BaseNamespace BaseNamespace ;
                                   decl R_BaseNamespaceName BaseNamespaceName ;
                                   decl R_NamespaceRegistry NamespaceRegistry] }} in
  (* TODO: [InitOptions]. *)
  let%success Type2Table := InitTypeTables globals (runs max_step globals) S using S in
  let globals := Globals_with_Type2Table globals Type2Table in
  (* TODO: [InitS3DefaulTypes]. *)
  let%success R_Toplevel :=
    init_R_Toplevel globals (runs max_step globals) S using S in
  (* TODO: [Init_R_Variables]. *)
  let S := state_with_context S R_Toplevel in
  let S := update_R_ExitContext S None in
  let S := update_R_ReturnedValue S NULL in
  (* TODO: Some more initialisation. *)
  let globals := flatten_Globals globals in (** Removing the now useless closures. **)
  result_success S globals.


(** * Initial State and Memory **)

(** The state defined in this section is the state of the program before running
  [setup_Rmainloop]. **)

(** An empty (and dummy) context **)
Definition empty_context := {|
    context_nextcontext := None ;
    context_cjmpbuf := 0 ;
    context_callflag := Ctxt_TopLevel ;
    context_promargs := NULL ;
    context_callfun := NULL ;
    context_sysparent := NULL ;
    context_call := NULL ;
    context_cloenv := NULL ;
    context_conexit := NULL ;
    context_returnValue := NULL ;
    context_jumptarget := None ;
    context_jumpmask := empty_context_type
  |}.

(** An empty (and dummy) state **)
Definition empty_state := {|
    state_memory := empty_memory ;
    state_context := empty_context ;
    R_ExitContext := None ;
    R_SymbolTable := NULL ;
    R_ReturnedValue := NULL ;
    R_Connections := nil ;
    R_OutputCon := 0
  |}.

