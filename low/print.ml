
open Low


let all_global_variables =
  [ (GlobalVariable1 R_AsCharacterSymbol, "R_AsCharacterSymbol") ;
    (GlobalVariable1 R_BaseEnv, "R_BaseEnv") ;
    (GlobalVariable1 R_BaseNamespaceName, "R_BaseNamespaceName") ;
    (GlobalVariable1 R_BaseNamespace, "R_BaseNamespace") ;
    (GlobalVariable1 R_BaseSymbol, "R_BaseSymbol") ;
    (GlobalVariable1 R_BraceSymbol, "R_BraceSymbol") ;
    (GlobalVariable1 R_Bracket2Symbol, "R_Bracket2Symbol") ;
    (GlobalVariable1 R_BracketSymbol, "R_BracketSymbol") ;
    (GlobalVariable1 R_ClassSymbol, "R_ClassSymbol") ;
    (GlobalVariable1 R_ColonSymbol, "R_ColonSymbol") ;
    (GlobalVariable1 R_CommentSymbol, "R_CommentSymbol") ;
    (GlobalVariable1 R_ConnIdSymbol, "R_ConnIdSymbol") ;
    (GlobalVariable1 R_DevicesSymbol, "R_DevicesSymbol") ;
    (GlobalVariable1 R_DeviceSymbol, "R_DeviceSymbol") ;
    (GlobalVariable1 R_DimNamesSymbol, "R_DimNamesSymbol") ;
    (GlobalVariable1 R_DimSymbol, "R_DimSymbol") ;
    (GlobalVariable1 R_DollarSymbol, "R_DollarSymbol") ;
    (GlobalVariable1 R_dot_Class, "R_dot_Class") ;
    (GlobalVariable1 R_dot_defined, "R_dot_defined") ;
    (GlobalVariable1 R_DotEnvSymbol, "R_DotEnvSymbol") ;
    (GlobalVariable1 R_dot_GenericCallEnv, "R_dot_GenericCallEnv") ;
    (GlobalVariable1 R_dot_GenericDefEnv, "R_dot_GenericDefEnv") ;
    (GlobalVariable1 R_dot_Generic, "R_dot_Generic") ;
    (GlobalVariable1 R_dot_Group, "R_dot_Group") ;
    (GlobalVariable1 R_dot_Method, "R_dot_Method") ;
    (GlobalVariable1 R_dot_Methods, "R_dot_Methods") ;
    (GlobalVariable2 R_dot_packageName, "R_dot_packageName") ;
    (GlobalVariable2 R_DotsSymbol, "R_DotsSymbol") ;
    (GlobalVariable2 R_dot_target, "R_dot_target") ;
    (GlobalVariable2 R_DoubleColonSymbol, "R_DoubleColonSymbol") ;
    (GlobalVariable2 R_DropSymbol, "R_DropSymbol") ;
    (GlobalVariable2 R_EmptyEnv, "R_EmptyEnv") ;
    (GlobalVariable2 R_ExactSymbol, "R_ExactSymbol") ;
    (GlobalVariable2 R_FalseValue, "R_FalseValue") ;
    (GlobalVariable2 R_GlobalEnv, "R_GlobalEnv") ;
    (GlobalVariable2 R_LastvalueSymbol, "R_LastvalueSymbol") ;
    (GlobalVariable2 R_LevelsSymbol, "R_LevelsSymbol") ;
    (GlobalVariable2 R_LogicalNAValue, "R_LogicalNAValue") ;
    (GlobalVariable2 R_MethodsNamespace, "R_MethodsNamespace") ;
    (GlobalVariable2 R_MissingArg, "R_MissingArg") ;
    (GlobalVariable2 R_ModeSymbol, "R_ModeSymbol") ;
    (GlobalVariable2 R_NamespaceEnvSymbol, "R_NamespaceEnvSymbol") ;
    (GlobalVariable2 R_NamespaceRegistry, "R_NamespaceRegistry") ;
    (GlobalVariable2 R_NamespaceSymbol, "R_NamespaceSymbol") ;
    (GlobalVariable2 R_NamesSymbol, "R_NamesSymbol") ;
    (GlobalVariable2 R_NameSymbol, "R_NameSymbol") ;
    (GlobalVariable2 R_NaRmSymbol, "R_NaRmSymbol") ;
    (GlobalVariable2 R_NilValue, "R_NilValue") ;
    (GlobalVariable2 R_PackageSymbol, "R_PackageSymbol") ;
    (GlobalVariable2 R_PreviousSymbol, "R_PreviousSymbol") ;
    (GlobalVariable2 R_QuoteSymbol, "R_QuoteSymbol") ;
    (GlobalVariable2 R_RecursiveSymbol, "R_RecursiveSymbol") ;
    (GlobalVariable3 R_RowNamesSymbol, "R_RowNamesSymbol") ;
    (GlobalVariable3 R_SeedsSymbol, "R_SeedsSymbol") ;
    (GlobalVariable3 R_SortListSymbol, "R_SortListSymbol") ;
    (GlobalVariable3 R_SourceSymbol, "R_SourceSymbol") ;
    (GlobalVariable3 R_SpecSymbol, "R_SpecSymbol") ;
    (GlobalVariable3 R_SrcfileSymbol, "R_SrcfileSymbol") ;
    (GlobalVariable3 R_SrcrefSymbol, "R_SrcrefSymbol") ;
    (GlobalVariable3 R_TmpvalSymbol, "R_TmpvalSymbol") ;
    (GlobalVariable3 R_TripleColonSymbol, "R_TripleColonSymbol") ;
    (GlobalVariable3 R_TrueValue, "R_TrueValue") ;
    (GlobalVariable3 R_TspSymbol, "R_TspSymbol") ;
    (GlobalVariable3 R_UnboundValue, "R_UnboundValue") ;
    (GlobalVariable3 R_UseNamesSymbol, "R_UseNamesSymbol") ;
    (GlobalVariable3 R_WholeSrcrefSymbol, "R_WholeSrcrefSymbol") ]

let all_global_variables_state =
  [ (r_SymbolTable, "R_SymbolTable") ]

let print_context_type = function
  | Ctxt_TopLevel -> "Ctxt_TopLevel"
  | Ctxt_Next -> "Ctxt_Next"
  | Ctxt_Break -> "Ctxt_Break"
  | Ctxt_Loop -> "Ctxt_Loop"
  | Ctxt_Function -> "Ctxt_Function"
  | Ctxt_CCode -> "Ctxt_CCode"
  | Ctxt_Return -> "Ctxt_Return"
  | Ctxt_Browser -> "Ctxt_Browser"
  | Ctxt_Generic -> "Ctxt_Generic"
  | Ctxt_Restart -> "Ctxt_Restart"
  | Ctxt_Builtin -> "Ctxt_Builtin"


let indent_no_break d =
  String.make d ' '

let indent d =
  "\n" ^ indent_no_break d


let char_list_to_string str =
  String.concat "" (List.map (String.make 1) str)

let print_raw_pointer = function
  | None -> "NULL"
  | Some i -> string_of_int i


let pointer_exceptions s g =
  List.concat [
      List.map (fun (proj, str) ->
        (proj s, str)) all_global_variables_state ;
      List.map (fun (var, str) ->
        (g var, str)) all_global_variables
    ]

let print_pointer t s g p =
    if t then
      try List.assoc p (pointer_exceptions s g)
      with Not_found ->
        print_raw_pointer p
    else print_raw_pointer p

let print_memory d s g m =
  "TODO memory"

let rec print_context d t s g ctxt =
  "next context:" ^
  (match ctxt.nextcontext with
   | None -> " None"
   | Some c -> indent (d + 2) ^ print_context (d + 2) t s g c) ^
  indent d ^ "call flag: " ^ print_context_type ctxt.callflag ^
  indent d ^ "prom args: " ^ print_pointer t s g ctxt.promargs ^
  indent d ^ "call fun: " ^ print_pointer t s g ctxt.callfun ^
  indent d ^ "sysparent: " ^ print_pointer t s g ctxt.sysparent ^
  indent d ^ "call: " ^ print_pointer t s g ctxt.call ^
  indent d ^ "cloenv: " ^ print_pointer t s g ctxt.cloenv ^
  indent d ^ "conexit: " ^ print_pointer t s g ctxt.conexit

let print_state d everything t s g =
  "Memory:" ^ indent (d + 2) ^ print_memory (d + 2) s g (state_memory s) ^
  (if everything then
    "\nGlobals:\n" ^
    String.concat "\n" (
      List.concat [
          List.map (fun (proj, str) ->
            indent_no_break (d + 2) ^ str ^ ": " ^ print_pointer t s g (proj s)) all_global_variables_state ;
          List.map (fun (var, str) ->
            indent_no_break (d + 2) ^ str ^ ": " ^ print_pointer t s g (g var)) all_global_variables
        ])
   else "") ^
  "\nContext:" ^ indent (d + 2) ^ print_context (d + 2) t s g (state_context s)

let print_result r cont =
  match r with
  | Result_success (s, g) ->
    print_endline "Success." ;
    cont (Some s) (Some g)
  | Result_error (s, str) ->
    print_endline ("Error: " ^ char_list_to_string str) ;
    cont (Some s) None
  | Result_impossible (s, str) ->
    print_endline ("Impossible! Please report. " ^ char_list_to_string str) ;
    cont (Some s) None
  | Result_not_implemented str ->
    print_endline ("Not implemented: " ^ char_list_to_string str) ;
    cont None None
  | Result_bottom s ->
    print_endline "Stopped because of lack of fuel." ;
    cont None None

let print_continue r s cont =
  print_result r (function
    | None ->
      print_endline "An error lead to an undefined state. Continuing using the old one." ;
      cont s
    | Some s -> cont s)

let print_defined r s cont =
  print_continue r s (fun s -> function
    | None ->
      print_endline "An error lead to an undefined result. Halting"
    | Some g -> cont s g)

