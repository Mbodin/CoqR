
open Low


let all_global_variables =
  [ (R_AsCharacterSymbol, "R_AsCharacterSymbol") ;
    (R_BaseEnv, "R_BaseEnv") ;
    (R_BaseNamespaceName, "R_BaseNamespaceName") ;
    (R_BaseNamespace, "R_BaseNamespace") ;
    (R_BaseSymbol, "R_BaseSymbol") ;
    (R_BraceSymbol, "R_BraceSymbol") ;
    (R_Bracket2Symbol, "R_Bracket2Symbol") ;
    (R_BracketSymbol, "R_BracketSymbol") ;
    (R_ClassSymbol, "R_ClassSymbol") ;
    (R_ColonSymbol, "R_ColonSymbol") ;
    (R_CommentSymbol, "R_CommentSymbol") ;
    (R_ConnIdSymbol, "R_ConnIdSymbol") ;
    (R_DevicesSymbol, "R_DevicesSymbol") ;
    (R_DeviceSymbol, "R_DeviceSymbol") ;
    (R_DimNamesSymbol, "R_DimNamesSymbol") ;
    (R_DimSymbol, "R_DimSymbol") ;
    (R_DollarSymbol, "R_DollarSymbol") ;
    (R_dot_Class, "R_dot_Class") ;
    (R_dot_defined, "R_dot_defined") ;
    (R_DotEnvSymbol, "R_DotEnvSymbol") ;
    (R_dot_GenericCallEnv, "R_dot_GenericCallEnv") ;
    (R_dot_GenericDefEnv, "R_dot_GenericDefEnv") ;
    (R_dot_Generic, "R_dot_Generic") ;
    (R_dot_Group, "R_dot_Group") ;
    (R_dot_Method, "R_dot_Method") ;
    (R_dot_Methods, "R_dot_Methods") ;
    (R_dot_packageName, "R_dot_packageName") ;
    (R_DotsSymbol, "R_DotsSymbol") ;
    (R_dot_target, "R_dot_target") ;
    (R_DoubleColonSymbol, "R_DoubleColonSymbol") ;
    (R_DropSymbol, "R_DropSymbol") ;
    (R_EmptyEnv, "R_EmptyEnv") ;
    (R_ExactSymbol, "R_ExactSymbol") ;
    (R_FalseValue, "R_FalseValue") ;
    (R_GlobalEnv, "R_GlobalEnv") ;
    (R_LastvalueSymbol, "R_LastvalueSymbol") ;
    (R_LevelsSymbol, "R_LevelsSymbol") ;
    (R_LogicalNAValue, "R_LogicalNAValue") ;
    (R_MethodsNamespace, "R_MethodsNamespace") ;
    (R_MissingArg, "R_MissingArg") ;
    (R_ModeSymbol, "R_ModeSymbol") ;
    (R_NamespaceEnvSymbol, "R_NamespaceEnvSymbol") ;
    (R_NamespaceRegistry, "R_NamespaceRegistry") ;
    (R_NamespaceSymbol, "R_NamespaceSymbol") ;
    (R_NamesSymbol, "R_NamesSymbol") ;
    (R_NameSymbol, "R_NameSymbol") ;
    (R_NaRmSymbol, "R_NaRmSymbol") ;
    (R_NilValue, "R_NilValue") ;
    (R_PackageSymbol, "R_PackageSymbol") ;
    (R_PreviousSymbol, "R_PreviousSymbol") ;
    (R_QuoteSymbol, "R_QuoteSymbol") ;
    (R_RecursiveSymbol, "R_RecursiveSymbol") ;
    (R_RowNamesSymbol, "R_RowNamesSymbol") ;
    (R_SeedsSymbol, "R_SeedsSymbol") ;
    (R_SortListSymbol, "R_SortListSymbol") ;
    (R_SourceSymbol, "R_SourceSymbol") ;
    (R_SpecSymbol, "R_SpecSymbol") ;
    (R_SrcfileSymbol, "R_SrcfileSymbol") ;
    (R_SrcrefSymbol, "R_SrcrefSymbol") ;
    (R_TmpvalSymbol, "R_TmpvalSymbol") ;
    (R_TripleColonSymbol, "R_TripleColonSymbol") ;
    (R_TrueValue, "R_TrueValue") ;
    (R_TspSymbol, "R_TspSymbol") ;
    (R_UnboundValue, "R_UnboundValue") ;
    (R_UseNamesSymbol, "R_UseNamesSymbol") ;
    (R_WholeSrcrefSymbol, "R_WholeSrcrefSymbol") ]

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

