(** Print
 * Contains various functions for printing values from Low. **)

open Low


(** The list of all global variables and their name to be displayed.
 * Static variables are not included on purpose.
 * The value [R_NilValue] should always be first to ease reading. **)
let all_global_variables =
  [ (R_NilValue, "R_NilValue") ;

    (NA_STRING, "NA_STRING") ;
    (R_AsCharacterSymbol, "R_AsCharacterSymbol") ;
    (R_BaseEnv, "R_BaseEnv") ;
    (R_BaseNamespaceName, "R_BaseNamespaceName") ;
    (R_BaseNamespace, "R_BaseNamespace") ;
    (R_BaseSymbol, "R_BaseSymbol") ;
    (R_BlankScalarString, "R_BlankScalarString") ;
    (R_BlankString, "R_BlankString") ;
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
    (R_WholeSrcrefSymbol, "R_WholeSrcrefSymbol") ;

    (MkPRIMSXP_primCache, "static variable primCache from mkPRIMSXP") ]

let _ =
  (** A sanity check that we forgot no name above **)
  if List.exists (fun c_Coq ->
      not (List.exists (fun (c_OCaml, _) ->
        c_Coq = c_OCaml) all_global_variables)) all_GlobalVariables then
    prerr_endline "Warning: some Coq global variables have not been associated a string in OCaml."

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

let string_to_char_list str =
  let rec aux i acc =
    if i < 0 then acc
    else aux (i - 1) (str.[i] :: acc) in
  aux (String.length str - 1) []

let is_prefix str1 str2 =
  let l1 = String.length str1 in
  let l2 = String.length str2 in
  if l1 > l2 then false
  else str1 = String.sub str2 0 l1

let split_on_char c str =
  let len = String.length str in
  let sub start end_excl =
    String.sub str start (end_excl - start) in
  let rec search start current =
    if current = len then [sub start current]
    else if str.[current] = c then
      sub start current :: search (1 + current) (1 + current)
    else search start (1 + current)
  in search 0 0


let print_raw_pointer = function
  | None -> "NULL"
  | Some i -> string_of_int i


let pointer_exceptions s g =
  List.concat [
      List.map (fun (var, str) ->
        (g var, str)) all_global_variables ;
      List.map (fun (proj, str) ->
        (proj s, str)) all_global_variables_state
    ]

let print_pointer t s g p =
    if t then
      try List.assoc p (pointer_exceptions s g)
      with Not_found ->
        print_raw_pointer p
    else print_raw_pointer p

let print_SExpType = function
  | NilSxp -> "NilSxp"
  | SymSxp -> "SymSxp"
  | ListSxp -> "ListSxp"
  | CloSxp -> "CloSxp"
  | EnvSxp -> "EnvSxp"
  | PromSxp -> "PromSxp"
  | LangSxp -> "LangSxp"
  | SpecialSxp -> "SpecialSxp"
  | BuiltinSxp -> "BuiltinSxp"
  | CharSxp -> "CharSxp"
  | LglSxp -> "LglSxp"
  | IntSxp -> "IntSxp"
  | RealSxp -> "RealSxp"
  | CplxSxp -> "CplxSxp"
  | StrSxp -> "StrSxp"
  | DotSxp -> "DotSxp"
  | AnySxp -> "AnySxp"
  | VecSxp -> "VecSxp"
  | ExprSxp -> "ExprSxp"
  | BcodeSxp -> "BcodeSxp"
  | ExtptrSxp -> "ExtptrSxp"
  | WeakrefSxp -> "WeakrefSxp"
  | RawSxp -> "RawSxp"
  | S4Sxp -> "S4Sxp"
  | NewSxp -> "NewSxp"
  | FreeSxp -> "FreeSxp"
  | FunSxp -> "FunSxp"

let print_named = function
  | Named_temporary -> "temporary"
  | Named_unique -> "unique"
  | Named_plural -> "plural"

let print_rComplex c =
  "(" ^ string_of_float c.rcomplex_r ^ ", " ^ string_of_float c.rcomplex_i ^ ")"

let print_character c =
  "'" ^ String.make 1 c ^ "'"

let print_gp gp_opt gp =
  let gp = (Obj.magic gp : nbits) in
  if not gp_opt then
    let print_bit b =
      if b then "1" else "0" in
    String.concat "" (List.map print_bit (NBits.nbits_to_list 16 gp))
  else string_of_int (NBits.nbits_to_nat 16 gp)

let is_temporary e =
  let infos = get_SxpInfo e in
  named infos = Named_temporary

let print_SExpRec d (show_gp, gp_opt, show_attrib, show_data, show_details, vector_line, charvec_string) t s g e =
  let print_basic =
    let infos = get_SxpInfo e in
    print_SExpType (type0 infos) ^ " " ^
    (if obj infos then "(obj) " else "") ^
    "(" ^ print_named (named infos) ^ ") " ^
    (if show_gp then "gp:" ^ print_gp gp_opt (gp infos) ^ " " else "") ^
    (if show_attrib then
       "attrib:" ^ print_pointer t s g (attrib (get_SExpRecHeader e)) ^ " "
     else "") in
  let print_after =
    let print_vector f v =
      let v = vector_SExpRec_vecsxp v in
      " length:" ^ string_of_int (vecSxp_length v) ^
      if show_data then
        if vector_line then
          indent d ^ String.concat " " (List.map f (vecSxp_data v))
        else
          String.concat "" (List.map (fun x -> indent d ^ f x) (vecSxp_data v))
      else "" in
    match e with
    | SExpRec_NonVector e ->
      if show_details then
        match nonVector_SExpRec_data e with
        | PrimSxp prim ->
          indent d ^ "Prim: Offset: " ^ string_of_int (prim_offset prim)
        | SymSxp0 sym ->
          indent d ^ "Sym: Name: " ^ print_pointer t s g (sym_pname sym) ^
          indent (d + 5) ^ "Value: " ^ print_pointer t s g (sym_value sym) ^
          indent (d + 5) ^ "Internal: " ^ print_pointer t s g (sym_internal sym)
        | ListSxp0 lis ->
          indent d ^ "List: Car: " ^ print_pointer t s g (list_carval lis) ^
          indent (d + 6) ^ "Cdr: " ^ print_pointer t s g (list_cdrval lis) ^
          indent (d + 6) ^ "Tag: " ^ print_pointer t s g (list_tagval lis)
        | EnvSxp0 env ->
          indent d ^ "Env: Frame: " ^ print_pointer t s g (env_frame env) ^
          indent (d + 5) ^ "Enclos: " ^ print_pointer t s g (env_enclos env)
        | CloSxp0 clo ->
          indent d ^ "Clo: Frame: " ^ print_pointer t s g (clo.clo_formals) ^
          indent (d + 5) ^ "Body: " ^ print_pointer t s g (clo.clo_body) ^
          indent (d + 5) ^ "Env: " ^ print_pointer t s g (clo.clo_env)
        | PromSxp0 prom ->
          indent d ^ "Prom: Value: " ^ print_pointer t s g (prom_value prom) ^
          indent (d + 6) ^ "Expr: " ^ print_pointer t s g (prom_expr prom) ^
          indent (d + 6) ^ "Env: " ^ print_pointer t s g (prom_env prom)
      else ""
    | SExpRec_VectorChar v ->
      "(vector char)" ^
      if charvec_string then
        let v = vector_SExpRec_vecsxp v in
        indent d ^ "\"" ^ char_list_to_string (vecSxp_data v) ^ "\""
      else
        print_vector print_character v
    | SExpRec_VectorLogical v -> "(vector logical)" ^ print_vector string_of_float v
    | SExpRec_VectorInteger v -> "(vector integer)" ^ print_vector string_of_float v
    | SExpRec_VectorComplex v -> "(vector complex)" ^ print_vector print_rComplex v
    | SExpRec_VectorReal v -> "(vector real)" ^ print_vector string_of_float v
    | SExpRec_VectorPointer  v -> "(vector pointer)" ^ print_vector (print_pointer t s g) v in
  print_basic ^ print_after

let remove_siblings l =
  let l' = List.stable_sort (fun (k1, _) (k2, _) -> compare k1 k2) l in
  let rec aux = function
    | [] -> []
    | (k1, v) :: (k2, _) :: l when k1 = k2 ->
      aux ((k1, v) :: l)
    | a :: l -> a :: aux l
  in aux l'

let heap_to_list h =
  remove_siblings (HeapList.to_list h)

let print_memory d s g t no_temporary expr_options m =
  String.concat (indent d) (List.filter (fun str -> str <> "")
    (List.map (fun (i, e) ->
      if not (is_temporary e) || not no_temporary then
        let si = print_pointer t s g (Some i) in
        si ^ ": " ^
        print_SExpRec (d + String.length si + 2) expr_options t s g e
      else "")
    (heap_to_list (state_heap_SExp m))))

let get_memory_cell s = function
  | None -> None
  | Some p ->
    HeapList.read_option nat_comparable (state_heap_SExp (state_memory s)) p

let print_pointed_value d expr_options t s g p =
  match get_memory_cell s p with
  | None -> "(Invalid pointer)"
  | Some e -> print_SExpRec d expr_options t s g e

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

let print_state d (context, memory, globals, initials, no_temporary, fetch_global, t) expr_options s g =
  (if memory then
    "Memory:" ^ indent (d + 2) ^
    print_memory (d + 2) s g t no_temporary expr_options (state_memory s)
    ^ (if globals || initials || context then indent d else "")
   else "") ^
  (if globals then
    "Global variables:" ^ indent (d + 2) ^
    String.concat (indent (d + 2)) (
      List.map (fun (proj, str) ->
        str ^ ": " ^ print_pointer t s g (proj s) ^
        if fetch_global then
          indent (String.length str + d + 4) ^ "Pointer value: " ^
          print_pointed_value (String.length str + d + 19) expr_options t s g (proj s)
        else "") all_global_variables_state)
    ^ (if initials || context then indent d else "")
   else "") ^
  (if initials then
    "Constant global variables:" ^ indent (d + 2) ^
    String.concat (indent (d + 2)) (
      List.map (fun (var, str) ->
        str ^ ": " ^ print_pointer t s g (g var) ^
        if fetch_global then
          indent (String.length str + d + 4) ^ "Pointer value: " ^
          print_pointed_value (String.length str + d + 19) expr_options t s g (g var)
        else "") all_global_variables)
    ^ (if context then indent d else "")
   else "") ^
  if context then
    "Context:" ^ indent (d + 2) ^ print_context (d + 2) t s g (state_context s)
  else ""

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

let print_defined r s pr cont =
  print_continue r s (fun s -> function
    | None ->
      print_endline "An error lead to an undefined result." ;
      cont s None
    | Some r ->
      pr s r ;
      cont s (Some r))

