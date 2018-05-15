(** Print
  Contains various functions for printing values from Extract. **)

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

open Extract

(* This looks like a bug: this function should have been extracted. *)
let make_Rcomplex r i = { rcomplex_r = r; rcomplex_i = i }


(** The list of all global variables and their name to be displayed.
  Static variables are not included on purpose.
  The value [R_NilValue] should always be first to ease reading. **)
let all_global_variables =
  [ (R_NilValue, "R_NilValue") ;

    (NA_STRING, "NA_STRING") ;
    (R_AsCharacterSymbol, "R_AsCharacterSymbol") ;
    (R_AssignSym, "R_AssignSym") ;
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
    (R_DollarGetsSymbol, "R_DollarGetsSymbol") ;
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
    (R_ReplaceFunsTable, "R_ReplaceFunsTable") ;
    (R_RestartToken,  "R_RestartToken") ;
    (R_RowNamesSymbol, "R_RowNamesSymbol") ;
    (R_SeedsSymbol, "R_SeedsSymbol") ;
    (R_SortListSymbol, "R_SortListSymbol") ;
    (R_SourceSymbol, "R_SourceSymbol") ;
    (R_SpecSymbol, "R_SpecSymbol") ;
    (R_SrcfileSymbol, "R_SrcfileSymbol") ;
    (R_SrcrefSymbol, "R_SrcrefSymbol") ;
    (R_SubassignSym, "R_SubassignSym") ;
    (R_Subassign2Sym, "R_Subassign2Sym") ;
    (R_SubsetSym, "R_SubsetSym") ;
    (R_Subset2Sym, "R_Subset2Sym") ;
    (R_TmpvalSymbol, "R_TmpvalSymbol") ;
    (R_TripleColonSymbol, "R_TripleColonSymbol") ;
    (R_TrueValue, "R_TrueValue") ;
    (R_TspSymbol, "R_TspSymbol") ;
    (R_UnboundValue, "R_UnboundValue") ;
    (R_UseNamesSymbol, "R_UseNamesSymbol") ;
    (R_valueSym, "R_valueSym") ;
    (R_WholeSrcrefSymbol, "R_WholeSrcrefSymbol") ;

    (MkPRIMSXP_primCache, "static variable primCache from mkPRIMSXP") ;
    (Do_attr_do_attr_formals, "static variable do_attr_formals from do_attr") ;
    (Do_attrgets_do_attrgets_formals, "static variable do_attrgets_formals from do_attrgets") ;
    (Do_substitute_do_substitute_formals, "static variable do_substitute_formals from do_substitute") ]

let _ =
  (** A sanity check that we forgot no name above **)
  if List.exists (fun c_Coq ->
      not (List.exists (fun (c_OCaml, _) ->
        c_Coq = c_OCaml) all_global_variables)) all_GlobalVariables then
    prerr_endline "Warning: some Coq global variables have not been associated a string in OCaml."

let all_global_variables_state =
  [ (r_SymbolTable, "R_SymbolTable") ]

let print_context_type (b1, (b2, (b3, (b4, (b5, (b6, (b7, ()))))))) =
  let l =
    let switch b str = if b then [str] else [] in
    List.concat (
        switch b1 "Ctxt_Next"
        :: switch b2 "Ctxt_Break"
        :: switch (b1 && b2) "Ctxt_Loop"
        :: switch b3 "Ctxt_Function"
        :: switch b4 "Ctxt_CCode"
        :: switch b5 "Ctxt_Browser"
        :: switch (b3 && b4) "Ctxt_Return"
        :: switch (b3 && b5) "Ctxt_Generic"
        :: switch b6 "Ctxt_Restart"
        :: switch b7 "Ctxt_Builtin"
        :: []
      ) in
  if l = [] then "Ctxt_TopLevel"
  else String.concat " | " l


let indent_no_break d =
  String.make d ' '

let indent d =
  "\n" ^ indent_no_break d


let char_list_to_string = Hooks.char_list_to_string

let string_to_char_list = Hooks.string_to_char_list

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


let print_unit () = "tt"
let print_bool b = if b then "true" else "false"
let print_str str =
  (* Warning: this produces OCaml escapes and not R escapes, which are slightly different
   * (OCaml uses decimal escapes and R octal and hexadecimal, typically). *)
  "\"" ^ String.escaped str ^ "\""


let print_raw_pointer = function
  | None -> "<NULL>"
  | Some i -> string_of_int i


let pointer_exceptions s g =
  List.concat [
      List.map (fun (var, str) ->
        (read_globals g var, str)) all_global_variables ;
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

let print_float x =
  match classify_float x with
  | FP_nan ->
    if r_IsNA x then "NA" else "NaN"
  | FP_infinite ->
    if compare x infinity = 0 then "Inf"
    else if compare x neg_infinity = 0 then "-Inf"
    else assert false
  | _ -> Printf.sprintf "%g" x

let print_rComplex c =
  if r_IsNA (rcomplex_r c) || r_IsNA (rcomplex_i c) then "NA"
  else
    let c =
      let f x = if x = -0. then 0. else x in
      make_Rcomplex (f (rcomplex_r c)) (f (rcomplex_i c)) in
    print_float (rcomplex_r c)
    ^ (if rcomplex_i c < 0. then "" else "+")
    ^ print_float (rcomplex_i c) ^ "i"

let print_character c =
  "'" ^ String.make 1 c ^ "'"

let print_logical i =
  if i = nA_LOGICAL then "NA"
  else if i = 0 then "FALSE"
  else "TRUE"

let print_integer i =
  if i = nA_INTEGER then "NA"
  else string_of_int i


let print_gp gp_opt gp =
  let gp = (Obj.magic gp : nbits) in
  if not gp_opt then
    let print_bit b =
      if b then "1" else "0" in
    String.concat "" (List.map print_bit (nbits_to_list 16 gp))
  else string_of_int (nbits_to_nat 16 gp)

let is_temporary e =
  let infos = get_SxpInfo e in
  named infos = Named_temporary

let print_SExpRec_debug d (show_gp, gp_opt, show_attrib, show_data, show_details, vector_line, charvec_string) t s g e =
  let infos = get_SxpInfo e in
  let print_basic =
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
          indent d ^ String.concat " " (List.map f (ArrayList.to_list (vecSxp_data v)))
        else
          String.concat "" (List.map (fun x -> indent d ^ f x) (ArrayList.to_list (vecSxp_data v)))
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
          indent d ^ "Clo: Formals: " ^ print_pointer t s g (clo.clo_formals) ^
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
        indent d ^ "\"" ^ char_list_to_string (ArrayList.to_list (vecSxp_data v)) ^ "\""
      else
        print_vector print_character v
    | SExpRec_VectorInteger v ->
      if type0 infos = IntSxp then
        "(vector integer)" ^ print_vector print_integer v
      else if type0 infos = LglSxp then
        "(vector logical)" ^ print_vector print_logical v
      else
        "(vector integer whose type is decorelated from its vector: " ^ print_SExpType (type0 infos) ^ ")"
        ^ print_vector print_integer v
    | SExpRec_VectorComplex v -> "(vector complex)" ^ print_vector print_rComplex v
    | SExpRec_VectorReal v -> "(vector real)" ^ print_vector print_float v
    | SExpRec_VectorPointer v -> "(vector pointer)" ^ print_vector (print_pointer t s g) v in
  print_basic ^ print_after

let get_memory_cell s = function
  | None -> None
  | Some p ->
    HeapList.read_option nat_comparable (state_heap_SExp (state_memory s)) p

let rec iterate_on_list failure f f_end s g p =
  let nil = read_globals g R_NilValue in
  if p = nil then
    f_end
  else
    match get_memory_cell s p with
    | None -> failure "[iterate_on_list] Invalid pointer found along the given list."
    | Some e ->
      match e with
      | SExpRec_NonVector e ->
        (match nonVector_SExpRec_data e with
        | ListSxp0 l ->
          f (list_carval l) (list_tagval l) (iterate_on_list failure f f_end s g (list_cdrval l))
        | _ -> failure "[iterate_on_list] Non-vector element found instead of a list."
        )
      | _ -> failure "[iterate_on_list] Vector element found instead of a list."

let rec print_SExpRec_like_R_aux prefix_list attrib_prefix_list d s g p e =
  let fetch_print_SExpRec_like_R ?(prefix_list = prefix_list) ?(attrib_prefix_list = attrib_prefix_list) p =
    match get_memory_cell s p with
    | None -> "(Invalid pointer)"
    | Some e -> print_SExpRec_like_R_aux prefix_list attrib_prefix_list d s g p e in
  let print_vector t f v =
    let v = ArrayList.to_list (vecSxp_data (vector_SExpRec_vecsxp v)) in
    if v = [] then
      t ^ "(0)"
    else
      let l = List.map f v in
      let n = List.fold_left max 0 (List.map (String.length) l) in
      String.concat " " (
        "[1]"
        :: List.map (fun str -> str ^ String.make (n - String.length str) ' ') l) in
  let print_vectorlist t f v =
    let v = ArrayList.to_list (vecSxp_data (vector_SExpRec_vecsxp v)) in
    if v = [] then
      t ^ "()"
    else
      let (_, l) =
        List.fold_left (fun (i, l) v ->
          let prefix = prefix_list ^ "[[" ^ string_of_int i ^ "]]" in
          let suffix = "" in
          (1 + i, suffix :: f prefix v :: prefix :: l)) (1, []) v in
      let l = List.rev l in
      String.concat "\n" l in
  let typeof = function
    | NilSxp -> "NULL"
    | SymSxp -> "symbol"
    | ListSxp -> "pairlist"
    | CloSxp -> "closure"
    | EnvSxp -> "environment"
    | PromSxp -> "promise"
    | LangSxp -> "lang"
    | SpecialSxp -> "special"
    | BuiltinSxp -> "builtin"
    | CharSxp -> "character"
    | LglSxp -> "logical"
    | IntSxp -> "integer"
    | RealSxp -> "numeric"
    | CplxSxp -> "complex"
    | StrSxp -> "string"
    | DotSxp -> "..."
    | AnySxp -> "any"
    | VecSxp -> "list"
    | ExprSxp -> "expression"
    | BcodeSxp -> "bytecode"
    | ExtptrSxp -> "external"
    | WeakrefSxp -> "weak reference"
    | RawSxp -> "raw"
    | S4Sxp -> "S4 object"
    | NewSxp -> "newly allocated object"
    | FreeSxp -> "free object"
    | FunSxp -> "function" in
  let print_nonvector ty = function
    | PrimSxp p -> (false, string_of_int (prim_offset p))
    | SymSxp0 s -> (true, fetch_print_SExpRec_like_R (sym_pname s))
    | ListSxp0 l ->
      (match ty with
       | NilSxp -> (true, "NULL")
       | _ ->
         (false, iterate_on_list
           (fun str -> "{ Error: " ^ str ^ " }")
           (fun c t str ->
             (if t = read_globals g R_NilValue then ""
              else ("(" ^ fetch_print_SExpRec_like_R t ^ ": "))
             ^ fetch_print_SExpRec_like_R c
             ^ (if t = read_globals g R_NilValue then "" else ")")
             ^ (if str = "" then "" else ", " ^ str)) "" s g p))
    | EnvSxp0 e -> (false, "")
    | CloSxp0 c -> (false, "")
    | PromSxp0 p -> (false, "value: " ^ fetch_print_SExpRec_like_R (prom_value p)) in
  let base =
    let ty = type0 (get_SxpInfo e) in
    let t = typeof ty in
    match e with
    | SExpRec_NonVector e ->
      let (ok, str) = print_nonvector ty (nonVector_SExpRec_data e) in
      if ok then str
      else "(" ^ t ^ (if str = "" then "" else ": " ^ str) ^ ")"
    | SExpRec_VectorChar v ->
      if p = read_globals g NA_STRING then "NA"
      else
        let v = vector_SExpRec_vecsxp v in
        print_str (char_list_to_string (ArrayList.to_list (vecSxp_data v)))
    | SExpRec_VectorInteger v ->
      if ty = IntSxp then
        print_vector "integer" print_integer v
      else if ty = LglSxp then
        print_vector "logical" print_logical v
      else
        print_vector ("decorelated integer: " ^ print_SExpType ty) print_logical v
    | SExpRec_VectorComplex v ->
      print_vector "complex" print_rComplex v
    | SExpRec_VectorReal v ->
      print_vector "numeric" print_float v
    | SExpRec_VectorPointer v ->
      if ty = VecSxp || ty = ExprSxp then
        print_vectorlist t (fun p -> fetch_print_SExpRec_like_R ~prefix_list:p ~attrib_prefix_list:"") v
      else print_vector t fetch_print_SExpRec_like_R v in
  let attrs =
    iterate_on_list (fun msg ->
        prerr_endline ("[print_SExpRec_like_R] Error when trying to display attributes: " ^ msg) ;
        indent d ^ "(Error while printing attributes)")
      (fun v t n ->
        let p = attrib_prefix_list ^ "attr(," ^ fetch_print_SExpRec_like_R t ^ ")" in
        indent d ^ p ^ indent d ^ fetch_print_SExpRec_like_R v ~attrib_prefix_list:p ^ n)
      "" s g (attrib (get_SExpRecHeader e)) in
  base ^ attrs

let print_SExpRec_like_R = print_SExpRec_like_R_aux "" ""

let print_SExpRec d (opts, print_unlike_R) t s g p e =
  if print_unlike_R then
    print_SExpRec_debug d opts t s g e
  else print_SExpRec_like_R d s g p e

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

let print_memory_cell_expr d s g expr_options t i e =
  let si = print_pointer t s g (Some i) in
  si ^ ": " ^
  print_SExpRec (d + String.length si + 2) expr_options t s g (Some i) e

let print_memory d s g t no_temporary expr_options m =
  String.concat (indent d) (List.filter (fun str -> str <> "")
    (List.map (fun (i, e) ->
      if not (is_temporary e && no_temporary) then
        print_memory_cell_expr d s g expr_options t i e
      else "")
    (heap_to_list (state_heap_SExp m))))

let print_pointed_value d expr_options t s g p =
  match get_memory_cell s p with
  | None -> "(Invalid pointer)"
  | Some e -> print_SExpRec d expr_options t s g p e

let rec print_list d expr_options t s g p =
  if p = read_globals g R_NilValue then ""
  else
    match get_memory_cell s p with
    | None -> "(Invalid pointer)"
    | Some e ->
      match e with
      | SExpRec_NonVector e_ ->
        (match nonVector_SExpRec_data e_ with
        | ListSxp0 l ->
          "{" ^ (if list_tagval l = read_globals g R_NilValue then ""
                 else print_pointed_value d expr_options t s g (list_tagval l)) ^ ": "
          ^ print_pointed_value (d + 2) expr_options t s g (list_carval l) ^ "} "
          ^ print_list d expr_options t s g (list_cdrval l)
        | _ -> "(not a list: " ^ print_SExpRec d expr_options t s g p e ^ ")")
      | _ ->
        "(not a list: " ^ print_SExpRec d expr_options t s g p e ^ ")"

let rec print_context d ce t s g ctxt =
  let expert str =
    if ce then str else "" in
  "next context:" ^
    (match ctxt.context_nextcontext with
     | None -> " None"
     | Some c -> indent (d + 2) ^ print_context (d + 2) ce t s g c) ^
  expert (indent d ^ "cjmp buffer: " ^ string_of_int ctxt.context_cjmpbuf) ^
  indent d ^ "call flag: " ^ print_context_type ctxt.context_callflag ^
  expert (indent d ^ "prom args: " ^ print_pointer t s g ctxt.context_promargs) ^
  expert (indent d ^ "call fun: " ^ print_pointer t s g ctxt.context_callfun) ^
  expert (indent d ^ "sysparent: " ^ print_pointer t s g ctxt.context_sysparent) ^
  expert (indent d ^ "call: " ^ print_pointer t s g ctxt.context_call) ^
  indent d ^ "cloenv: " ^ print_pointer t s g ctxt.context_cloenv ^
  indent d ^ "conexit: " ^ print_pointer t s g ctxt.context_conexit ^
  expert (indent d ^ "return value: " ^ print_pointer t s g ctxt.context_returnValue) ^
  expert (indent d ^ "jump target:" ^
    (match ctxt.context_nextcontext with
     | None -> " None"
     | Some c -> " cjmp buffer: " ^ string_of_int c.context_cjmpbuf (*indent (d + 2) ^ print_context (d + 2) ce t s g c*))) ^
  expert (indent d ^ "jump mask: " ^ print_context_type ctxt.context_jumpmask)

let print_state d (context, all_context, memory, globals, initials, no_temporary, fetch_global, t) expr_options s g =
  (if memory || globals || initials || context then indent_no_break d else "") ^
  (if memory then
    "Memory:" ^ indent (d + 2) ^
    print_memory (d + 2) s g t no_temporary expr_options (state_memory s)
    ^ (if globals || initials || context then indent d else "")
   else "") ^
  (if globals then
    "Global variables:" ^ indent (d + 2) ^
    String.concat (indent (d + 2)) (
      List.map (fun (proj, str) ->
        str ^ ": " ^ print_raw_pointer (proj s) ^
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
        str ^ ": " ^ print_raw_pointer (read_globals g var) ^
        if fetch_global then
          indent (String.length str + d + 4) ^ "Pointer value: " ^
          print_pointed_value (String.length str + d + 19) expr_options t s g (read_globals g var)
        else "") all_global_variables)
    ^ (if context then indent d else "")
   else "") ^
  if context then
    "Context:" ^ indent (d + 2) ^ print_context (d + 2) all_context t s g (state_context s)
  else ""

let print_stack pr_stack stack =
  if pr_stack then
    let st = String.concat ", " (List.map char_list_to_string stack) in
    " (Execution stack: " ^ st ^ ")"
  else ""

let print_result verbose pr_stack r cont =
  match r with
  | Result_success (s, g) ->
    if verbose then print_endline "Success." ;
    cont (Some s) (Some g)
  | Result_longjump (s, i, cs) ->
    print_endline ("Impossible! Please report. A long jump reached the top level (target jump buffer: " ^ string_of_int i ^ ").") ;
    cont (Some s) None
  | Result_error_stack (s, stack, str) ->
    print_endline ("Error: " ^ char_list_to_string str ^ print_stack pr_stack stack) ;
    cont (Some s) None
  | Result_impossible_stack (s, stack, str) ->
    print_endline ("Impossible! Please report. " ^ char_list_to_string str ^ print_stack pr_stack stack) ;
    cont (Some s) None
  | Result_not_implemented_stack (stack, str) ->
    let location =
      match List.rev stack with
      | [] -> ""
      | f :: _ -> "[" ^ char_list_to_string f ^ "] " in
    print_endline ("Not implemented: " ^ location ^ char_list_to_string str ^ print_stack pr_stack stack) ;
    cont None None
  | Result_bottom s ->
    print_endline "Stopped because of lack of fuel." ;
    cont None None

let print_continue verbose pr_stack r s cont =
  print_result verbose pr_stack r (function
    | None ->
      print_endline "An error lead to an undefined state. Continuing using the old one." ;
      cont s
    | Some s -> cont s)

let print_defined verbose pr_stack r s pr cont =
  print_continue verbose pr_stack r s (fun s -> function
    | None ->
      print_endline "An error lead to an undefined result." ;
      cont s None
    | Some r ->
      pr s r ;
      cont s (Some r))

let print_and_continue verbose pr_stack
    (show_state_after_computation, show_result_after_computation, run_options, ((_, print_unlike_R) as expr_options))
    g r s pr cont =
  print_defined verbose pr_stack r s (fun s r ->
    if show_state_after_computation then (
      print_endline "State:" ;
      print_endline (print_state 2 run_options expr_options s g)) ;
    if show_result_after_computation then (
      if print_unlike_R then
        print_endline ("Result: " ^ pr 8 g s r)
      else print_endline (pr 0 g s r))) cont

