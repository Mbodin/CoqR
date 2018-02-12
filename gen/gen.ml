
open Structures

let _ = Random.self_init ()

let debug = ref false
let full_debug = ref false
let max_step = ref (-1)
let smart = ref false
let verbose = ref false
let file = ref ""

let _ =
  Arg.parse [
      ("-debug", Arg.Set debug, "Prints how many times each state was used at each step.") ;
      ("-full-debug", Arg.Set debug, "Prints the current derivation at each step.") ;
      ("-max-step", Arg.Set_int max_step, "To prevent infinite loops, stops when reaching this number of unfoldings.") ;
      ("-verbose", Arg.Set verbose, "Explains what the program is doing.") ;
      ("-smart", Arg.Set smart, "Try to be smart.") ]
    (fun str ->
      if !file = "" then
        file := str
      else prerr_endline ("I do not know what to do with “" ^ str ^ "”."))
    "This programs generates random programs from a grammar. Usage:\n\tgen.native [OPTIONS] [GRAMMAR_FILE]"

let rules =
  if !verbose then print_endline "Opening file…" ;
  let channel =
    if !file = "" then file := "gram" ;
    if !file = "-" then stdin
    else open_in !file in
  let buf = Lexing.from_channel channel in
  if !verbose then print_endline "Parsing grammar…" ;
  Parser.main Lexer.lex buf

let start_identifier =
  if !verbose then print_endline "Looking for the initial identifier…" ;
  match rules with
  | (id, _, _) :: _ -> id
  | [] -> failwith "Empty grammar!"

let add_rule l (id, a, prod) =
  let rec findapply f = function
    | [] -> [(id, f ([], [], []))]
    | (id', prods) :: l ->
      if id = id' then
        (id, f prods) :: l
      else (id', prods) :: findapply f l in
  let addprod (often, normal, rare) =
    match a with
    | Often -> (prod :: often, normal, rare)
    | Normal -> (often, prod :: normal, rare)
    | Rare -> (often, normal, prod :: rare) in
  findapply addprod l

let convert =
  List.fold_left add_rule []

let rec remove_void_transitions (r : rule_automaton) =
  let is_void id =
    let (l1, l2, l3) =
      try List.assoc id r
      with Not_found -> failwith ("Unknown identifier: " ^ id) in
    (l1 = [] && l2 = [] && l3 = []) in
  let changed = ref false in
  let r =
    List.map (fun (id, (often, normal, rare)) ->
      let f =
        List.filter (List.for_all (function
          | Str _ -> true
          | Id id ->
            if is_void id then (
              changed := true ;
              false
            ) else true)) in
      (id, (f often, f normal, f rare))) r in
  if !changed then
    remove_void_transitions r
  else r

let symbols_from (r : rule_automaton) id =
  let prods =
    let (l1, l2, l3) =
      try List.assoc id r
      with Not_found -> failwith ("Unknown identifier: " ^ id) in
    List.concat (List.map (fun l ->
      List.concat (List.map (function
        | Str _ -> []
        | Id id -> [id]) l)) (l1 @ l2 @ l3)) in
  let rec symbols seen id =
    let seen = id :: seen in
    let newids = List.filter (fun id -> not (List.mem id seen)) prods in
    if newids = [] then seen
    else List.fold_left symbols seen newids in
  symbols [] id

let is_loop r id =
  List.mem id (symbols_from r id)

let remove_loops (r : rule_automaton) =
  let f id =
    List.filter (List.for_all (function
      | Str _ -> true
      | Id id' -> not (List.mem id (symbols_from r id')))) in
  List.map (fun (id, (often, normal, rare)) ->
    (id, (f id often, f id normal, f id rare))) r

let rules : rule_automaton =
  if !verbose then print_endline "Converting the rules into an automaton…" ;
  let r = convert rules in
  if !smart then (
    if !verbose then print_endline "Optimising the automaton…" ;
    remove_void_transitions r
  ) else r

let stats = ref []

let step rules p_often p_rare l =
  let rec merge_local = function
    | ([] | [_]) as l -> l
    | Str str1 :: Str str2 :: l -> merge_local (Str (str1 ^ str2) :: l)
    | t :: l -> t :: merge_local l in
  let rec map_first_id f = function
    | [] -> []
    | Str str :: l -> Str str :: map_first_id f l
    | Id id :: l -> f id @ l in
  let transition id =
    let rec updatestat = function
        | [] -> [(id, 1)]
        | (id', c) :: l ->
          if id = id' then (id, 1 + c) :: l
          else (id', c) :: updatestat l in
    if !debug then stats := updatestat !stats ;
    let (often, normal, rare) =
      try List.assoc id rules
      with Not_found -> failwith ("Unknown identifier: " ^ id) in
    let choose l =
      List.nth l (Random.int (List.length l)) in
    if Random.float 1.0 < p_often
       && often <> [] then choose often
    else if Random.float 1.0 < p_rare
         && (often <> [] || normal <> []) then choose (often @ normal)
    else (
        if often <> [] || normal <> [] || rare <> [] then
          choose (often @ normal @ rare)
        else (
          if !verbose || !debug then prerr_endline "Void transition found." ;
          [])) in
  merge_local (map_first_id transition l)

let print_step l =
  let print = function
    | Str str -> "\"" ^ String.escaped str ^ "\""
    | Id id -> id in
  print_endline (String.concat " " (List.map print l))

let print_stats _ =
  let print (id, c) = id ^ ": " ^ string_of_int c in
  stats := List.sort (fun (_, c1) (_, c2) -> compare c2 c1) !stats ;
  print_endline (String.concat ", " (List.map print !stats))

let generate rules p_often p_rare =
  let emergency_occured = ref false in
  let rec emergency l =
      if !verbose then print_string ("Maximum number of steps reached" ^ if !emergency_occured then " again. " else ". ") ;
    if !smart && not !emergency_occured then (
      if !verbose then print_endline "Trying to fix things…" ;
      emergency_occured := true ;
      let rules = remove_void_transitions (remove_loops rules) in
      aux rules 0 l
    ) else (
      if !verbose then print_endline "Printing result as it is right now…" ;
      let print = function
        | Str str -> str
        | Id id -> "#" ^ id ^ "\n" in
      String.concat "" (List.map print l)
    )
  and aux rules i l =
    if !max_step > 0 && i > !max_step then
      emergency l
    else
      match step rules p_often p_rare l with
      | [] -> ""
      | [Str str] -> str
      | l ->
        if !full_debug then print_step l ;
        if !debug then print_stats () ;
        aux rules (1 + i) (step rules p_often p_rare l) in
  aux rules 0 [Id start_identifier]

let _ =
  if !verbose then print_endline "Starting the generation…" ;
  print_endline (generate rules 0.3 0.7)

