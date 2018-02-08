
open Structures

let _ = Random.self_init ()

let file =
  match Array.length Sys.argv with
  | 0 | 1 -> open_in "gram"
  | 2 ->
    if Sys.argv.(1) = "-" then
      stdin
    else open_in Sys.argv.(1)
  | _ -> failwith "Too many arguments!"

let debug = false
let full_debug = false
let max_step = 1000

let rules =
  let buf = Lexing.from_channel file in
  Parser.main Lexer.lex buf

let start_identifier =
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

let rules : rule_automaton = convert rules

let stats = ref []

let step p_often p_rare l =
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
    if debug then stats := updatestat !stats ;
    let (often, normal, rare) =
      try List.assoc id rules
      with Not_found -> failwith ("Unkown identifier: " ^ id) in
    let choose l =
      List.nth l (Random.int (List.length l)) in
    if Random.float 1.0 < p_often
       && often <> [] then choose often
    else if Random.float 1.0 < p_rare
         && (often <> [] || normal <> []) then choose (often @ normal)
    else (
        assert (often <> [] || normal <> [] || rare <> []) ;
        choose (often @ normal @ rare)
      ) in
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

let generate p_often p_rare =
  let emergency l =
    let print = function
      | Str str -> str
      | Id id -> "#" ^ id ^ "\n" in
    String.concat "" (List.map print l) in
  let rec aux i l =
    if max_step > 0 && i > max_step then
      emergency l
    else
      match step p_often p_rare l with
      | [] -> ""
      | [Str str] -> str
      | l ->
        if full_debug then print_step l ;
        if debug then print_stats () ;
        aux (1 + i) (step p_often p_rare l) in
  aux 0 [Id start_identifier]

let _ =
  print_endline (generate 0.3 0.7)

