
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
    let (often, normal, rare) =
      try List.assoc id rules
      with Not_found -> failwith ("Unkown identifier: " ^ id) in
    let choose l =
      List.nth l (Random.int (List.length l)) in
    if Random.float 1.0 < p_often then choose often
    else if Random.float 1.0 < p_rare then choose (often @ normal)
    else choose (often @ normal @ rare) in
  merge_local (map_first_id transition l)

let generate p_often p_rare =
  let rec aux l =
    match step p_often p_rare l with
    | [Str str] -> str
    | l -> aux (step p_often p_rare l) in
  aux [Id start_identifier]

let _ =
  print_endline (generate 0.3 0.5)

