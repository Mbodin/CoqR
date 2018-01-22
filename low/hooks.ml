(** Hooks
  Contains some impure functions used by the Coq extracted code (mainly input and output). **)

let log = ref false


let char_list_to_string str =
  String.concat "" (List.map (String.make 1) str)

let string_to_char_list str =
  let rec aux i acc =
    if i < 0 then acc
    else aux (i - 1) (str.[i] :: acc) in
  aux (String.length str - 1) []


let generic_print print loc st str =
  let str = char_list_to_string str in
  let str =
    if !log then
      "Printed message (" ^ loc ^ "): " ^ str
    else str in
  print str ;
  Some st

let stdout_print st str = generic_print print_string "stdout" st str
let stderr_print st str = generic_print prerr_string "stderr" st str

let generic_flush channel loc st =
  if !log then output_string channel ("Flush (" ^ loc ^ ")") ;
  flush channel ;
  Some st

let stdout_flush st = generic_flush stdout "stdout" st
let stderr_flush st = generic_flush stderr "stderr" st

