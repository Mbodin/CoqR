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


let generic_print print loc () str =
  let str = char_list_to_string str in
  let str =
    if !log then
      "Printed message (" ^ loc ^ "): " ^ str
    else str in
  print str ;
  Some ()

let stdout_print = generic_print print_string "stdout"
let stderr_print = generic_print prerr_string "stderr"

let generic_flush channel loc () =
  if !log then output_string channel ("Flush (" ^ loc ^ ")") ;
  flush channel ;
  Some ()

let stdout_flush = generic_flush stdout "stdout"
let stderr_flush = generic_flush stderr "stderr"

