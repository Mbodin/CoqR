(** Debug
  Contains debuging functions. **)

open Print
open Low
open DebugType
open Funlist


let swap (a, b) = (b, a)


let read_unit_opt = function
  | "tt" | "()" -> Some ()
  | _ -> None

let read_bool_opt = function
  | "true" -> Some true
  | "false" -> Some false
  | _ -> None

let read_int_opt str =
  try Some (int_of_string str)
  with Failure _ -> None

let read_float_opt str =
  try Some (float_of_string str)
  with Failure _ -> None

let read_pointer_opt s g str =
  let l = ("NULL", None) :: List.map swap (pointer_exceptions s g) in
  try Some (List.assoc str l)
  with Not_found ->
    try Some (Some (int_of_string str))
    with Failure _ -> None

let read_pointer s g str =
  match read_pointer_opt s g str with
  | Some p -> p
  | None ->
    prerr_endline ("Impossible to parse “" ^ str ^ "” as a pointer. Assuming R_NilValue.") ;
    g R_NilValue


let rec print_type = function
  | Result_unit _ -> "unit"
  | Result_bool _ -> "bool"
  | Result_int _ -> "int"
  | Result_float _ -> "float"
  | Result_string _ -> "string"
  | Result_pointer _ -> "SEXP"
  | Argument_unit f -> "unit -> " ^ print_type (f ())
  | Argument_bool f -> "bool -> " ^ print_type (f false)
  | Argument_int f -> "int -> " ^ print_type (f 0)
  | Argument_float f -> "float -> " ^ print_type (f 0.)
  | Argument_pointer f -> "SEXP -> " ^ print_type (f None)

let print_fun (name, t) =
  name ^ " : " ^ print_type t

let list_all_fun d =
  indent_no_break d ^ String.concat (indent d) (List.map print_fun funlist)

let print_exec_pointer = print_pointer
let print_exec_unit _ _ _ () = "tt"
let print_exec_bool _ _ _ b = if b then "true" else "false"
let print_exec_int _ _ _ = string_of_int
let print_exec_float _ _ _ = string_of_float
let print_exec_string _ _ _ str = "\"" ^ str "\""

let rec parse_args s g : ((_ -> _ -> _ -> 'a result) -> (_ -> _ -> _ -> 'a -> string) -> 'b) -> string list -> funtype -> 'b
  = fun cont l -> function
  | Result_unit f -> cont f print_exec_unit
  | Result_bool f -> cont f print_exec_bool
  | Result_int f -> cont f print_exec_int
  | Result_float f -> cont f print_exec_float
  | Result_string f -> cont f print_exec_string
  | Result_pointer f -> cont f print_exec_pointer
  | Argument_unit f -> parse_one_arg s g cont f read_unit_opt print_exec_unit () l
  | Argument_bool f -> parse_one_arg s g cont f read_bool_opt print_exec_bool false l
  | Argument_int f -> parse_one_arg s g cont f read_int_opt print_exec_int 0 l
  | Argument_float f -> parse_one_arg s g cont f read_float_opt print_exec_float 0. l
  | Argument_pointer f -> parse_one_arg s g cont f read_pointer_opt print_exec_pointer (g R_NilValue) l

and parse_one_arg s g
  : ((_ -> _ -> _ -> 'a result) -> (_ -> _ -> _ -> 'a -> string) -> 'b) -> ('c -> funlist) -> (string -> 'c option) -> ('c -> string) -> 'c -> list string -> 'b
  = fun cont f read print def -> function
    | [] -> exit 0


let parse_arg_fun s g cont cont_failure = function
  | [] ->
    prerr_endline "A function name is expected as the argument of this command." ;
    cont_failure ()
  | f :: l ->
    try
      let f = List.assoc f funlist in
      parse_args s g cont l f
    with Not_found ->
      prerr_endline ("Unknown function: “" ^ f ^ "”.") ;
      cont_failure ()

