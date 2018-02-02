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
    read_globals g R_NilValue


let rec print_type = function
  | Result_unit _ -> "unit"
  | Result_bool _ -> "bool"
  | Result_int _ -> "int"
  | Result_int_list _ -> "int list"
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

let parse_one_arg : (string -> 'a option) -> ('a -> string) -> 'a -> string -> ('a -> string list -> 'b) -> string list -> 'b
  = fun read print def msg cont -> function
    | [] ->
      prerr_endline ("Missing argument. Assuming " ^ print def ^ ".") ;
      cont def []
    | arg :: l ->
      match read arg with
      | Some a ->
        cont a l
      | None ->
        prerr_endline ("Impossible to parse " ^ msg ^ " from “" ^ arg ^ "”. "
          ^ "Assuming that " ^ print def ^ " was missing here.") ;
        cont def (arg :: l)

let rec parse_args verbose pr_stack opt readable fetch s g r cont l = function
  | Result_unit f ->
    cont l (fun cont s ->
      print_and_continue verbose pr_stack opt g (f g r s) s (fun n g s -> print_unit) (fun s _ -> cont s))
  | Result_bool f ->
    cont l (fun cont s ->
      print_and_continue verbose pr_stack opt g (f g r s) s (fun n g s -> print_bool) (fun s _ -> cont s))
  | Result_int f ->
    cont l (fun cont s ->
      print_and_continue verbose pr_stack opt g (f g r s) s (fun n g s -> print_integer) (fun s _ -> cont s))
  | Result_int_list f ->
    cont l (fun cont s ->
      print_and_continue verbose pr_stack opt g (f g r s) s (fun n g s l -> "[" ^ String.concat "; " (List.map print_integer l) ^ "]") (fun s _ -> cont s))
  | Result_float f ->
    cont l (fun cont s ->
      print_and_continue verbose pr_stack opt g (f g r s) s (fun n g s -> print_float) (fun s _ -> cont s))
  | Result_string f ->
    cont l (fun cont s ->
      print_and_continue verbose pr_stack opt g (f g r s) s (fun n g s -> char_list_to_string) (fun s _ -> cont s))
  | Result_pointer f ->
    cont l (fun cont s ->
      print_and_continue verbose pr_stack opt g (f g r s) s (fun n g s p ->
        print_pointer readable s g p ^
        if fetch then (
          indent n ^ "Pointer value: " ^
          let (_, _, _, expr_opt) = opt in
          print_pointed_value (n + 15) expr_opt readable s g p
        ) else "") (fun s _ -> cont s))
  | Argument_unit f ->
    parse_one_arg read_unit_opt print_unit () "a unit"
      (fun res l -> parse_args verbose pr_stack opt readable fetch s g r cont l (f res)) l
  | Argument_bool f ->
    parse_one_arg read_bool_opt print_bool false "a boolean"
      (fun res l -> parse_args verbose pr_stack opt readable fetch s g r cont l (f res)) l
  | Argument_int f ->
    parse_one_arg read_int_opt print_integer 0 "an integer"
      (fun res l -> parse_args verbose pr_stack opt readable fetch s g r cont l (f res)) l
  | Argument_float f ->
    parse_one_arg read_float_opt print_float 0. "a floating-point number"
      (fun res l -> parse_args verbose pr_stack opt readable fetch s g r cont l (f res)) l
  | Argument_pointer f ->
    parse_one_arg (read_pointer_opt s g) (print_pointer readable s g) (read_globals g R_NilValue) "a pointer"
      (fun res l -> parse_args verbose pr_stack opt readable fetch s g r cont l (f res)) l


let parse_arg_fun verbose pr_stack opt readable fetch s g r cont cont_failure = function
  | [] ->
    prerr_endline "A function name is expected as the argument of this command." ;
    cont_failure ()
  | f :: l ->
    try
      let f = List.assoc f funlist in
      parse_args verbose pr_stack opt readable fetch s g r cont l f
    with Not_found ->
      prerr_endline ("Unknown function: “" ^ f ^ "”.") ;
      cont_failure ()

