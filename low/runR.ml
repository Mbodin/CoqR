
let interactive = ref true
let readable_pointers = ref true
let show_memory = ref false
let show_globals = ref true
let show_initials = ref false
let show_gp = ref false
let gp_opt = ref false
let show_attrib = ref false
let show_data = ref false
let show_details = ref false
let vector_line = ref false
let charvec_string = ref false
let no_temporary = ref false
let max_steps = ref max_int

let boolean_switches =
  let make_boolean_switch categories verb_small_on verb_small_off verb_verbatim_on verb_verbatim_off pointer command noun =
    (categories, verb_small_on, verb_small_off, verb_verbatim_on, verb_verbatim_off, pointer, command, noun) in
  let print_switch categories =
    make_boolean_switch (("show", "hide", "all", "Show", "Hide", "everything") :: categories) "show" "hide" "Show" "Hide" in [
    print_switch [] show_memory "memory" "the state of the memory" ;
    print_switch [] show_globals "globals" "the value of (non-constant) global variables" ;
    print_switch [] show_initials "initials" "the value of constant global variables" ;
    print_switch [] show_gp "gp" "the general purpose field of basic language elements" ;
    print_switch [] show_attrib "attrib" "the attribute field of basic language elements" ;
    print_switch [] show_data "data" "the data of vectors" ;
    print_switch [] show_details "details" "the pointers stored in each basic language element"
  ]

let get_pointer (_, _, _, _, _, p, _, _) = p
let get_categories (l, _, _, _, _, _, _, _) = l

let all_categories =
  let rec aux c = function
    | x :: l ->
      aux (c @ List.filter (fun x -> not (List.mem x c)) (get_categories x)) l
    | [] -> c
  in aux [] boolean_switches

let _ =
  Arg.parse ([
      ("-non-interactive", Arg.Clear interactive, "Non-interactive mode") ;
      ("-no-abr", Arg.Clear readable_pointers, "Do not write down pointers in a more readable way") ;
      ("-vector-line", Arg.Set vector_line, "Show vectors as line instead of column (to be used in combination with -show-data)") ;
      ("-charvec-string", Arg.Set charvec_string, "Show character vectors as strings instead of a list of characters (to be used in combination with -show-data)") ;
      ("-no-temporary", Arg.Set no_temporary, "Do not show basic element with a temporary named field") ;
      ("-steps", Arg.Set_int max_steps, "Set the maximum number of steps of the interpreter") ;
      ("-bit-gp", Arg.Set gp_opt, "Show the general purpose field as a bit field instead of a number (to be used in combination with -show-gp)") ]
    @ List.concat (List.map (fun (_, vsy, vsn, vvy, vvn, p, c, n) ->
        let default b =
          if b then " (default)" else "" in [
          ("-" ^ vsy ^ "-" ^ c, Arg.Set p, vvy ^ " " ^ n ^ default !p) ;
          ("-" ^ vsn ^ "-" ^ c, Arg.Clear p, vvn ^ " " ^ n ^ default (not !p)) ]) boolean_switches)
    @ List.concat (List.map (fun c ->
        let this_category =
          List.filter (fun b -> List.mem c (get_categories b)) boolean_switches in
        let (vsy, vsn, c, vvy, vvn, e) = c in
        let all v _ =
          List.iter (fun b -> get_pointer b := v) this_category in [
          ("-" ^ vsy ^ "-" ^ c, Arg.Unit (all true), vvy ^ " " ^ e) ;
          ("-" ^ vsn ^ "-" ^ c, Arg.Unit (all false), vvn ^ " " ^ e) ;
        ]) all_categories))
    (fun str -> prerr_endline ("I do not know what to do with “" ^ str ^ "”."))
    "This programs aims at mimicking the core of R. Usage:"


let _ =
  Print.print_defined (Low.setup_Rmainloop !max_steps Low.empty_state) Low.empty_state
    (fun s g ->
      print_endline (Print.print_state 0 !show_memory !show_globals !show_initials !no_temporary
        (!show_gp, !gp_opt, !show_attrib, !show_data, !show_details, !vector_line, !charvec_string)
        !readable_pointers s g))

