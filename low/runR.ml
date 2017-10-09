
let interactive = ref true
let readable_pointers = ref true
let show_memory = ref false
let show_globals = ref true
let show_initials = ref false
let show_gp = ref false
let gp_opt = ref true
let show_attrib = ref false
let show_data = ref false
let show_details = ref false
let vector_line = ref false
let charvec_string = ref false
let no_temporary = ref false
let max_steps = ref max_int

let boolean_switches =
  let make_boolean_switch categories dep verb_small_on verb_small_off verb_verbatim_on verb_verbatim_off pointer command noun =
    (categories, dep, verb_small_on, verb_small_off, verb_verbatim_on, verb_verbatim_off, pointer, command, noun) in
  let category_print = ("show", "hide", "all", "Show", "Hide", "everything", false) in
  let category_read = ("human", "computer", "readable", "human", "computer", "Makes the output easily readable by a", true) in
  let print_switch categories dep =
    make_boolean_switch (category_print :: categories) dep "show" "hide" "Show" "Hide" in
  let write_switch categories dep =
    make_boolean_switch (category_read :: categories) dep "use" "no" "Write" "Do not write" in
  let show_data_switch = print_switch [] [] show_data "data" "the data of vectors" in
  let show_gp_switch = print_switch [] [] show_gp "gp" "the general purpose field of basic language elements" in
  [
    print_switch [] [] show_memory "memory" "the state of the memory" ;
    print_switch [] [] show_globals "globals" "the value of (non-constant) global variables" ;
    print_switch [] [] show_initials "initials" "the value of constant global variables" ;
    show_gp_switch ;
    print_switch [] [] show_attrib "attrib" "the attribute field of basic language elements" ;
    show_data_switch ;
    print_switch [] [] show_details "details" "the pointers stored in each basic language element" ;
    write_switch [] [] readable_pointers "abr" "pointers in a human readable way" ;
    write_switch [] [show_data_switch] vector_line "inline-vector" "vectors as line instead of column" ;
    write_switch [] [show_data_switch] charvec_string "string" "character vectors as strings instead of a list of characters" ;
    write_switch [] [show_gp_switch] gp_opt "num-gp" "the general purpose field as a number instead of a bit vector"
  ]

let get_pointer (_, _, _, _, _, _, p, _, _) = p
let get_categories (l, _, _, _, _, _, _, _, _) = l
let get_dependencies (_, d, _, _, _, _, _, _, _) = d

let name_switch v (_, _, vsy, vsn, vvy, vvn, p, c, n) =
  "-" ^ (if v then vsy else vsn) ^ "-" ^ c

let base_suffix = "-base"
let name_switch_base v b =
  name_switch v b ^ if get_dependencies b = [] then "" else base_suffix

let all_categories =
  let rec aux c = function
    | x :: l ->
      aux (c @ List.filter (fun x -> not (List.mem x c)) (get_categories x)) l
    | [] -> c
  in aux [] boolean_switches

let _ =
  Arg.parse ([
      ("-non-interactive", Arg.Clear interactive, "Non-interactive mode") ;
      ("-no-temporary", Arg.Set no_temporary, "Do not show basic element with a temporary named field") ;
      ("-steps", Arg.Set_int max_steps, "Set the maximum number of steps of the interpreter") ]
    @ List.concat (List.map (fun b ->
        let (_, d, vsy, vsn, vvy, vvn, p, c, n) = b in
        let deps = String.concat " " (List.map (name_switch true) d) in
        let print_dep =
          " (to be used in combination with " ^ deps ^ ")" in
        let default b =
          if b then " (default)" else "" in
        let ret dep_text print_dep = [
            (name_switch true b ^ dep_text, Arg.Set p, vvy ^ " " ^ n ^ print_dep ^ default !p) ;
            (name_switch false b ^ dep_text, Arg.Clear p, vvn ^ " " ^ n ^ print_dep ^ default (not !p))
          ] in
        let set_with_dep v _ =
          List.iter (fun b -> get_pointer b := true) d ;
          p := v in
        if d = [] then
          ret "" ""
        else
          ret base_suffix print_dep @ [
              (name_switch true b, Arg.Unit (set_with_dep true),
                vvy ^ " " ^ n ^ " (equivalent to " ^ deps ^ " " ^ name_switch_base true b ^ ")") ;
              (name_switch false b, Arg.Unit (set_with_dep false),
                vvn ^ " " ^ n ^ " (equivalent to " ^ deps ^ " " ^ name_switch_base false b ^ ")")
            ]) boolean_switches)
    @ List.concat (List.map (fun c ->
        let this_category =
          List.filter (fun b -> List.mem c (get_categories b)) boolean_switches in
        let (vsy, vsn, c, vvy, vvn, e, r) = c in
        let equivalent v =
          " (equivalent to " ^ String.concat " " (List.map (name_switch_base v) this_category) ^ ")" in
        let all v _ =
          List.iter (fun b -> get_pointer b := v) this_category in [
          ("-" ^ vsy ^ "-" ^ c, Arg.Unit (all true), (if r then e ^ " " ^ vvy else vvy ^ " " ^ e) ^ equivalent true) ;
          ("-" ^ vsn ^ "-" ^ c, Arg.Unit (all false), (if r then e ^ " " ^ vvn else vvn ^ " " ^ e) ^ equivalent false) ;
        ]) all_categories))
    (fun str -> prerr_endline ("I do not know what to do with “" ^ str ^ "”."))
    "This programs aims at mimicking the core of R. Usage:\n\trunR.native [OPTIONS]"

let _ =
  Print.print_defined (Low.setup_Rmainloop !max_steps Low.empty_state) Low.empty_state
    (fun s g ->
      print_endline (Print.print_state 0 !show_memory !show_globals !show_initials !no_temporary
        (!show_gp, !gp_opt, !show_attrib, !show_data, !show_details, !vector_line, !charvec_string)
        !readable_pointers s g))

