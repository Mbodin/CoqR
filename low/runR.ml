(** RunR
 * Main file. It runs the interactive Coq R interpreter. **)

(** * References to Options **)

let interactive = ref true
let max_steps = ref max_int

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
let show_context = ref true

let show_globals_initial = ref false
let show_result_after_computation = ref true
let show_state_after_computation = ref false
let only_parsing = ref false

(** * Generating List of Options **)

let boolean_switches =
  let make_boolean_switch categories dep verb_small_on verb_small_off verb_verbatim_on verb_verbatim_off pointer command noun =
    (categories, dep, verb_small_on, verb_small_off, verb_verbatim_on, verb_verbatim_off, pointer, command, noun) in
  let category_print = ("show", "hide", "all", "Show", "Hide", "every available information about the state", false) in
  let category_read = ("human", "computer", "readable", "human", "computer", "Makes the output easily readable by a", true) in
  let category_computation = ("show", "hide", "computations", "Show", "Hide", "intermediate computations", false) in
  let print_switch categories dep =
    make_boolean_switch (category_print :: categories) dep "show" "hide" "Show" "Hide" in
  let write_switch categories dep =
    make_boolean_switch (category_read :: categories) dep "use" "no" "Write" "Do not write" in
  let computation_switch categories dep =
    make_boolean_switch (category_computation :: categories) dep "show" "hide" "Show" "Do not show" in
  let show_data_switch = print_switch [] [] show_data "data" "the data of vectors" in
  let show_gp_switch = print_switch [] [] show_gp "gp" "the general purpose field of basic language elements" in
  [
    print_switch [] [] show_memory "memory" "the state of the memory" ;
    print_switch [] [] show_context "context" "the execution context" ;
    print_switch [] [] show_globals "globals" "the value of (non-constant) global variables" ;
    print_switch [] [] show_initials "initials" "the value of constant global variables" ;
    show_gp_switch ;
    print_switch [] [] show_attrib "attrib" "the attribute field of basic language elements" ;
    show_data_switch ;
    print_switch [] [] show_details "details" "the pointers stored in each basic language element" ;
    write_switch [] [] readable_pointers "abr" "pointers in a human readable way" ;
    write_switch [] [show_data_switch] vector_line "inline-vector" "vectors as line instead of column" ;
    write_switch [] [show_data_switch] charvec_string "string" "character vectors as strings instead of a list of characters" ;
    write_switch [] [show_gp_switch] gp_opt "num-gp" "the general purpose field as a number instead of a bit vector" ;
    computation_switch [] [] show_result_after_computation "result" "the result of intermediate computation" ;
    computation_switch [] [] show_state_after_computation "state" "the intermediate state after each computation" ;
    computation_switch [] [] show_globals_initial "globals-initial" "the value of constant global variables in the beginning" ;
    make_boolean_switch [] [] "disable" "enable" "Do not evaluate (only parsing)" "Evaluate" only_parsing "evaluation" "expressions"
  ]

let get_pointer (_, _, _, _, _, _, p, _, _) = p
let get_categories (l, _, _, _, _, _, _, _, _) = l
let get_dependencies (_, d, _, _, _, _, _, _, _) = d

let name_switch v (_, _, vsy, vsn, vvy, vvn, p, c, n) =
  (if v then vsy else vsn) ^ "-" ^ c

let base_suffix = "-base"
let name_switch_base v b =
  name_switch v b ^ if get_dependencies b = [] then "" else base_suffix

let all_categories =
  let rec aux c = function
    | x :: l ->
      aux (c @ List.filter (fun x -> not (List.mem x c)) (get_categories x)) l
    | [] -> c
  in aux [] boolean_switches

let make_options prefix =
  let name_switch v b = prefix ^ name_switch v b in
  let name_switch_base v b = prefix ^ name_switch_base v b in
  [(prefix ^ "no-temporary", Arg.Set no_temporary, "Do not show basic element with a temporary named field") ;
   (prefix ^ "steps", Arg.Set_int max_steps, "Set the maximum number of steps of the interpreter") ]
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
        (prefix ^ vsy ^ "-" ^ c, Arg.Unit (all true), (if r then e ^ " " ^ vvy else vvy ^ " " ^ e) ^ equivalent true) ;
        (prefix ^ vsn ^ "-" ^ c, Arg.Unit (all false), (if r then e ^ " " ^ vvn else vvn ^ " " ^ e) ^ equivalent false) ;
      ]) all_categories)

(** * Reading Arguments **)

let _ =
    Arg.parse
      (("-non-interactive", Arg.Clear interactive, "Non-interactive mode") :: make_options "-")
      (fun str -> prerr_endline ("I do not know what to do with “" ^ str ^ "”."))
      "This programs aims at mimicking the core of R. Usage:\n\trunR.native [OPTIONS]\nCommands are parsed from left to right.\nDuring interactive mode, type “#help” to get some help."

(** * Main Loop **)

let expr_options _ =
  (!show_gp, !gp_opt, !show_attrib, !show_data, !show_details, !vector_line, !charvec_string)

let print_and_continue g r s pr cont =
  Print.print_defined r s (fun s r ->
    if !show_state_after_computation then (
      print_endline "State:" ;
      print_endline (Print.print_state 2 !show_context !show_memory !show_globals !show_initials !no_temporary
        (expr_options ()) !readable_pointers s g)) ;
    if !show_result_after_computation then
      print_endline ("Result: " ^ pr 8 g s r)) cont

let find_opt f l =
  try Some (List.find f l) with
  | Not_found -> None

let _ =
  print_endline "Initialising…" ;
  Print.print_defined (Low.setup_Rmainloop !max_steps Low.empty_state) Low.empty_state (fun s globals ->
    if !show_globals_initial then
      print_endline (Print.print_state 2 !show_context !show_memory!show_globals !show_initials !no_temporary
        (expr_options ()) !readable_pointers s globals)) (fun s globals ->
    match globals with
    | None -> print_endline "Initialisation of constant global variables failed. Halting"
    | Some globals ->
      (** Initialing the read-eval-print-loop **)
      let buf = Lexing.from_channel stdin in
      let rec loop s =
        print_string "> "; flush stdout;
        let success f =
          let f =
            if !only_parsing then f
            else ParserUtils.bind f (fun g r s p ->
              Low.eval_global g r s p) in
          print_and_continue globals (f globals (Low.runs globals !max_steps) s) s (fun n globals s ->
            Print.print_pointer !readable_pointers s globals) (fun s _ -> loop s) in try
          match Parser.main Lexer.lex buf with
          | ParserUtils.Success f ->
            success f
          | ParserUtils.Command "#quit" -> ()
          | ParserUtils.Command cmd ->
            let rec interactive_options =
              let print_help _ =
                List.iter (fun (c, _, h) -> print_endline ("  " ^ c ^ " " ^ h)) interactive_options in
              let print_state _ =
                print_endline "State:" ;
                print_endline (Print.print_state 2 !show_context !show_memory !show_globals !show_initials !no_temporary
                  (expr_options ()) !readable_pointers s globals) in
              ("#help", Arg.Unit print_help, "Print this list of command") ::
              ("#quit", Arg.Unit (fun _ -> ()), "Exit the interpreter") ::
              ("#state", Arg.Unit print_state, "Print the current state") ::
              make_options "#" in
            let exact c cont =
              if c = cmd then (
                cont ();
                print_endline "Done.";
                loop s)
              else success ParserUtils.null in
            match find_opt (fun (c, _, _) -> Print.is_prefix c cmd) interactive_options with
            | None -> loop s (*success ParserUtils.null*)
            (*| Some (c, Arg.Set_int f, _) -> ()*)
            | Some (c, Arg.Set p, _) -> exact c (fun _ -> p := true)
            | Some (c, Arg.Clear p, _) -> exact c (fun _ -> p := false)
            | Some (c, Arg.Unit f, _) -> exact c f
            | Some (c, _, _) -> prerr_endline ("Uncaught command: " ^ c)
        with
        | Parser.Error ->
          print_endline ("Parser error at offset " ^ string_of_int (Lexing.lexeme_start buf) ^ ".")
      in loop s)

