(** RunR
  Main file. It runs the interactive Coq R interpreter. **)

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
let show_data = ref true
let show_details = ref false
let vector_line = ref false
let charvec_string = ref false
let no_temporary = ref false
let show_context = ref true
let all_context = ref false
let fetch_global = ref false
let print_unlike_R = ref false
let always_print_pointer = ref false

let show_globals_initial = ref false
let show_result_after_computation = ref true
let show_state_after_computation = ref false
let only_parsing = ref false
let fetch_result = ref true

let initial_state = ref ""


(** * Generating List of Options **)

let boolean_switches =
  let make_boolean_switch categories dep verb_small_on verb_small_off verb_verbatim_on verb_verbatim_off pointer command noun expert =
    (categories, dep, verb_small_on, verb_small_off, verb_verbatim_on, verb_verbatim_off, pointer, command, noun, expert) in
  let category_print = ("show", "hide", "all", "Show", "Hide", "every available information about the state", false) in
  let category_read = ("human", "computer", "readable", "human", "computer", "Makes the output easily readable by a", true) in
  let category_computation = ("show", "hide", "computations", "Show", "Hide", "intermediate computations", false) in
  let print_switch categories dep =
    make_boolean_switch (category_print :: categories) dep "show" "hide" "Show" "Hide" in
  let write_switch categories dep =
    make_boolean_switch (category_read :: categories) dep "use" "no" "Write" "Do not write" in
  let computation_switch categories dep =
    make_boolean_switch (category_computation :: categories) dep "show" "hide" "Show" "Do not show" in
  let print_context =
    print_switch [] [] show_context "context" "the execution context" true in
  let print_unlike_R =
    make_boolean_switch [] [] "unlike" "like" "Do not" "Try to (this is an experimental feature)" print_unlike_R "R" "print results as R would" false in
  let print_globals =
    print_switch [] [] show_globals "globals" "the value of (non-constant) global variables" false in
  let print_initials =
    print_switch [] [] show_initials "initials" "the value of constant global variables" true in
  let show_data_switch =
    print_switch [] [print_unlike_R] show_data "data" "the data of vectors" false in
  let show_gp_switch =
    print_switch [] [print_unlike_R] show_gp "gp" "the general purpose field of basic language elements" true in
  let show_result =
    computation_switch [] [] show_result_after_computation "result" "the result of intermediate computation" false in
  [
    print_switch [] [] show_memory "memory" "the state of the memory" true ;
    print_context ;
    print_switch [] [print_context] all_context "all-context" "all fields of contexts" true ;
    print_unlike_R ;
    computation_switch [] [] always_print_pointer "pointer-result" "the value of the pointer returned even when trying to mimic R" true ;
    print_globals ;
    print_initials ;
    print_switch [] [print_globals ; print_initials] fetch_global "fetch-global" "the value pointed by global variables" true ;
    show_gp_switch ;
    print_switch [] [print_unlike_R] show_attrib "attrib" "the attribute field of basic language elements" true ;
    show_data_switch ;
    print_switch [] [] show_details "details" "the pointers stored in each basic language element" true ;
    write_switch [] [] readable_pointers "abr" "pointers in a human readable way" false ;
    write_switch [] [show_data_switch] vector_line "inline-vector" "vectors as line instead of column" false ;
    write_switch [] [show_data_switch] charvec_string "string" "character vectors as strings instead of a list of characters" false ;
    write_switch [] [show_gp_switch] gp_opt "num-gp" "the general purpose field as a number instead of a bit vector" true ;
    show_result ;
    computation_switch [] [show_result] fetch_result "result-value" "the value pointed by the current computation" true ;
    computation_switch [] [] show_state_after_computation "state" "the intermediate state after each computation" false ;
    computation_switch [] [] show_globals_initial "globals-initial" "the value of constant global variables in the beginning" true ;
    make_boolean_switch [] [] "disable" "enable" "Do not evaluate (only parsing)" "Evaluate" only_parsing "evaluation" "expressions from the input" true
  ]

let get_pointer (_, _, _, _, _, _, p, _, _, _) = p
let get_categories (l, _, _, _, _, _, _, _, _, _) = l
let get_dependencies (_, d, _, _, _, _, _, _, _, _) = d
let is_expert (_, _, _, _, _, _, _, _, _, e) = e

let name_switch v (_, _, vsy, vsn, vvy, vvn, p, c, n, _) =
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

let make_options expert prefix default =
  let name_switch v b = prefix ^ name_switch v b in
  let name_switch_base v b = prefix ^ name_switch_base v b in
  let doc_strict str =
    if expert then str else "" in
  [(prefix ^ "no-temporary", Arg.Set no_temporary, doc_strict "Do not show basic element with a temporary named field.") ;
   (prefix ^ "steps", Arg.Set_int max_steps, doc_strict "Set the maximum number of steps of the interpreter.") ;
   (prefix ^ "only-parsing", Arg.Set only_parsing, doc_strict ("Synonym of " ^ prefix ^ "disable-evaluation.")) ]
  @ List.concat (List.map (fun b ->
      let (_, d, vsy, vsn, vvy, vvn, p, c, n, e) = b in
      let doc str =
        if e = true && expert = false then ""
        else str in
      let deps = String.concat " " (List.map (name_switch true) d) in
      let print_dep =
        " (to be used in combination with " ^ deps ^ ")" in
      let default b =
        if b then " (" ^ default ^ ")" else "" in
      let ret dep_text print_dep = [
          (name_switch true b ^ dep_text, Arg.Set p, doc_strict (vvy ^ " " ^ n ^ print_dep ^ "." ^ default !p)) ;
          (name_switch false b ^ dep_text, Arg.Clear p, doc_strict (vvn ^ " " ^ n ^ print_dep ^ "." ^ default (not !p)))
        ] in
      let set_with_dep v _ =
        List.iter (fun b -> get_pointer b := true) d ;
        p := v in
      if d = [] then
        ret "" ""
      else
        ret base_suffix print_dep @ [
            (name_switch true b, Arg.Unit (set_with_dep true),
              doc (vvy ^ " " ^ n ^ " (equivalent to " ^ deps ^ " " ^ name_switch_base true b ^ ").")) ;
            (name_switch false b, Arg.Unit (set_with_dep false),
              doc (vvn ^ " " ^ n ^ " (equivalent to " ^ deps ^ " " ^ name_switch_base false b ^ ")."))
          ]) boolean_switches)
  @ List.concat (List.map (fun c ->
      let this_category =
        List.filter (fun b -> List.mem c (get_categories b)) boolean_switches in
      let (vsy, vsn, c, vvy, vvn, e, r) = c in
      let equivalent v =
        " (equivalent to " ^ String.concat " " (List.map (name_switch_base v) this_category) ^ ")." in
      let all v _ =
        List.iter (fun b -> get_pointer b := v) this_category in [
        (prefix ^ vsy ^ "-" ^ c, Arg.Unit (all true), (if r then e ^ " " ^ vvy else vvy ^ " " ^ e) ^ equivalent true) ;
        (prefix ^ vsn ^ "-" ^ c, Arg.Unit (all false), (if r then e ^ " " ^ vvn else vvn ^ " " ^ e) ^ equivalent false) ;
      ]) all_categories)

let text_expert prefix =
  "This program accepts a large number of options. To avoid frightening new users, they are hidden by default. This option makes " ^ prefix ^ "help print all of them."

let sort_commands =
  List.sort (fun (s1, _, _) (s2, _, _) -> compare s1 s2)


(** * Reading Arguments **)

let _ =
    let arguments = ref [] in
    let all_arguments =
      sort_commands (
        ("-non-interactive", Arg.Clear interactive, "Non-interactive mode.") ::
        ("-initial-state", Arg.Set_string initial_state, "Load a state from an external file and uses it as initial state.") ::
        ("-expert-mode", Arg.Unit (fun _ -> prerr_endline "This program is already in expert mode."), text_expert "-" ^ " (current)") ::
          make_options true "-" "default") in
    let simple_arguments =
      sort_commands (
        ("-non-interactive", Arg.Clear interactive, "") ::
        ("-initial-state", Arg.Set_string initial_state, "") ::
        ("-expert-mode", Arg.Unit (fun _ -> arguments := all_arguments), text_expert "-") ::
        make_options false "-" "default") in
    arguments := simple_arguments ;
    Arg.parse_dynamic arguments
      (fun str -> prerr_endline ("I do not know what to do with “" ^ str ^ "”."))
      "This programs aims at mimicking the core of R. Usage:\n\trunR.native [OPTIONS]\nCommands are parsed from left to right.\nDuring interactive mode, type “#help” to get some help."

(** * Main Loop **)

let run_options _ =
  (!show_context, !all_context, !show_memory, !show_globals, !show_initials, !no_temporary, !fetch_global, !readable_pointers)

let expr_options _ =
  ((!show_gp, !gp_opt, !show_attrib, !show_data, !show_details, !vector_line, !charvec_string), !print_unlike_R)

let find_opt f l =
  try Some (List.find f l) with
  | Not_found -> None

type type_s_globals = Low.state * Low.globals

let expert_mode = ref false

let _ =
  let initialising_function =
    if !initial_state = "" then (
      print_endline "Initialising…" ;
      Low.setup_Rmainloop !max_steps Low.empty_state
    ) else (
      print_endline ("Reading state from " ^ !initial_state ^ "…") ;
      let inchannel = open_in_bin !initial_state in
      let (s, globals) = (Marshal.from_channel inchannel : type_s_globals) in
      Low.Result_success (s, globals)) in
  Print.print_defined initialising_function Low.empty_state (fun s globals ->
    if !show_globals_initial then
      print_endline (Print.print_state 2 (run_options ()) (expr_options ()) s globals)) (fun s globals ->
    match globals with
    | None -> print_endline "Initialisation of constant global variables failed. Halting"
    | Some globals ->
      let buf = Lexing.from_channel stdin in
      let rec loop s =
        (** The read-eval-print-loop **)
        print_string "> " ; flush stdout ;
        let success f =
          let f =
            if !only_parsing then f
            else ParserUtils.bind f (fun g r s p ->
              Low.eval_global g r s p) in
          Print.print_and_continue
            (!show_state_after_computation, !show_result_after_computation, run_options (), expr_options ())
            globals (f globals (Low.runs !max_steps globals) s) s (fun n globals s p ->
              if !print_unlike_R then
                Print.print_pointer !readable_pointers s globals p ^
                if !fetch_result then (
                  Print.indent n ^ "Pointer value: " ^
                  Print.print_pointed_value (n + 15) (expr_options ()) !readable_pointers s globals p
                ) else ""
              else
                let str =
                  if !always_print_pointer then
                    Print.print_pointer !readable_pointers s globals p ^ ": "
                  else "" in
                str ^ Print.print_pointed_value (n + String.length str) (expr_options ()) !readable_pointers s globals p)
            (fun s _ -> loop s) in
        ParserUtils.parseInit () ;
        try match Parser.main Lexer.lex buf with
        | ParserUtils.Success f ->
          success f
        | ParserUtils.Command cmd ->
          (** Parsing commands **)
          let interactive_options = ref [] in
          let rec make_interactive_options _ =
            let print_help _ =
              List.iter (fun (c, _, h) -> if h <> "" then print_endline ("  " ^ c ^ " " ^ h)) !interactive_options in
            let dummy _ = () in
            let print_state _ =
              print_endline "State:" ;
              print_endline (Print.print_state 2 (run_options ()) (expr_options ()) s globals) in
            let get_and_print_memory_cell str =
              let p = Debug.read_pointer s globals str in
              print_endline (Print.print_pointed_value 2 (expr_options ()) !readable_pointers s globals p) in
            let get_and_print_list str =
              let p = Debug.read_pointer s globals str in
              print_endline (Print.print_list 2 (expr_options ()) !readable_pointers s globals p) in
            let print_list_fun _ =
              print_endline (Debug.list_all_fun 2) in
            let save_state str =
              print_endline ("Saving current state into the file " ^ str ^ "…") ;
              let outchannel = open_out_bin str in
              Marshal.to_channel outchannel ((s, globals) : type_s_globals) [Marshal.Closures] in
            let set_expert _ =
              expert_mode := true ;
              interactive_options := make_interactive_options () in
            sort_commands (
              List.map (fun (c, a, d, e) ->
                  if e = true && !expert_mode = false then (c, a, "")
                  else (c, a, d)) (
                ("#help", Arg.Unit print_help, "Print this list of command", false) ::
                ("#quit", Arg.Unit dummy, "Exit the interpreter", false) ::
                ("#expert-mode", Arg.Unit set_expert, text_expert "#" ^ (if !expert_mode then " (current)" else ""), false) ::
                ("#state", Arg.Unit print_state, "Print the current state", false) ::
                ("#show", Arg.String get_and_print_memory_cell, "Print the content of the requested memory cell", true) ::
                ("#show-list", Arg.String get_and_print_list, "Assuming that the requested memory cell is a list, print the list.", true) ::
                ("#execute", Arg.Unit dummy, "Execute a Coq function for debugging purposes (Warning: using this command may lead to states not reachable in a normal execution)", true) ::
                ("#list-fun", Arg.Unit print_list_fun, "Lists the available functions for the command #execute", true) ::
                ("#save-state", Arg.String save_state, "Save the state into an external file (this state can be reused using -initial-state)", true) :: []) @
                make_options !expert_mode "#" "current") in
          interactive_options := make_interactive_options () ;
          let check_change_state seen_state_change cmd =
            let parsing_warning = function
              | "#execute" | "#show" | "#show-list" ->
                if seen_state_change then
                  prerr_endline "Warning: pointers are parsed before the first state change. Possible inconsistency." ;
              | _ -> () in
            let printing_warning = function
              | "#show" | "#show-list" | "#save-state" ->
                if seen_state_change then
                  prerr_endline "Warning: the state is printed before its first change. Possible inconsistency." ;
              | _ -> () in
            parsing_warning cmd ;
            printing_warning cmd in
          let rec parse_args at_leat_one seen_state_change cont = function
            | [] ->
              let s = cont s in
              if at_leat_one then
                print_endline "Done." ;
              loop s
            | "#quit" :: l -> ignore (cont s)
            | "#execute" as cmd :: l ->
              check_change_state seen_state_change cmd ;
              Debug.parse_arg_fun
                (!show_state_after_computation, !show_result_after_computation, run_options (), expr_options ())
                !readable_pointers !fetch_result s globals (Low.runs !max_steps globals)
                (fun l f ->
                  parse_args true true (fun s ->
                    let s = cont s in
                    f (fun s -> s) s) l)
                (fun _ ->
                  prerr_endline "A failure occurred during argument parsing. Ignoring this command." ;
                  parse_args at_leat_one seen_state_change cont l) l
            | cmd :: l ->
              check_change_state seen_state_change cmd ;
              let continue l cont' =
                parse_args true seen_state_change (fun s -> cont' (cont s)) l in
              match find_opt (fun (c, _, _) -> c = cmd) !interactive_options with
              | None ->
                if at_leat_one then (
                  if cmd.[0] = '#' then
                    prerr_endline ("Unknown option: " ^ cmd ^ ".\nNo command has been run.")
                  else
                    prerr_endline ("Don’t know what to do with “" ^ cmd ^ "”.\nNo command has been run.")) ;
                loop s
              | Some (c, Arg.Set_int p, _) ->
                (match l with
                 | [] ->
                   prerr_endline ("Missing operand for command " ^ c ^ ". Assuming 0.") ;
                   continue [] (fun s -> p := 0 ; s)
                 | i :: l ->
                   let i =
                     try int_of_string i
                     with
                     | Failure _ ->
                       prerr_endline ("Impossible to parse “" ^ i ^ "” as a number. Assuming 0.") ;
                       0
                   in continue l (fun s -> p := i ; s))
              | Some (c, Arg.String f, _) ->
                (match l with
                 | [] ->
                   prerr_endline ("Missing operand for command " ^ c ^ ". Assuming the empty string.") ;
                   continue [] (fun s -> f "" ; s)
                 | str :: l ->
                   continue l (fun s -> f str ; s))
              | Some (c, Arg.Set p, _) -> continue l (fun s -> p := true ; s)
              | Some (c, Arg.Clear p, _) -> continue l (fun s -> p := false ; s)
              | Some (c, Arg.Unit f, _) -> continue l (fun s -> f () ; s)
              | Some (c, _, _) ->
                prerr_endline ("Uncaught command: " ^ c) ;
                loop s
          in parse_args false false (fun s -> s) (List.filter (fun s -> s <> "") (Print.split_on_char ' ' cmd))
        with
        | Parser.Error ->
          print_endline ("Error: Parser error at offset " ^ string_of_int (Lexing.lexeme_start buf) ^ ".") ;
          loop s
        | Lexer.SyntaxError msg ->
          print_endline ("Error: Lexer error: " ^ msg ^ ".") ;
          loop s
        | Failure msg ->
          print_endline ("Error: " ^ msg) ;
          loop s in
      if !interactive then loop s
      else ())

