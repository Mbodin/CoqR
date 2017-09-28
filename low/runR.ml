
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
let no_temporary = ref false
let max_steps = ref max_int

let _ =
  Arg.parse [
      ("-non-interactive", Arg.Clear interactive, "Non-interactive mode") ;
      ("-no-abr", Arg.Clear readable_pointers, "Do not write down pointers in a more readable way") ;
      ("-show-memory", Arg.Set show_memory, "Show the state of the memory") ;
      ("-hide-globals", Arg.Clear show_globals, "Hide the value of (non-constant) global variables") ;
      ("-show-initials", Arg.Set show_initials, "Show the value of constant global variables") ;
      ("-show-gp", Arg.Set show_gp, "Show the general purpose field of basic language elements") ;
      ("-bit-gp", Arg.Set gp_opt, "Show the general purpose field as a bit field instead of a number") ;
      ("-show-attrib", Arg.Set show_attrib, "Show the attribute field of basic language elements") ;
      ("-show-data", Arg.Set show_data, "Show the data of vectors") ;
      ("-show-details", Arg.Set show_details, "Show the pointers stored in each basic language element") ;
      ("-no-temporary", Arg.Set no_temporary, "Do not show basic element with a temporary named field") ;
      ("-steps", Arg.Set_int max_steps, "Set the maximum number of steps of the interpreter") ]
    (fun str -> prerr_endline ("I do not know what to do with “" ^ str ^ "”."))
    "This programs aims at mimicking the core of R. Usage:"


let _ =
  Print.print_defined (Low.setup_Rmainloop !max_steps Low.empty_state) Low.empty_state
    (fun s g ->
      print_endline (Print.print_state 0 !show_memory !show_globals !show_initials !no_temporary
        (!show_gp, !gp_opt, !show_attrib, !show_data, !show_details) !readable_pointers s g))

