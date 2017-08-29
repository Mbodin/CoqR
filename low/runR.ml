
let interactive = ref true
let readable_pointers = ref true
let show_globals = ref true
let max_steps = ref max_int

let _ =
  Arg.parse [
      ("-non-interactive", Arg.Clear interactive, "Non-interactive mode") ;
      ("-no-abr", Arg.Clear readable_pointers, "Do not write down pointers in a more readable way") ;
      ("-no-globals", Arg.Clear show_globals, "Hide the value of global variables") ;
      ("-steps", Arg.Set_int max_steps, "Set the maximum number of steps of the interpreter") ]
    (fun str -> prerr_endline ("I do not know what to do with “" ^ str ^ "”."))
    "This programs aims to mimic the core of R. Usage:"


let _ =
  Print.print_defined (Low.setup_Rmainloop !max_steps Low.empty_state) Low.empty_state
    (fun s g ->
      print_endline (Print.print_state 0 !show_globals !readable_pointers s g))

