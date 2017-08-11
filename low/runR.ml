
open CoqExtract

let _ =
  match setup_Rmainloop max_int empty_state with
  | Result_success (s, g) -> print_string "Success"
  | Result_error (s, str) -> print_string "Error"
  | Result_impossible (s, str) -> print_string "Impossible! Please report."
  | Result_not_implemented str -> print_string "Not implemented"
  | Result_bottom s -> print_string "Stopped because of lack of fuel."

