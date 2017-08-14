
open Low

let char_list_to_string str =
  String.concat "" (List.map (String.make 1) str)

let _ =
  match setup_Rmainloop max_int empty_state with
  | Result_success (s, g) ->
    print_endline "Success"
  | Result_error (s, str) ->
    print_endline ("Error: " ^ char_list_to_string str)
  | Result_impossible (s, str) ->
    print_endline ("Impossible! Please report. " ^ char_list_to_string str)
  | Result_not_implemented str ->
    print_endline ("Not implemented: " ^ char_list_to_string str)
  | Result_bottom s ->
    print_endline "Stopped because of lack of fuel."

