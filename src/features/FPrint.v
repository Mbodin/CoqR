(** ** print.c **)
(** The function names of this section corresponds to the function names
  in the file main/print.c. **)

Definition do_invisible S (call op args env : SEXP) : result SEXP :=
  add%stack "do_invisible" in
    let%success args_length := R_length globals runs S args using S in
    match args_length with
    | 0 => result_success S (R_NilValue : SEXP)
    | 1 => run%success Rf_check1arg S args call "x" using S in
          read%list args_car, _, _ := args using S in
          result_success S args_car
          | _ => run%success Rf_checkArityCall S op args call using S in
                 result_success S call
    end.
