(** ** array.c **)
(** The function names of this section corresponds to the function names
  in the file main/array.c. **)

Definition do_length S (call op args env : SEXP) : result SEXP :=
  add%stack "do_length" in
    run%success Rf_checkArityCall S op args call using S in
    run%success Rf_check1arg S args call "x" using S in
    read%list args_car, _, _ := args using S in
    let x := args_car in
    let%success x_obj := isObject S x using S in
    let%success (disp, ans) := DispatchOrEval globals runs S call op "length" args env false true using S in
    if x_obj && disp then
        let%success ans_length := R_length globals runs S ans using S in
        let%success ans_type := TYPEOF S ans using S in
        ifb ans_length = 1 /\ ans_type = RealSxp then
            read%Real d := ans at 0 using S in
            ifb R_FINITE d /\ d >= 0 /\ d <= INT_MAX /\ Double.floor d = d then
                let%success ans := coerceVector globals runs S ans IntSxp using S in
                    result_success S ans
            else
                result_success S ans
        else
            result_success S ans
    else
    (** Assuming LONG_VECTOR_SUPPORT is false **)
        let%success x_length := R_length globals runs S x using S in
        let (S, s_x) := ScalarInteger globals S x_length in
            result_success S s_x.
