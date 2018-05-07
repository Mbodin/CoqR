(** ** complex.c **)

(** The function names of this section corresponds to the function names
  in the file main/complex.c. **)

Set Implicit Arguments.
Require Import Ascii.
Require Export Rcore.
Require Export Util.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.

Local Coercion int_to_double : Z >-> double.



Definition complex_binary (S : state) (code : int) (s1 s2 : SEXP) : result SEXP :=
  unimplemented_function "complex_binary".

Definition complex_unary S (code : int) s1 :=
  add%stack "complex_unary" in
  ifb code = PLUSOP then
    result_success S s1
  else ifb code = MINUSOP then
    let%success ans :=
      if%success NO_REFERENCES S s1 using S then
        result_success S s1
      else duplicate globals runs S s1 using S in
    read%VectorComplex s1_ := s1 using S in
    let px := VecSxp_data s1_ in
    let pa := ArrayListExtra.map (fun x =>
      make_Rcomplex (Double.opp (Rcomplex_r x)) (Double.opp (Rcomplex_i x))) px in
    write%VectorComplex ans := pa using S in
    result_success S ans
    else result_error S "Invalid unary operator.".

Definition complex_math1 (S : state) (call op args env : SEXP) : result SEXP :=
  unimplemented_function "complex_math1".
