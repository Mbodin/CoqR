(** ** printutils.c **)

(** The function names of this section corresponds to the function names
  in the file main/printutils.c. **)

Set Implicit Arguments.
Require Import Ascii.
Require Export Rcore.
Require Export Util.
Require Export Connections.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.

Local Coercion int_to_double : Z >-> double.


(** This function is inspired from [Rprintf]. **)
Definition Rprint S str :=
  add%stack "Rprint" in
  let con_num := R_OutputCon S in
  run_print S con_num str.
