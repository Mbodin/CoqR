(** ** sign.c **)

(** The function names of this section corresponds to the function names
  in the file nmath/sign.c. **)

Set Implicit Arguments.
Require Import Ascii.
Require Export Rcore.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.

Local Coercion int_to_double : Z >-> double.

Definition sign x :=
  ifb ISNAN x then x
  else ifb x > 0 then 1
  else ifb x = 0 then 0
  else (-1)%Z.
