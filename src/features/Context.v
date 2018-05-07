(** ** context.c **)

(** The function names of this section corresponds to the function names
  in the file main/context.c. **)

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

Fixpoint do_parentframe_loop cptr t (n : int) :=
  match context_nextcontext cptr with
  | None => (R_GlobalEnv : SEXP)
  | Some cptr_nextcontext =>
    ifb context_type_mask (context_callflag cptr) Ctxt_Function then
      ifb context_cloenv cptr = t then
        ifb n = 1 then context_sysparent cptr
        else do_parentframe_loop cptr_nextcontext (context_sysparent cptr) (n - 1)
      else do_parentframe_loop cptr_nextcontext t n
    else do_parentframe_loop cptr_nextcontext t n
  end.

Definition do_parentframe S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_parentframe" in
  run%success Rf_checkArityCall S op args call using S in
  read%list args_car, _, _ := args using S in
  let t := args_car in
  let%success n := asInteger globals S t using S in
  ifb n = NA_INTEGER \/ n < 1 then
    result_error S "Invalid ‘n’ value."
  else
    let cptr := R_GlobalContext S in
    let t := context_sysparent cptr in
    result_success S (do_parentframe_loop cptr t n).
