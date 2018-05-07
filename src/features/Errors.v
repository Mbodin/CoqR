(** ** errors.c **)

(** The function names of this section corresponds to the function names
  in the file main/errors.c. **)

Set Implicit Arguments.
Require Import Ascii.
Require Export Rcore.


Definition WrongArgCount A S s : result A :=
  add%stack "WrongArgCount" in
  result_error S ("Incorrect number of arguments to " ++ s ++ ".").
