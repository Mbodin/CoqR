(** Rinvariants.
  Contains the proofs of some invariants respected by the functions
  defined in Reval, Rinit, and Rfeatures. **)

Set Implicit Arguments.
Require Export Rinit Rfeatures.


(* TODO *)

(* I think that it would be easy to use tactics to check that [setup_Rmainloop]
  is indeed of the form [result_success S globals] or something like that. *)

(** It would be nice to prove that the read-eval-print-loop can not
  return a [result_impossible]. **)

(** If runs returns a result, then adding fuel does not change it. **)

