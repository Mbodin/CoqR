(** Rinvariants.
  Contains the proofs of some invariants respected by the functions
  defined in Rcore, Rinit, and Rfeatures. **)

Set Implicit Arguments.
Require Export Rinit Rfeatures Path.


Inductive null_pointer_exceptions : path -> Prop :=
  .

Record safe_state (S : state) := make_safe_state {
    no_null_pointer : forall p,
      ~ null_pointer_exceptions p ->
      move_along_path p S <> Some NULL ;
    safe_bindings : forall p pointer,
      move_along_path p S = Some pointer ->
      pointer <> NULL ->
      exists pointer',
        read_SExp S pointer = Some pointer'
  }.


(* TODO *)

(* I think that it would be easy to use tactics to check that [setup_Rmainloop]
  is indeed of the form [result_success S globals] or something like that. *)

(** It would be nice to prove that the read-eval-print-loop can not
  return a [result_impossible]. **)

(** If runs returns a result, then adding fuel does not change it. **)

