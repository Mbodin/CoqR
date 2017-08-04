(** Rinit.
 * Initialises global variables. **)

Set Implicit Arguments.
Require Export Reval.


(** * Initial Memory **)

(** Some initialisations from the functions [InitBaseEnv]
  * and [InitGlobalEnv] in main/envir.c. **)

(* TODO: We are now *after* the definition of [NewEnvironment] and can now use it.
 * I think that it would be easy to use tactics to check that [initial_allocations]
 * is indeed of the form [result_success S Globals] or something like that. *)

Definition initial_allocations :=
  let newEnvironmentEmpty S rho :=
    (** This function behaves like [NewEnvironment] when one
      * of its first two argument pointers are [R_NilValue]. **)
    alloc_memory_SExp S (make_SExpRec_env R_NilValue R_NilValue rho) in
  let S := empty_memory in
  let (S, R_EmptyEnv) := newEnvironmentEmpty S R_NilValue in
  let (S, R_BaseEnv) := newEnvironmentEmpty S R_EmptyEnv in
  let (S, R_GlobalEnv) := newEnvironmentEmpty S R_BaseEnv in
  let (S, R_BaseNamespace) := newEnvironmentEmpty S R_GlobalEnv in
  (* TODO: R_PreserveObject and SET_SYMVALUE *)
  let (S, R_NamespaceRegistry) := newEnvironmentEmpty S R_NilValue in
  (* TODO: R_PreserveObject and defineVar *)
  (S, R_EmptyEnv, R_BaseEnv, R_GlobalEnv, R_BaseNamespace, R_NamespaceRegistry).

Definition initial_memory :=
  let '(m, _, _, _, _, _) := initial_allocations in m.

Definition R_EmptyEnv :=
  let '(_, R_EmptyEnv, _, _, _, _) := initial_allocations in R_EmptyEnv.

Definition R_BaseEnv :=
  let '(_, _, R_BaseEnv, _, _, _) := initial_allocations in R_BaseEnv.

Definition R_GlobalEnv :=
  let '(_, _, _, R_GlobalEnv, _, _) := initial_allocations in R_GlobalEnv.

Definition R_BaseNamespace :=
  let '(_, _, _, _, R_BaseNamespace, _) := initial_allocations in R_BaseNamespace.

Definition R_NamespaceRegistry :=
  let '(_, _, _, _, _, R_NamespaceRegistry) := initial_allocations in R_NamespaceRegistry.


(** * Initial State **)

Definition R_Toplevel := {|
     nextcontext := None ;
     callflag := Ctxt_TopLevel ;
     promargs := R_NilValue ;
     callfun := R_NilValue ;
     sysparent := R_BaseEnv ;
     call := R_NilValue ;
     cloenv := R_BaseEnv ;
     conexit := R_NilValue
  |}.

Definition initial_state := {|
    state_memory := initial_memory ;
    state_context := R_Toplevel
  |}.


Definition Globals : Globals := {|
    TODO
  |}.


(** * Closing the Loop **)

Fixpoint runs max_step : runs_type :=
  match max_step with
  | O => {|
      runs_while := fun _ S _ _ _ => result_bottom S ;
      runs_eval := fun S _ _ => result_bottom S
    |}
  | S max_step =>
    let wrap {A : Type} (f : runs_type -> A) : A :=
      f (runs max_step) in
    let wrap_dep {A} (f : forall B : Type, runs_type -> A B) B : A B :=
      f B (runs max_step) in {|
      runs_while := wrap_dep while ;
      runs_eval := wrap eval
    |}
  end.


(** * Proofs **)

(* TODO *)

(** It would be nice to prove that the read-eval-print-loop can not
 * return a [result_impossible]. **)

(** If runs returns a result, then adding fuel does not change it. **)

(** The property we want to eventually prove is that if [eval] returns
 * a result, then the C function eval does similarly. **)

