(** Rinit.
 * Initialises global variables. **)

Set Implicit Arguments.
Require Export Reval.

(* TODO: to bew sorted. *)
Definition ScalarString (S : state) (x : SExpRec_pointer) : result SExpRec_pointer :=
  result_not_implemented "[ScalarString] TODO".
(* TODO. See include/Rinlinedfuns.h. It seems to be an indirection to a string (to only manipulate arrays of strings at the top level). *)

(* TODO: to bew sorted. *)
Definition mkChar (S : state) (str : string) : result SExpRec_pointer :=
  result_not_implemented "[mkChar] TODO".
(* TODO. See main/envir.c. It creates a character vector from a string. *)

(* TODO: to bew sorted. *)
Definition install (runs : runs_type) (S : state) (name : string) : result SExpRec_pointer :=
  result_not_implemented "[install] TODO".
(* TODO. See main/names.c. It creates a new symbol object from this string. *)

(* TODO: to bew sorted. *)
Definition defineVar (runs : runs_type) (S : state) (symbol value rho : SExpRec_pointer) : result SExpRec_pointer :=
  result_not_implemented "[defineVar] TODO".
(* TODO. See main/envir.c. *)

(** * Initial State and Memory **)

(** An empty (and dummy) context **)
Definition empty_context := {|
     nextcontext := None ;
     callflag := Ctxt_TopLevel ;
     promargs := NULL ;
     callfun := NULL ;
     sysparent := NULL ;
     call := NULL ;
     cloenv := NULL ;
     conexit := NULL
  |}.

Definition empty_state := {|
    state_memory := empty_memory ;
    state_context := empty_context
  |}.

(** [InitBaseEnv], from main/envir.c **)
Definition InitBaseEnv runs S :=
  let%success R_EmptyEnv :=
    NewEnvironment runs S R_NilValue R_NilValue R_NilValue using S in
  let%success R_BaseEnv :=
    NewEnvironment runs S R_NilValue R_NilValue R_EmptyEnv using S in
  result_success S (R_EmptyEnv, R_BaseEnv).

(* FIXME: I think that we can remove this definition. *)
Definition init_context runs S :=
  let%success (R_EmptyEnv, R_BaseEnv) :=
    InitBaseEnv runs S using S in
  result_success S {|
      nextcontext := None ;
      callflag := Ctxt_TopLevel ;
      promargs := R_NilValue ;
      callfun := R_NilValue ;
      sysparent := R_BaseEnv ;
      call := R_NilValue ;
      cloenv := R_BaseEnv ;
      conexit := R_NilValue
    |}.

(** [InitGlobalEnv], from main/envir.c **)
Definition InitGlobalEnv runs S R_BaseSymbol R_BaseEnv :=
  let%success R_GlobalEnv :=
    NewEnvironment runs S R_NilValue R_NilValue R_BaseEnv using S in
  let%success R_BaseNamespace :=
    NewEnvironment runs S R_NilValue R_NilValue R_GlobalEnv using S in
  let%success BaseNamespaceEnvSym :=
    install runs S ".BaseNamespaceEnv" using S in
  read%sym BaseNamespaceEnvSym_, BaseNamespaceEnvSym_sym :=
    BaseNamespaceEnvSym using S in
  let BaseNamespaceEnvSym_sym := {|
      sym_pname := sym_pname BaseNamespaceEnvSym_sym ;
      sym_value := R_BaseNamespace ;
      sym_internal := sym_internal BaseNamespaceEnvSym_sym
    |} in
  let BaseNamespaceEnvSym_ := {|
      NonVector_SExpRec_header := NonVector_SExpRec_header BaseNamespaceEnvSym_ ;
      NonVector_SExpRec_data := BaseNamespaceEnvSym_sym
    |} in
  write%defined BaseNamespaceEnvSym := BaseNamespaceEnvSym_ using S in
  let%success R_BaseNamespaceName :=
    let%success str :=
      mkChar S "base" using S in
    ScalarString S str using S in
  let%success R_NamespaceRegistry :=
    NewEnvironment runs S R_NilValue R_NilValue R_NilValue using S in
  let%success _ :=
    defineVar runs S R_BaseSymbol R_BaseNamespace R_NamespaceRegistry using S in
  result_success S (R_GlobalEnv, R_BaseNamespace, R_BaseNamespaceName, R_NamespaceRegistry).


(* TODO: [SymbolSHortcuts] from main/names.c. We need a nice way to represent it. *)

Definition init_globals (runs : runs_type) : result Globals :=
  result_not_implemented "[init_globals]".

(* TODO: Add in the repport that [R_PreserveObject] is just a function telling the garbage
   collector that the object should not be freed. *)

(* I think that it would be easy to use tactics to check that [initial_allocations]
 * is indeed of the form [result_success S globals] or something like that. *)

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



(** * Closing the Loop **)

Fixpoint runs max_step : runs_type :=
  match max_step with
  | O => {|
      runs_do_while := fun _ S _ _ _ => result_bottom S ;
      runs_eval := fun S _ _ => result_bottom S
    |}
  | S max_step =>
    let wrap {A : Type} (f : runs_type -> A) : A :=
      f (runs max_step) in
    let wrap_dep {A} (f : forall B : Type, runs_type -> A B) B : A B :=
      f B (runs max_step) in {|
      runs_do_while := wrap_dep do_while ;
      runs_eval := wrap eval
    |}
  end.


(** * Proofs **)

(* TODO: move to another file, like Rinvariant.v. *)

(* TODO *)

(** It would be nice to prove that the read-eval-print-loop can not
 * return a [result_impossible]. **)

(** If runs returns a result, then adding fuel does not change it. **)

(** The property we want to eventually prove is that if [eval] returns
 * a result, then the C function eval does similarly. **)

