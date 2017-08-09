(** Rinit.
 * Initialises global variables. **)

Set Implicit Arguments.
Require Export Reval.


(** * Initialising Functions **)

Section Globals.

Variable globals : Globals.

Let R_NilValue := R_NilValue globals.

Let R_EmptyEnv := R_EmptyEnv globals.
Let R_BaseEnv := R_BaseEnv globals.
Let R_GlobalEnv := R_GlobalEnv globals.
Let R_BaseNamespace := R_BaseNamespace globals.
Let R_BaseNamespaceName := R_BaseNamespaceName globals.
Let R_BaseSymbol := R_BaseSymbol globals.
Let R_NamespaceRegistry := R_NamespaceRegistry globals.

Let R_TrueValue := R_TrueValue globals.
Let R_FalseValue := R_FalseValue globals.
Let R_LogicalNAValue := R_LogicalNAValue globals.

Let R_DotsSymbol := R_DotsSymbol globals.
Let R_UnboundValue := R_UnboundValue globals.
Let R_MissingArg := R_MissingArg globals.


(** A special part of [InitMemory] about [R_NilValue], from main/memory.c **)
Definition init_R_NilValue S :=
  let nil_obj := {|
      NonVector_SExpRec_header := make_SExpRecHeader (build_SxpInfo NilSxp) NULL ;
      NonVector_SExpRec_data := {|
          list_carval := NULL ;
          list_cdrval := NULL ;
          list_tagval := NULL
      |}
    |} in
  let (S, R_NilValue) := alloc_SExp S nil_obj in
  let nil_obj := {|
      NonVector_SExpRec_header := make_SExpRecHeader (build_SxpInfo NilSxp) R_NilValue ;
      NonVector_SExpRec_data := {|
          list_carval := R_NilValue ;
          list_cdrval := R_NilValue ;
          list_tagval := R_NilValue
      |}
    |} in
  write%defined R_NilValue := nil_obj using S in
  map%pointer R_NilValue with set_named_plural using S in
  result_success S R_NilValue.

(** [InitMemory], from main/memory.c **)
Definition InitMemory S :=
  let%success R_NilValue := init_R_NilValue S using S in
  let (S, R_TrueValue) := mkTrue globals S in
  let (S, R_FalseValue) := mkFalse globals S in
  let (S, R_LogicalNAValue) := alloc_vector_lgl globals S [NA_LOGICAL] in
  result_success S R_NilValue.

(** [InitBaseEnv], from main/envir.c **)
Definition InitBaseEnv runs S :=
  let%success R_EmptyEnv :=
    NewEnvironment runs globals S R_NilValue R_NilValue R_NilValue using S in
  let%success R_BaseEnv :=
    NewEnvironment runs globals S R_NilValue R_NilValue R_EmptyEnv using S in
  result_success S (R_EmptyEnv, R_BaseEnv).

(** [InitNames], from main/names.c **)
Definition InitNames S :=
  TODO.

(** [InitGlobalEnv], from main/envir.c **)
Definition InitGlobalEnv runs S :=
  let%success R_GlobalEnv :=
    NewEnvironment runs globals S R_NilValue R_NilValue R_BaseEnv using S in
  let%success R_BaseNamespace :=
    NewEnvironment runs globals S R_NilValue R_NilValue R_GlobalEnv using S in
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
    let (S, str) :=
      mkChar globals S "base" in
    ScalarString globals S str using S in
  let%success R_NamespaceRegistry :=
    NewEnvironment runs globals S R_NilValue R_NilValue R_NilValue using S in
  let%success _ :=
    defineVar runs S R_BaseSymbol R_BaseNamespace R_NamespaceRegistry using S in
  result_success S (R_GlobalEnv, R_BaseNamespace, R_BaseNamespaceName, R_NamespaceRegistry).

(** [InitOptions], from main/options.c **)
(* FIXME: Do we want to model it? *)
Definition InitOptions runs S :=
  TODO.

(** [InitTypeTables], from main/util.c **)
(* FIXME: Do we want to model it? *)
Definition InitTypeTables runs S :=
  TODO.

(** [InitS3DefaulTypes], from main/attrib.c **)
(* FIXME: Do we want to model it? *)
Definition InitS3DefaulTypes runs S :=
  TODO.

(** A special part of [setup_Rmainloop] about [R_Toplevel], from main/main.c **)
Definition init_R_Toplevel runs S :=
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

End Globals.

(** The functions above are all called in the C version of [setup_Rmainloop].
  * In C, each of these functions modify some global variables.
  * In Coq, we have to build intermediate [Globals] structures,
  * accounting for the various changes. **)
Definition setup_Rmainloop runs S : result Globals :=
  result_not_implemented "[setup_Rmainloop] TODO".


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


Definition globals : Globals.
(** We can now start the bootstrapping procedure to compute [globals]. **)
(* TODO *)
(* I think that it would be easy to use tactics to check that [setup_Rmainloop]
 * is indeed of the form [result_success S globals] or something like that. *)

Let R_NilValue := R_NilValue globals.

Let R_EmptyEnv := R_EmptyEnv globals.
Let R_BaseEnv := R_BaseEnv globals.
Let R_GlobalEnv := R_GlobalEnv globals.
Let R_BaseNamespace := R_BaseNamespace globals.
Let R_BaseNamespaceName := R_BaseNamespaceName globals.
Let R_BaseSymbol := R_BaseSymbol globals.
Let R_NamespaceRegistry := R_NamespaceRegistry globals.

Let R_TrueValue := R_TrueValue globals.
Let R_FalseValue := R_FalseValue globals.
Let R_LogicalNAValue := R_LogicalNAValue globals.

Let R_DotsSymbol := R_DotsSymbol globals.
Let R_UnboundValue := R_UnboundValue globals.
Let R_MissingArg := R_MissingArg globals.

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


(** * Installing Symbols **)

(* TODO: [SymbolSHortcuts] from main/names.c. We need a nice way to represent it. *)


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

