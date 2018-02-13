(** Path.
  Provides abstractions to reason about the heap. **)

Set Implicit Arguments.
Require Export Rcore.


Section Parametrised.

Variable runs : runs_type.

(** We do not want to reason about particular pointers.  Instead, we
  would like to remember the path taken to get this pointer.  This is
  what this abstraction tries to catch. **)

Inductive step_sym :=
  | Ssym_pname
  | Ssym_value
  | Ssym_internal
  .

Definition move_along_step_sym s :=
  match s with
  | Ssym_pname => sym_pname
  | Ssym_value => sym_value
  | Ssym_internal => sym_internal
  end.

Inductive step_list :=
  | Slist_carval
  | Slist_cdrval
  | Slist_tagval
  .

Definition move_along_step_list s :=
  match s with
  | Slist_carval => list_carval
  | Slist_cdrval => list_cdrval
  | Slist_tagval => list_tagval
  end.

Inductive step_env :=
  | Senv_frame
  | Senv_enclos
  (** | Senv_hashtab **)
  .

Definition move_along_step_env s :=
  match s with
  | Senv_frame => env_frame
  | Senv_enclos => env_enclos
  end.

Inductive step_clo :=
  | Sclo_formals
  | Sclo_body
  | Sclo_env
  .

Definition move_along_step_clo s :=
  match s with
  | Sclo_formals => clo_formals
  | Sclo_body => clo_body
  | Sclo_env => clo_env
  end.

Inductive step_prom :=
  | Sprom_value
  | Sprom_expr
  | Sprom_env
  .

Definition move_along_step_prom s :=
  match s with
  | Sprom_value => prom_value
  | Sprom_expr => prom_expr
  | Sprom_env => prom_env
  end.

Inductive path_step :=
  | Sattrib : path_step
  | SNonVectorSym : step_sym -> path_step
  | SNonVectorList : step_list -> path_step
  | SNonVectorEnv : step_env -> path_step
  | SNonVectorClo : step_clo -> path_step
  | SNonVectorProm : step_prom -> path_step
  | SVectorPointer : nat -> path_step
  .
Coercion SNonVectorSym : step_sym >-> path_step.
Coercion SNonVectorList : step_list >-> path_step.
Coercion SNonVectorEnv : step_env >-> path_step.
Coercion SNonVectorClo : step_clo >-> path_step.
Coercion SNonVectorProm : step_prom >-> path_step.

Definition move_along_path_step s (S : state) e :=
  LibOption.apply_on (read_SExp S e) (fun e_ =>
    let non_vector_case {T} (step : T -> SEXP) (proj : _ -> option T) :=
      LibOption.apply_on (get_NonVector e_) (fun e_ =>
        LibOption.map step (proj e_)) in
    match s with
    | Sattrib => Some (attrib e_)
    | SNonVectorSym s =>
      non_vector_case (move_along_step_sym s) get_symSxp
    | SNonVectorList s =>
      non_vector_case (move_along_step_list s) get_listSxp
    | SNonVectorEnv s =>
      non_vector_case (move_along_step_env s) get_envSxp
    | SNonVectorClo s =>
      non_vector_case (move_along_step_clo s) get_cloSxp
    | SNonVectorProm s =>
      non_vector_case (move_along_step_prom s) get_promSxp
    | SVectorPointer n =>
      LibOption.apply_on (get_VectorPointer e_) (fun e_ =>
        nth_option n (VecSxp_data e_))
    end).

Inductive context_step :=
  | Scontext_nextcontext
  | Scontext_jumptarget
  .

Definition move_along_context_step s c :=
  match s with
  | Scontext_nextcontext => context_nextcontext c
  | Scontext_jumptarget => context_jumptarget c
  end.

Inductive entry_context :=
  | Pstate_context
  | PExit_context
  .

Definition move_along_entry_context e S :=
  match e with
  | Pstate_context => Some (state_context S)
  | PExit_context => R_ExitContext S
  end.

Inductive context_path :=
  | context_path_entry : entry_context -> context_path
  | context_path_step : context_path -> context_step -> context_path
  .

Fixpoint move_along_context_path p S :=
  match p with
  | context_path_entry e =>
    move_along_entry_context e S
  | context_path_step p s =>
    LibOption.apply (move_along_context_step s) (move_along_context_path p S)
  end.

Inductive context_field :=
  | Scontext_promargs
  | Scontext_callfun
  | Scontext_sysparent
  | Scontext_call
  | Scontext_cloenv
  | Scontext_conexit
  | Scontext_returnValue
  .

Definition move_along_context_field f :=
  match f with
  | Scontext_promargs => context_promargs
  | Scontext_callfun => context_callfun
  | Scontext_sysparent => context_sysparent
  | Scontext_call => context_call
  | Scontext_cloenv => context_cloenv
  | Scontext_conexit => context_conexit
  | Scontext_returnValue => context_returnValue
  end.

Inductive entry_point :=
  | Econtext : context_path -> context_field -> entry_point
  | ESymbolTable : entry_point
  | EReturnedValue : entry_point
  | EasymSymbol : nat -> entry_point
  .

Definition move_along_entry_point e S :=
  match e with
  | Econtext p f =>
    option_map (move_along_context_field f) (move_along_context_path p S)
  | ESymbolTable => Some (R_SymbolTable S)
  | EReturnedValue => Some (R_ReturnedValue S)
  | EasymSymbol n => nth_option n (R_asymSymbol S)
  end.

Inductive path :=
  | Pentry : entry_point -> path
  | Pstep : path -> path_step -> path
  .

Fixpoint move_along_path p S :=
  match p with
  | Pentry e => move_along_entry_point e S
  | Pstep p s =>
    LibOption.apply (move_along_path_step s S) (move_along_path p S)
  end.

Definition path_from_list (el : entry_point * list path_step) :=
  let (e, l) := el in
  fold_left (fun s p => Pstep p s) (Pentry e) l.

End Parametrised.

