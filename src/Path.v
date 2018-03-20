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

Global Instance step_sym_Comparable : Comparable step_sym.
  prove_comparable_trivial_inductive_faster.
Defined.

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

Global Instance step_list_Comparable : Comparable step_list.
  prove_comparable_trivial_inductive_faster.
Defined.

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

Global Instance step_env_Comparable : Comparable step_env.
  prove_comparable_trivial_inductive_faster.
Defined.

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

Global Instance step_clo_Comparable : Comparable step_clo.
  prove_comparable_trivial_inductive_faster.
Defined.

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

Global Instance step_prom_Comparable : Comparable step_prom.
  prove_comparable_trivial_inductive_faster.
Defined.

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

Global Instance path_step_Comparable : Comparable path_step.
  prove_comparable_simple_inductive.
Defined.

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

Lemma move_along_path_step_NULL : forall s S,
  move_along_path_step s S NULL = None.
Proof. introv. unfolds. rewrite~ read_SExp_NULL. Qed.

Definition move_along_path_from p (S : state) e :=
  fold_left (fun s => LibOption.apply (move_along_path_step s S)) (Some e) p.

Lemma move_along_path_from_NULL : forall p S,
  p <> nil ->
  move_along_path_from p S NULL = None.
Proof.
  introv D. destruct p as [|s p]; tryfalse.
  unfolds. simpl. rewrite move_along_path_step_NULL. clear D s. induction p.
  - reflexivity.
  - rew_list. simpl. apply~ IHp.
Qed.

Lemma move_along_path_from_nil : forall S e,
  move_along_path_from nil S e = Some e.
Proof. introv. reflexivity. Qed.

Lemma move_along_path_from_cons : forall S s p e1 e2 e3,
  move_along_path_step s S e1 = Some e2 ->
  move_along_path_from p S e2 = Some e3 ->
  move_along_path_from (s :: p) S e1 = Some e3.
Proof. introv E1 E2. unfolds. rew_list. simpl. rewrite* E1. Qed.

Lemma move_along_path_from_last : forall S s p e1 e2 e3,
  move_along_path_from p S e1 = Some e2 ->
  move_along_path_step s S e2 = Some e3 ->
  move_along_path_from (p & s) S e1 = Some e3.
Proof. introv E1 E2. unfolds. rew_list. unfolds in E1. rewrite* E1. Qed.

Lemma move_along_path_from_cons_inv : forall S s p e1 e3,
  move_along_path_from (s :: p) S e1 = Some e3 ->
  exists e2,
    move_along_path_step s S e1 = Some e2
    /\ move_along_path_from p S e2 = Some e3.
Proof.
  introv E. unfolds in E. rew_list in E. simpl in E. destruct* move_along_path_step.
  false. induction p.
  - inverts E.
  - rew_list in E. simpl in E. applys~ IHp E.
Qed.

Lemma move_along_path_from_last_inv : forall S s p e1 e3,
  move_along_path_from (p & s) S e1 = Some e3 ->
  exists e2,
    move_along_path_from p S e1 = Some e2
    /\ move_along_path_step s S e2 = Some e3.
Proof.
  introv E. unfolds in E. rew_list in E. destruct @fold_left eqn: E'; tryfalse~.
  simpl in E. eexists. splits*.
Qed.

Inductive context_step :=
  | Scontext_nextcontext
  | Scontext_jumptarget
  .

Global Instance context_step_Comparable : Comparable context_step.
  prove_comparable_trivial_inductive_faster.
Defined.

Definition move_along_context_step s c :=
  match s with
  | Scontext_nextcontext => context_nextcontext c
  | Scontext_jumptarget => context_jumptarget c
  end.

Inductive entry_context :=
  | Pstate_context
  | PExit_context
  .

Global Instance entry_context_Comparable : Comparable entry_context.
  prove_comparable_trivial_inductive_faster.
Defined.

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

Lemma move_along_context_path_state_with_memory : forall S p m,
  move_along_context_path p (state_with_memory S m) = move_along_context_path p S.
Proof. introv. induction~ p. simpl. rewrite~ IHp. Qed.

Inductive context_field :=
  | Scontext_promargs
  | Scontext_callfun
  | Scontext_sysparent
  | Scontext_call
  | Scontext_cloenv
  | Scontext_conexit
  | Scontext_returnValue
  .

Global Instance context_field_Comparable : Comparable context_field.
  prove_comparable_trivial_inductive_faster.
Defined.

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

Lemma move_along_entry_point_state_with_memory : forall S e m,
  move_along_entry_point e (state_with_memory S m) = move_along_entry_point e S.
Proof. introv. destruct~ e. simpl. rewrite~ move_along_context_path_state_with_memory. Qed.

Lemma move_along_entry_point_alloc_SExp : forall S S' e p p_,
  alloc_SExp S p_ = (S', p) ->
  move_along_entry_point e S' = move_along_entry_point e S.
Proof. introv E. inverts E. apply~ move_along_entry_point_state_with_memory. Qed.

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

Inductive suffix : path -> list path_step -> Prop :=
  | suffix_nil : forall p, suffix p nil
  | suffix_cons : forall p s l,
    suffix p l ->
    suffix (Pstep p s) (l & s)
  .

Definition last p s :=
  suffix p [s].

End Parametrised.

