(** Globals.
  * Lists all global variables used in the C source code of R,
  * that are initialised, then never changed. **)


Require Export RinternalsAux.


(** Global variables that are initialised once, then treated as
 * constants.  They are initialised in the file Rinit.v. **)
Inductive GlobalVariable :=
  | R_AsCharacterSymbol
  | R_BaseEnv
  | R_BaseNamespaceName
  | R_BaseNamespace
  | R_BaseSymbol
  | R_BraceSymbol
  | R_Bracket2Symbol
  | R_BracketSymbol
  | R_ClassSymbol
  | R_ColonSymbol
  | R_CommentSymbol
  | R_ConnIdSymbol
  | R_DevicesSymbol
  | R_DeviceSymbol
  | R_DimNamesSymbol
  | R_DimSymbol
  | R_DollarSymbol
  | R_dot_Class
  | R_dot_defined
  | R_DotEnvSymbol
  | R_dot_GenericCallEnv
  | R_dot_GenericDefEnv
  | R_dot_Generic
  | R_dot_Group
  | R_dot_Method
  | R_dot_Methods
  | R_dot_packageName
  | R_DotsSymbol
  | R_dot_target
  | R_DoubleColonSymbol
  | R_DropSymbol
  | R_EmptyEnv
  | R_ExactSymbol
  | R_FalseValue
  | R_GlobalEnv
  | R_LastvalueSymbol
  | R_LevelsSymbol
  | R_LogicalNAValue
  | R_MethodsNamespace
  | R_MissingArg
  | R_ModeSymbol
  | R_NamespaceEnvSymbol
  | R_NamespaceRegistry
  | R_NamespaceSymbol
  | R_NamesSymbol
  | R_NameSymbol 
  | R_NaRmSymbol
  | R_NilValue
  | R_PackageSymbol
  | R_PreviousSymbol
  | R_QuoteSymbol
  | R_RecursiveSymbol
  | R_RowNamesSymbol
  | R_SeedsSymbol
  | R_SortListSymbol
  | R_SourceSymbol
  | R_SpecSymbol
  | R_SrcfileSymbol
  | R_SrcrefSymbol
  | R_TmpvalSymbol
  | R_TripleColonSymbol
  | R_TrueValue
  | R_TspSymbol
  | R_UnboundValue
  | R_UseNamesSymbol
  | R_WholeSrcrefSymbol
  .

Local Instance GlobalVariable_Comparable : Comparable GlobalVariable.
  prove_comparable_simple_inductive.
Defined.

Definition Globals : Type := GlobalVariable -> SExpRec_pointer.

Definition empty_globals : Globals :=
  fun _ => NULL.

Definition GlobalsWith (g : Globals) (C : GlobalVariable) (p : SExpRec_pointer) : Globals :=
  fun C' =>
    ifb C = C' then p
    else g C'.

Delimit Scope globals_scope with globals.

Open Scope globals.

Notation "'{{' g 'with' C ':=' p '}}'" :=
  (GlobalsWith g C p) : globals_scope.

Definition GlobalsWith_list :=
  fold_left (fun C_p g => GlobalsWith g (fst C_p) (snd C_p)).

Notation "'{{' g 'with' L '}}'" :=
  (GlobalsWith_list g L) : globals_scope.


(** To avoid too many closures. **)
Definition flatten_Globals (g : Globals) : Globals.
  refine (proj1_sig (_ : { g' | forall C, g C = g' C })).
  refine (exist _ (let args : _ := _ in fun C : GlobalVariable =>
                   ltac:(destruct C; do 100 (exact (fst args) || refine (let args := snd args in _)))) _).
  intro C. destruct C; try reflexivity.
  refine (exist _ (let args : _ := _ in fun C : GlobalVariable =>
                   ltac:(destruct C; repeat (exact (fst args) || refine (let args := snd args in _)))) _).
  intro C. destruct C; repeat (exact (fst args) || refine (let args := snd args in _)).
Defined.

