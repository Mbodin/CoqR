(** Globals.
  * Lists all global variables used in the C source code of R,
  * that are initialised, then never changed. **)


Require Export Rinternals Shared.


(** Global variables that are initialised once, then treated as
 * constants.  They are initialised in the file Rinit.v.
 * Each of these syntactic global variables are then associated
 * with the natural coercion (using the current context of type
 * [Globals], see below) to their value, of type [SExpRec_pointer].
 * See the beginning of the files Reval.v and Rinit.v for more
 * details. **)

Inductive GlobalVariable :=
  | NA_STRING
  | R_AsCharacterSymbol
  | R_BaseEnv
  | R_BaseNamespaceName
  | R_BaseNamespace
  | R_BaseSymbol
  | R_BlankScalarString
  | R_BlankString
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
  (** The following global variables are [static] variables of functions **)
  | mkPRIMSXP_primCache
  .

Definition all_GlobalVariables : list GlobalVariable.
  let rec aux t :=
    match t with
    | ?C = _ -> ?t =>
      let l := aux t in
      constr:(C :: l)
    | _ ?C -> ?t =>
      let l := aux t in
      constr:(C :: l)
    | _ => constr:(@nil GlobalVariable)
    end in
  let ind := constr:(GlobalVariable_ind (fun x => x = R_NilValue)) in
  let t := type of ind in
  let l := aux t in
  exact l.
Defined.

Local Instance GlobalVariable_Comparable : Comparable GlobalVariable.
  prove_comparable_trivial_inductive.
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


(** Each application of [GlobalsWith] adds a closure in the built context.
 * To avoid too many closures (which may lead to slowness or stack overflow),
 * we propose the following definition.
 * It computes once and for all the value of [g] for all possible global
 * variable, then waits for an argument, which is matched, looking for the
 * right precomputed value.
 * There is thus only one (used) closure at the end, and a fairly reasonnable
 * compiler should optimise out the [g] argument, unused after the precomputation.
 * The definition of [flatten_Globals] is however done using tactics, which are
 * quite slow (as they proof its correctness at the same time as defining it).
 * Its computation is thus disabled by default. **)

Definition flatten_Globals (g : Globals) : Globals.
  let rec build_let l t :=
    match t with
    | @nil _ =>
      let rec build_match l :=
        match l with
        | @nil _ => exact (GlobalVariable_rect (fun _ => SExpRec_pointer))
        | ?x :: ?l => exact (ltac:(build_match l) x)
        end in
      build_match l
    | ?C :: ?t =>
      let a := fresh "g_" C in
      exact (let a := g C in ltac:(build_let (a :: l) t))
    end in
  let l := eval unfold all_GlobalVariables in all_GlobalVariables in
  build_let (@nil SExpRec_pointer) l.
Defined.

Lemma flatten_Globals_correct : forall g C,
  g C = flatten_Globals g C.
Proof.
  introv. destruct C; reflexivity.
Qed.
