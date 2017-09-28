(** Globals.
  * Lists all global variables used in the C source code of R,
  * that are initialised, then never changed. **)


Require Export RinternalsAux.


(** Global variables that are initialised once, then treated as
 * constants.  They are initialised in the file Rinit.v.
 * Each of these syntactic global variables are then associated
 * with the natural coercion (using the current context of type
 * [Globals], see below) to their value, of type [SExpRec_pointer].
 * See the beginning of the files Reval.v and Rinit.v for more
 * details. **)

(** To ease compilation time (in particular the proof of comparability
 * below), this definition has been arbitrarily splitted into arbitrary
 * subtypes. **)

Inductive GlobalVariables_1 :=
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
  .

Inductive GlobalVariables_2 :=
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
  .

Inductive GlobalVariables_3 :=
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

Inductive StaticVariables :=
  | mkPRIMSXP_primCache
  (* TODO: Check whether the following static variables are
   * really initialised then never changed. *)
  | do_onexit_do_onexit_formals
  | do_attr_do_attr_formals
  .

Inductive GlobalVariable :=
  | GlobalVariable_1 : GlobalVariables_1 -> GlobalVariable
  | GlobalVariable_2 : GlobalVariables_2 -> GlobalVariable
  | GlobalVariable_3 : GlobalVariables_3 -> GlobalVariable
  | StaticVariable : StaticVariables -> GlobalVariable
  .
Coercion GlobalVariable_1 : GlobalVariables_1 >-> GlobalVariable.
Coercion GlobalVariable_2 : GlobalVariables_2 >-> GlobalVariable.
Coercion GlobalVariable_3 : GlobalVariables_3 >-> GlobalVariable.
Coercion StaticVariable : StaticVariables >-> GlobalVariable.

(** It is important for the following type class to only be local,
 * to avoid having a code of the form [ifb C1 = C2 then], where [C1]
 * and [C2] are two global variables, to be interpreted as the
 * syntactic equality where it should be seen as a semantic equality,
 * throught the context coercion. **)

Local Instance GlobalVariables_1_Comparable : Comparable GlobalVariables_1.
  prove_comparable_simple_inductive.
Defined.

Local Instance GlobalVariables_2_Comparable : Comparable GlobalVariables_2.
  prove_comparable_simple_inductive.
Defined.

Local Instance GlobalVariables_3_Comparable : Comparable GlobalVariables_3.
  prove_comparable_simple_inductive.
Defined.

Local Instance StaticVariables_Comparable : Comparable StaticVariables.
  prove_comparable_simple_inductive.
Defined.

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

Ltac define_flatten_function g :=
  match goal with
  | |- ?T -> SExpRec_pointer =>
    refine (proj1_sig (_ : { g' | forall C, g C = g' C }));
    let arg := fresh "arg" in
    refine (exist _ (let args := _ in fun C : T =>
                     ltac:(destruct C;
                           repeat (exact arg
                               || refine (let (arg, args) := args : _ * _ in _)))) _);
    let C := fresh "C" in
    intro C; destruct C; [ > .. |
     let rec aux :=
       match goal with |- ?g = let (arg, args) := ?y in _ =>
         let E := fresh "E" in
         asserts E: (y = (g, tt)) || (
           let ya := fresh "arg" in let yb := fresh "args" in
           match type of y with (?A * ?B)%type => evar (ya : A); evar (yb : B) end;
           asserts E: (y = (ya, yb)); [| unfolds yb; try rewrite E; (reflexivity || aux) ]) end
     in simpl; aux; reflexivity ]; simpl; reflexivity
  end.

Definition flatten_Globals_1 (g : GlobalVariables_1 -> SExpRec_pointer) :
    GlobalVariables_1 -> SExpRec_pointer.
  define_flatten_function g.
Defined.

Definition flatten_Globals_2 (g : GlobalVariables_2 -> SExpRec_pointer) :
    GlobalVariables_2 -> SExpRec_pointer.
  define_flatten_function g.
Defined.

Definition flatten_Globals_3 (g : GlobalVariables_3 -> SExpRec_pointer) :
    GlobalVariables_3 -> SExpRec_pointer.
  define_flatten_function g.
Defined.

Definition flatten_Statics (g : StaticVariables -> SExpRec_pointer) :
    StaticVariables -> SExpRec_pointer.
  define_flatten_function g.
Defined.

Definition flatten_Globals (g : Globals) : Globals :=
  let f1 := flatten_Globals_1 g in
  let f2 := flatten_Globals_2 g in
  let f3 := flatten_Globals_3 g in
  let s := flatten_Statics g in
  fun x =>
    match x with
    | GlobalVariable_1 x => f1 x
    | GlobalVariable_2 x => f2 x
    | GlobalVariable_3 x => f3 x
    | StaticVariable x => s x
    end.

Lemma flatten_Globals_correct : forall g C,
  g C = flatten_Globals g C.
Proof.
  introv. destruct C; simpl; unfolds;
    match goal with |- context [ proj1_sig ?s ] => sets_eq si: s end;
    apply (proj2_sig si).
Qed.


