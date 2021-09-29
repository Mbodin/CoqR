(** Globals.
  Lists all global variables used in the C source code of R,
  that are initialised, then never changed. **)

(* Copyright © 2018 Martin Bodin

  This program is free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301 USA *)


From Lib Require Export Common.
From CoqR Require Export Rinternals InternalTypes.


(** * Initialised **)

(** Global variables that are initialised once, then treated as
  constants.  They are initialised in the file Rinit.v.
  Each of these syntactic global variables are then associated
  with the natural coercion (using the current context of type
  [Globals], see below) to their value, of type [SEXP].
  See the beginning of the files Rcore.v, Rinit.v or Rfeatures.v
  for more details. **)

Inductive GlobalVariable :=
  | NA_STRING
  | R_AsCharacterSymbol
  | R_AssignSym
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
  | R_DollarGetsSymbol
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
  | R_ReplaceFunsTable
  | R_RestartToken
  | R_RowNamesSymbol
  | R_SeedsSymbol
  | R_SortListSymbol
  | R_SourceSymbol
  | R_SpecSymbol
  | R_SrcfileSymbol
  | R_SrcrefSymbol
  | R_SubassignSym
  | R_Subassign2Sym
  | R_SubsetSym
  | R_Subset2Sym
  | R_TmpvalSymbol
  | R_TripleColonSymbol
  | R_TrueValue
  | R_TspSymbol
  | R_UnboundValue
  | R_UseNamesSymbol
  | R_valueSym
  | R_WholeSrcrefSymbol
  (** The following global variables are [static] variables of functions **)
  | mkPRIMSXP_primCache
  | do_attr_do_attr_formals
  | do_attrgets_do_attrgets_formals
  | do_substitute_do_substitute_formals
  | do_usemethod_do_usemethod_formals
  .

Definition all_GlobalVariables : list GlobalVariable.
Proof. list_all_constructors. Defined.

Local Instance GlobalVariable_Comparable : Comparable GlobalVariable.
Proof. prove_comparable_trivial_inductive_faster. Defined.

Definition Global_mapping : Type := GlobalVariable -> SEXP.

Record Globals := make_Globals {
    global_mapping :> Global_mapping ;
    global_Type2Table : ArrayList.array Type2Table_type
  }.

Definition read_globals (globals : Globals) : GlobalVariable -> SEXP :=
  globals : Global_mapping.

Definition Globals_with_mapping (g : Globals) m :=
  make_Globals m (global_Type2Table g).

Definition Globals_with_Type2Table (g : Globals) t :=
  make_Globals (global_mapping g) t.

Definition empty_global_mapping : Global_mapping :=
  fun _ => NULL.

Definition empty_Globals : Globals :=
  make_Globals empty_global_mapping \{}.

Definition Global_mapping_with (g : Global_mapping) (C : GlobalVariable) (p : SEXP) : Global_mapping :=
  fun C' =>
    ifb C = C' then p
    else g C'.

Definition GlobalsWith (g : Globals) (C : GlobalVariable) (p : SEXP) : Globals :=
  Globals_with_mapping g (Global_mapping_with g C p).


Declare Scope globals_scope.
Delimit Scope globals_scope with globals.
Open Scope globals.

Notation "'{{' g 'with' C ':=' p '}}'" :=
  (GlobalsWith g C p) : globals_scope.

Definition GlobalsWith_list :=
  fold_left (fun C_p g => GlobalsWith g (fst C_p) (snd C_p)).

Notation "'{{' g 'with' L '}}'" :=
  (GlobalsWith_list g L) : globals_scope.


(** Each application of [GlobalsWith] adds a closure in the built context.
  To avoid too many closures (which may lead to slowness or stack overflow),
  we propose the following definition.
  It computes once and for all the value of [g] for all possible global
  variable, then waits for an argument, which is matched, looking for the
  right precomputed value.
  There is thus only one (used) closure at the end, and a fairly reasonnable
  compiler should optimise out the [g] argument, unused after the precomputation.
  The definition of [flatten_Globals] is however done using tactics, which are
  quite slow (as they proof its correctness at the same time as defining it).
  Its computation is thus disabled by default. **)

Definition flatten_Global_mapping (g : Global_mapping) : Global_mapping.
Proof.
  let rec build_let l t :=
    match t with
    | @nil _ =>
      let rec build_match l :=
        match l with
        | @nil _ => exact (GlobalVariable_rect (fun _ => SEXP))
        | ?x :: ?l => exact (ltac:(build_match l) x)
        end in
      build_match l
    | ?C :: ?t =>
      let a := fresh "g_" C in
      exact (let a := g C in ltac:(build_let (a :: l) t))
    end in
  let l := eval unfold all_GlobalVariables in all_GlobalVariables in
  build_let (@nil SEXP) l.
Defined.

Lemma flatten_Global_mapping_correct : forall g C,
  g C = flatten_Global_mapping g C.
Proof. introv. destruct C; reflexivity. Qed.

Definition flatten_Globals (g : Globals) : Globals :=
  Globals_with_mapping g (flatten_Global_mapping g).


(** * Constants **)

(** We now list constant global variables. **)

(* We may want to make [INT_MIN] and [INT_MAX] a parameter of the formalisation,
  as it depends on the C compiler options. *)
Definition INT_MIN : int := - 2 ^ 31.
Definition INT_MAX : int := 2 ^ 31 - 1.

Definition R_INT_MAX := INT_MAX.
Definition R_INT_MIN := INT_MIN.

Definition R_NaInt := INT_MIN.
Definition NA_INTEGER := R_NaInt.
Definition NA_LOGICAL := R_NaInt.
Definition R_PosInf : double := Double.posInf.
Definition R_NegInf : double := Double.negInf.
Definition R_NaN : double := Double.NaN.
Definition R_NaReal : double := Double.NaN1954.
Definition NA_REAL : double := R_NaReal.

Definition R_NaString := NA_STRING.

Definition R_XLEN_T_MAX : int := Zpos 4503599627370496.

Definition PLUSOP := 1.
Definition MINUSOP := 2.
Definition TIMESOP := 3.
Definition DIVOP := 4.
Definition POWOP := 5.
Definition MODOP := 6.
Definition IDIVOP := 7.

Definition EQOP := 1.
Definition NEOP := 2.
Definition LTOP := 3.
Definition LEOP := 4.
Definition GEOP := 5.
Definition GTOP := 6.

