(** Reval.
 * Describes how R evaluates expressions.
 * The content of this file is the Coq equivalent of functions from R source code.
 * Note that only relevant definitions are translated here. Some are just
 * reinterpreted in Coq without following the original algorithm of the
 * C source. See report for more details. **)

Set Implicit Arguments.
Require Import Ascii.
Require Export Monads Globals.

(** * Global structure of the interpreter **)

(** A structure to deal with infinite execution (which is not allowed in Coq). Inspired from JSCert. **)
Record runs_type : Type := runs_type_intro {
    runs_do_while : forall A, state -> A -> (state -> A -> result bool) -> (state -> A -> result A) -> result A ;
    runs_eval : state -> SExpRec_pointer -> SExpRec_pointer -> result SExpRec_pointer ;
    runs_inherits : state -> SExpRec_pointer -> string -> result bool ;
    runs_getAttrib : state -> SExpRec_pointer -> SExpRec_pointer -> result SExpRec_pointer
  }.


Section ParameterisedGlobals.

(** * Global Definitions **)

Definition INT_MIN : int := - 2 ^ 31. (* We may want to make this a parameter. *)

Definition R_NaInt := INT_MIN.
Definition R_PosInf := 0 : int (* TODO *).
Definition R_NaN := 0 : int (* TODO *).
Definition NA_INTEGER := R_NaInt.
Definition NA_LOGICAL := R_NaInt.
Definition NA_REAL := R_NaInt (* TODO: CHECK *).


Variable globals : Globals.

Let read_globals : GlobalVariable -> SExpRec_pointer := globals.

Local Coercion read_globals : GlobalVariable >-> SExpRec_pointer.

Section ParameterisedRuns.

Variable runs : runs_type.


(** * Interpreter functions **)

(** We recall from RinternalsAux.v that we write [p_] for the object
 * referenced by the pointer [p], and [p_f] for the field [f] or it **)

(** ** Frequent Patterns **)

(** The functions presented here are not from R source code, but
 * represent frequent programming pattern in its source code. **)

(** A basic C-like loop **)
Definition do_while A S (a : A) expr stat : result A :=
  let%success b := expr S a using S in
  if b : bool then
    let%success a := stat S a using S in
    runs_do_while runs S a expr stat
  else
    result_success S a.

Notation "'do%let' a ':=' e 'while' expr 'do' stat 'using' S" :=
  (do_while S e (fun S a => expr) (fun S a => stat))
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' 'while' expr 'do' stat 'using' S" :=
  (do%let _ := tt while expr do stat using S)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ')' ':=' a 'while' expr 'do' stat 'using' S" :=
  (do%let x := a
   while let (a1, a2) := x in expr
   do let (a1, a2) := x in stat
   using S)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ')' ':=' a 'while' expr 'do' stat 'using' S" :=
  (do%let x := a
   while let '(a1, a2, a3) := x in expr
   do let '(a1, a2, a3) := x in stat
   using S)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' a 'while' expr 'do' stat 'using' S" :=
  (do%let x := a
   while let '(a1, a2, a3, a4) := x in expr
   do let '(a1, a2, a3, a4) := x in stat
   using S)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' a 'while' expr 'do' stat 'using' S" :=
  (do%let x := a
   while let '(a1, a2, a3, a4, a5) := x in expr
   do let '(a1, a2, a3, a4, a5) := x in stat
   using S)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' 'while' expr 'do' stat 'using' S 'in' cont" :=
  (let%success _ :=
     do%let while expr
     do stat
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' a ':=' e 'while' expr 'do' stat 'using' S 'in' cont" :=
  (let%success a :=
     do%let a := e
     while expr
     do stat
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ')' ':=' a 'while' expr 'do' stat 'using' S 'in' cont" :=
  (let%success (a1, a2) :=
     do%let (a1, a2) := a
     while expr
     do stat
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ')' ':=' a 'while' expr 'do' stat 'using' S 'in' cont" :=
  (let%success (a1, a2, a3) :=
     do%let (a1, a2, a3) := a
     while expr
     do stat
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' a 'while' expr 'do' stat 'using' S 'in' cont" :=
  (let%success (a1, a2, a3, a4) :=
     do%let (a1, a2, a3, a4) := a
     while expr
     do stat
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' a 'while' expr 'do' stat 'using' S 'in' cont" :=
  (let%success (a1, a2, a3, a4, a5) :=
     do%let (a1, a2, a3, a4, a5) := a
     while expr
     do stat
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.



(** Looping through a list is a frequent pattern in R source code.
 * [fold_left_listSxp_gen] corresponds to the C code
 * [for (i = l, v = a; i != R_NilValue; i = CDR (i)) v = iterate ( *i, v); v]. **)
Definition fold_left_listSxp_gen A S (l : SExpRec_pointer) (a : A)
    (iterate : state -> A -> SExpRec_pointer -> SExpRec -> ListSxp_struct -> result A) : result A :=
  do%success (l, a) := (l, a)
  while result_success S (decide (l <> R_NilValue))
  do
    read%list l_, l_list := l using S in
    let%success a := iterate S a l l_ l_list using S in
    result_success S (list_cdrval l_list, a)
  using S in
  result_success S a.

Notation "'fold%let' a ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S" :=
  (fold_left_listSxp_gen S le e (fun S a l l_ l_list => iterate))
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S" :=
  (fold%let _ := tt along le as l, l_, l_list
   do iterate
   using S)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' '(' a1 ',' a2 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S" :=
  (fold%let x := e along le as l, l_, l_list
   do let (a1, a2) := x in iterate
   using S)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' '(' a1 ',' a2 ',' a3 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S" :=
  (fold%let x := e along le as l, l_, l_list
   do let '(a1, a2, a3) := x in iterate
   using S)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S" :=
  (fold%let x := e along le as l, l_, l_list
   do let '(a1, a2, a3, a4) := x in iterate
   using S)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S" :=
  (fold%let x := e along le as l, l_, l_list
   do let '(a1, a2, a3, a4, a5) := x in iterate
   using S)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S 'in' cont" :=
  (let%success _ :=
     fold%let along le as l, l_, l_list
     do iterate
     using S using S in
   cont)
    (at level 50, left associativity) : monad_scope.

Notation "'fold%success' a ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S 'in' cont" :=
  (let%success a :=
     fold%let a := e along le as l, l_, l_list
     do iterate
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' '(' a1 ',' a2 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S 'in' cont" :=
  (let%success (a1, a2) :=
     fold%let (a1, a2) := e along le as l, l_, l_list
     do iterate
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' '(' a1 ',' a2 ',' a3 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S 'in' cont" :=
  (let%success (a1, a2, a3) :=
     fold%let (a1, a2, a3) := e along le as l, l_, l_list
     do iterate
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S 'in' cont" :=
  (let%success (a1, a2, a3, a4) :=
     fold%let (a1, a2, a3, a4) := e along le as l, l_, l_list
     do iterate
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S 'in' cont" :=
  (let%success (a1, a2, a3, a4, a5) :=
     fold%let (a1, a2, a3, a4, a5) := e along le as l, l_, l_list
     do iterate
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.


(* [fold_left_listSxp] corresponds to the C code
 * [for (i = l, v = a; i != R_NilValue; i = CDR (i)) v = iterate (CAR (i), TAG (i), v); v]. **)
Definition fold_left_listSxp A S (l : SExpRec_pointer) (a : A)
    (iterate : state -> A -> SExpRec_pointer -> SExpRec_pointer -> result A) : result A :=
  fold%let a := a along l as _, _, l_list
  do iterate S a (list_carval l_list) (list_tagval l_list) using S.

Notation "'fold%let' a ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' S" :=
  (fold_left_listSxp S le e (fun S a l_car l_tag => iterate))
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' '(' a1 ',' a2 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' S" :=
  (fold%let x := e along le as l_car, l_tag
   do let (a1, a2) := x in iterate
   using S)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' '(' a1 ',' a2 ',' a3 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' S" :=
  (fold%let x := e along le as l_car, l_tag
   do let '(a1, a2, a3) := x in iterate
   using S)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' S" :=
  (fold%let x := e along le as l_car, l_tag
   do let '(a1, a2, a3, a4) := x in iterate
   using S)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' S" :=
  (fold%let x := e along le as l_car, l_tag
   do let '(a1, a2, a3, a4, a5) := x in iterate
   using S)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' S 'in' cont" :=
  (let%success _ :=
     fold%let _ := tt along le as l_car, l_tag
     do iterate
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' a ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' S 'in' cont" :=
  (let%success a :=
     fold%let a := e along le as l_car, l_tag
     do iterate
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' '(' a1 ',' a2 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' S 'in' cont" :=
  (let%success (a1, a2) :=
     fold%let (a1, a2) := e along le as l_car, l_tag
     do iterate
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' '(' a1 ',' a2 ',' a3 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' S 'in' cont" :=
  (let%success (a1, a2, a3) :=
     fold%let (a1, a2, a3) := e along le as l_car, l_tag
     do iterate
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' S 'in' cont" :=
  (let%success (a1, a2, a3, a4) :=
     fold%let (a1, a2, a3, a4) := e along le as l_car, l_tag
     do iterate
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' S 'in' cont" :=
  (let%success (a1, a2, a3, a4, a5) :=
     fold%let (a1, a2, a3, a4, a5) := e along le as l_car, l_tag
     do iterate
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.


(** ** Rinternals.h **)

(** The function names of this section corresponds to the macro names
 * in the file include/Rinternals.h. **)

Definition PRINTNAME S x :=
  read%defined x_ := x using S in
  let%sym x_, x_sym := x_ using S in
  result_success S (sym_pname x_sym).

Definition CHAR S x :=
  read%VectorChar x_vector := x using S in
  result_success S (list_to_string x_vector).

Definition SET_MISSING S e (m : nat) I :=
  map%gp e with @NBits.write_nbits 16 4 0 (NBits.nat_to_nbits m I) ltac:(NBits.nbits_ok) using S in
  result_success S tt.
Arguments SET_MISSING : clear implicits.

Definition INCREMENT_NAMED S x :=
  read%defined x_ := x using S in
  match named x_ with
  | named_temporary =>
    map%pointer x with set_named_unique using S in
    result_success S tt
  | named_unique =>
    map%pointer x with set_named_plural using S in
    result_success S tt
  | named_plural =>
    result_success S tt
  end.


(** ** memory.c **)

(** The function names of this section corresponds to the function names
 * in the file main/memory.c. **)

Definition CONS S (car cdr : SExpRec_pointer) : state * SExpRec_pointer :=
  let e_ := make_SExpRec_list R_NilValue car cdr R_NilValue in
  alloc_SExp S e_.

Definition allocList S (n : nat) : state * SExpRec_pointer :=
  let fix aux S n p :=
    match n with
    | 0 => (S, p)
    | S n =>
      let (S, p) := aux S n p in
      CONS S R_NilValue p
    end
  in aux S n R_NilValue.

Definition STRING_ELT S (x : SExpRec_pointer) i : result SExpRec_pointer :=
  read%defined x_ := x using S in
  ifb type x_ <> StrSxp then
    result_error S "[STRING_ELT] Not a character vector."
  else
    let%Pointer r := x_ at i using S in
    result_success S r.

(** Note: there is a macro definition renaming [NewEnvironment] to
  * [Rf_NewEnvironment] in the file include/Defn.h. As a consequence,
  * the compiled C files references [Rf_NewEnvironment] and not
  * [NewEnvironment]. These two functions are exactly the same. **)
Definition NewEnvironment S (namelist valuelist rho : SExpRec_pointer) : result SExpRec_pointer :=
  let (S, newrho) := alloc_SExp S (make_SExpRec_env R_NilValue valuelist rho) in
  do%success (v, n) := (valuelist, namelist)
  while result_success S (decide (v <> R_NilValue /\ n <> R_NilValue)) do
    read%list v_, v_list := v using S in
    read%list n_, n_list := n using S in
    let v_list := set_tag_list (list_tagval n_list) v_list in
    let v_ := {|
        NonVector_SExpRec_header := v_ ;
        NonVector_SExpRec_data := v_list
      |} in
    write%defined v := v_ using S in
    result_success S (list_cdrval v_list, list_cdrval n_list) using S in
  result_success S newrho.

(** Similarly, there is a macro renaming [mkPROMISE] to [Rf_mkPROMISE]. **)
Definition mkPromise S (expr rho : SExpRec_pointer) : result SExpRec_pointer :=
  map%pointer expr with set_named_plural using S in
  let (S, s) := alloc_SExp S (make_SExpRec_prom R_NilValue R_UnboundValue expr rho) in
  result_success S s.


(** ** Rinlinedfuns.c **)

(** The function names of this section corresponds to the function names
 * in the file include/Rinlinedfuns.c. **)

(** The way the original functions [allocVector], [allocVector3], etc.
  * from R source code are defined are not compatible with the way the
  * memory of the C language has been formalised here. The functions
  * below are thus slightly different from their C counterparts.
  * The [repeat] function of Coq can be used to initialise their data. **)

Definition alloc_vector_char S v_data : state * SExpRec_pointer :=
  alloc_SExp S (make_SExpRec_char R_NilValue v_data).

Definition alloc_vector_lgl S v_data : state * SExpRec_pointer :=
  alloc_SExp S (make_SExpRec_lgl R_NilValue v_data).

Definition alloc_vector_int S v_data : state * SExpRec_pointer :=
  alloc_SExp S (make_SExpRec_int R_NilValue v_data).

Definition alloc_vector_real S v_data : state * SExpRec_pointer :=
  alloc_SExp S (make_SExpRec_real R_NilValue v_data).

Definition alloc_vector_cplx S v_data : state * SExpRec_pointer :=
  alloc_SExp S (make_SExpRec_cplx R_NilValue v_data).

(** The following allocators uses pointers. Note that the original
 * [allocVector] function initialises them to [R_NilValue] (and not
 * [NULL], for instance) by default. **)

Definition alloc_vector_str S v_data : state * SExpRec_pointer :=
  alloc_SExp S (make_SExpRec_str R_NilValue v_data).

Definition alloc_vector_vec S v_data : state * SExpRec_pointer :=
  alloc_SExp S (make_SExpRec_vec R_NilValue v_data).

Definition alloc_vector_expr S v_data : state * SExpRec_pointer :=
  alloc_SExp S (make_SExpRec_expr R_NilValue v_data).

Definition ScalarLogical x : SExpRec_pointer :=
  ifb x = NA_LOGICAL then
    R_LogicalNAValue
  else ifb x <> 0 then
    R_TrueValue
  else R_FalseValue.

Definition ScalarInteger S x : state * SExpRec_pointer :=
  alloc_vector_int S [x].

Definition ScalarReal S x : state * SExpRec_pointer :=
  alloc_vector_real S [x].

Definition ScalarComplex S x : state * SExpRec_pointer :=
  alloc_vector_cplx S [x].

Definition ScalarString S (x : SExpRec_pointer) : result SExpRec_pointer :=
  read%defined x_ := x using S in
  ifb type x_ <> CharSxp then
    result_error S "[ScalarString] The given argument is not of type ‘CharSxp’."
  else
    let (S, s) := alloc_vector_str S [x] in
    result_success S s.

(** Named [length] in the C source file. **)
Definition R_length S s :=
  read%defined s_ := s using S in
  match type s_ with
  | NilSxp => result_success S 0
  | LglSxp
  | IntSxp
  | RealSxp
  | CplxSxp
  | StrSxp
  | CharSxp
  | VecSxp
  | ExprSxp
  | RawSxp =>
    let%defined l := get_VecSxp_length s_ using S in
    result_success S l
  | ListSxp
  | LangSxp
  | DotSxp =>
    do%success (s, i) := (s, 0)
    while result_success S (decide (s <> NULL /\ s <> R_NilValue))
    do
      read%list s_, s_list := s using S in
      result_success S (list_cdrval s_list, 1 + i)
    using S in
    result_success S i
  | EnvSxp =>
    result_not_implemented "[R_length] Rf_envlength"
  | _ =>
    result_success S 1
  end.

Definition inherits S s name :=
  read%defined s_ := s using S in
  if obj s_ then
    let%success klass := runs_getAttrib runs S s R_ClassSymbol using S in
    read%VectorPointer klass_vector := klass using S in
    let%success b :=
      fold_left (fun str rb =>
        let%success b := rb using S in
        if b : bool then
          result_success S true
        else
          let%success str_ := CHAR S str using S in
          result_success S (decide (str_ = name)))
        (result_success S false) (VecSxp_data klass_vector) using S in
    result_success S b
  else
    result_success S false.

Definition isInteger S s :=
  read%defined s_ := s using S in
  let%success inh := inherits S s "factor" using S in
  result_success S (decide (type s_ = IntSxp /\ ~ inh)).


Definition lcons S car cdr :=
  let (S, e) := CONS S car cdr in
  map%pointer e with set_type LangSxp using S in
  result_success S e.

Definition list1 S s :=
  CONS S s R_NilValue.

Definition list2 S s t :=
  let (S, l) := list1 S t in
  CONS S s l.

Definition list3 S s t u :=
  let (S, l) := list2 S t u in
  CONS S s l.

Definition list4 S s t u v :=
  let (S, l) := list3 S t u v in
  CONS S s l.

Definition list5 S s t u v w :=
  let (S, l) := list4 S t u v w in
  CONS S s l.

Definition list6 S s t u v w x :=
  let (S, l) := list5 S t u v w x in
  CONS S s l.

Definition lang1 S s :=
  lcons S s R_NilValue.

Definition lang2 S s t :=
  let (S, l) := list1 S t in
  lcons S s l.

Definition lang3 S s t u :=
  let (S, l) := list2 S t u in
  lcons S s l.

Definition lang4 S s t u v :=
  let (S, l) := list3 S t u v in
  lcons S s l.

Definition lang5 S s t u v w :=
  let (S, l) := list4 S t u v w in
  lcons S s l.

Definition lang6 S s t u v w x :=
  let (S, l) := list5 S t u v w x in
  lcons S s l.


(** ** envir.c **)

(** The function names of this section corresponds to the function names
 * in the file main/envir.c. The most important functions of envir.c
 * are shown in a later section. **)

(** The function [mkChar] from the R source code performs a lot of things.
 * It deals with encoding, for embedded zero-characters, as well as avoid
 * allocated twice the same string, by looking through the already
 * allocated strings. We do none of the above. **)
(* FIXME: What is the difference between [intCHARSXP] and [CHARSXP]? *)
Definition mkChar S (str : string) : state * SExpRec_pointer :=
  (* TODO: Caching values using R_StringHash. *)
  alloc_vector_char S (string_to_list str).

Definition mkString S (str : string) : state * SExpRec_pointer :=
  let (S, c) := mkChar S str in
  alloc_vector_str S [c].


(** ** dstruct.c **)

(** The function names of this section corresponds to the function names
 * in the file main/dstruct.c. **)

Definition iSDDName S (name : SExpRec_pointer) :=
  let%success buf := CHAR S name using S in
  ifb substring 0 2 buf = ".."%string /\ String.length buf > 2 then
    let buf := substring 2 (String.length buf) buf in
    (* I am simplifying the C code here. *)
    result_success S (decide (Forall (fun c : Ascii.ascii =>
        Mem c (["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"])%char)
      (string_to_list buf)))
  else
  result_success S false.

Definition mkSYMSXP S (name value : SExpRec_pointer) :=
  let%success i := iSDDName S name using S in
  let (S, c) := alloc_SExp S (make_SExpRec_sym R_NilValue name value R_NilValue) in
  map%gp c with @NBits.write_nbit 16 0 ltac:(NBits.nbits_ok) i using S in
  result_success S c.


(** ** names.c **)

(** The function names of this section corresponds to the function names
 * in the file main/names.c. **)

Definition mkSymMarker S pname :=
  let (S, ans) := alloc_SExp S (make_SExpRec_sym R_NilValue pname NULL R_NilValue) in
  write%defined ans := make_SExpRec_sym R_NilValue pname ans R_NilValue using S in
  result_success S ans.

Definition install S name : result SExpRec_pointer :=
  (** As said in the description of [InitNames] in Rinit.v,
    * the hash table present in [R_SymbolTable] has not been
    * formalised as such.
    * Instead, it is represented as a single list, and not
    * as [HSIZE] different lists.
    * This approach is slower, but equivalent. **)
  fold%success ret := None along R_SymbolTable S as R_SymbolTable_car, _ do
    match ret with
    | Some v =>
      result_success S ret
    | None =>
      let%success str_sym := PRINTNAME S R_SymbolTable_car using S in
      let%success str_name_ := CHAR S str_sym using S in
      ifb name = str_name_ then
        result_success S (Some R_SymbolTable_car)
      else result_success S None
    end
    using S in
  match ret with
  | Some v => result_success S v
  | None =>
    ifb name = ""%string then
      result_error S "[install] Attempt to use zero-length variable name."
    else
      let (S, str) := mkChar S name in
      let%success sym := mkSYMSXP S str R_UnboundValue using S in
      let (S, SymbolTable) := CONS S sym (R_SymbolTable S) in
      let S := update_R_SymbolTable S SymbolTable in
      result_success S sym
  end.

(** We here choose to model [installChar] as its specifation
  * given by the associated comment in the C source file. **)
Definition installChar S charSXP :=
  let%success str := CHAR S charSXP using S in
  install S str.


(** ** sysutils.c **)

(** The function names of this section corresponds to the function names
 * in the file main/sysutils.c. **)

Definition installTrChar S x :=
  read%defined x_ := x using S in
  ifb type x_ <> CharSxp then
    result_error S "[installTrChar] Must be called on a [CharSxp]."
  else
    (** The original C program deals with encoding here. **)
    installChar S x.


(** ** gram.y **)

(** The function names of this section corresponds to the function names
 * in the file main/gram.y. **)

Definition mkTrue S :=
  alloc_vector_lgl S [1 : int].

Definition mkFalse S :=
  alloc_vector_lgl S [0 : int].

Definition mkNA S :=
  alloc_vector_lgl S [NA_LOGICAL : int].


Definition NewList S :=
  let (S, s) := CONS S R_NilValue R_NilValue in
  set%car s := s using S in
  result_success S s.

Definition GrowList S l s :=
  let (S, tmp) := CONS S s R_NilValue in
  read%list _, l_list := l using S in
  set%cdr list_carval l_list := tmp using S in
  set%car l := tmp using S in
  result_success S l.

Definition TagArg S arg tag :=
  read%defined tag_ := tag using S in
  let cont S := lang2 S arg tag in
  match type tag_ with
  | StrSxp =>
    let%success tag_ := STRING_ELT S tag 0 using S in
    let%success _ := installTrChar S tag_ using S in
    cont S
  | NilSxp
  | SymSxp =>
    cont S
  | _ =>
    result_error S "[TagArg] Incorrect tag type."
  end.

Definition FirstArg S s tag :=
  let%success tmp := NewList S using S in
  let%success tmp := GrowList S tmp s using S in
  read%list _, tmp_list := tmp using S in
  set%tag list_carval tmp_list := tag using S in
  result_success S tmp.

Definition NextArg S l s tag :=
  let%success l := GrowList S l s using S in
  read%list _, l_list := l using S in
  set%tag list_carval l_list := tag using S in
  result_success S l.

Definition CheckFormalArgs S formlist new :=
  fold%success along formlist as _, formlist_tag do
    ifb formlist_tag = new then
      result_error S "[CheckFormalArgs] Repeated formal argument."
    else result_success S tt using S in
  result_success S tt.


(** ** context.c **)

(** The function names of this section corresponds to the function names
 * in the file main/context.c. **)

Definition begincontext S flags syscall env sysp promargs callfun :=
  let cptr := {|
     nextcontext := Some (R_GlobalContext S) ;
     callflag := flags ;
     promargs := promargs ;
     callfun := callfun ;
     sysparent := sysp ;
     call := syscall ;
     cloenv := env ;
     conexit := R_NilValue
   |} in
  state_with_context S cptr.

Definition endcontext S cptr :=
  let%success _ :=
    ifb cloenv cptr <> R_NilValue /\ conexit cptr <> R_NilValue then
      let s := conexit cptr in
      let savecontext := R_ExitContext S in
      let S := state_with_exit_context S (Some cptr) in
      let S := state_with_context S (context_with_conexit cptr R_NilValue) in
      fold%success along s as _, _, s_list do
        let S := state_with_context S (context_with_conexit cptr (list_cdrval s_list)) in
        let%success _ :=
          runs_eval runs S (list_carval s_list) (cloenv cptr) using S in
        result_success S tt using S in
      let S := state_with_exit_context S savecontext in
      result_success S tt
    else result_success S tt using S in
  let%success _ :=
    ifb R_ExitContext S = Some cptr then
      let S := state_with_exit_context S None in
      result_success S tt
    else result_success S tt using S in
  let%defined c := nextcontext cptr using S in
  let S := state_with_context S c in
  result_success S tt.


(** ** match.c **)

(** The function names of this section corresponds to the function names
 * in the file main/match.c. **)

Definition psmatch s1 s2 exact :=
  if exact : bool then
    decide (s1 = s2)
  else
    String.prefix s1 s2.

Definition pmatch S (formal tag : SExpRec_pointer) exact : result bool :=
  let get_name str :=
    read%defined str_ := str using S in
    match type str_ with
    | SymSxp =>
      let%success str_name := PRINTNAME S str using S in
      CHAR S str_name
    | CharSxp =>
      CHAR S str
    | StrSxp =>
      let%success str_ := STRING_ELT S str 0 using S in
      result_not_implemented "[pmatch] translateChar(str_)" (* TODO *)
    | _ =>
      result_error S "[pmatch] invalid partial string match."
    end in
  let%success f := get_name formal using S in
  let%success t := get_name tag using S in
  result_success S (psmatch f t exact).

(** The function [matchArgs] matches the arguments supplied to a given
 * call with the formal, expected arguments.
 * This is more complex as it may seem as arguments in R can be named
 * (and thus provided in any order), or can be ‘...’.
 * The algorithm presented in this function is thus crucial to understand
 * the semantics of function calls in R.
 * It is furthermore rather complicated.
 * This is a large function and is divided into all its passes. **)

(** The function makes use of some bits from the general purpose pool
 * to mark some arguments as being used or missing. **)

Definition argused e_ :=
  NBits.nbits_to_nat (gp e_).

Definition set_argused (used : nat) I :=
  set_gp (NBits.nat_to_nbits used I).
Arguments set_argused : clear implicits.

Definition missing e_ :=
  NBits.sub_nbits 0 4 (gp e_) ltac:(NBits.nbits_ok).

Definition matchArgs_first S
    (formals actuals supplied : SExpRec_pointer) : result (list nat) :=
  fold%success (a, fargusedrev) := (actuals, nil) along formals as _, f_tag do
    let%success f_tag_sym_name := PRINTNAME S f_tag using S in
    let%success ftag_name := CHAR S f_tag_sym_name using S in
    let continuation S fargusedi :=
      read%list a_, a_list := a using S in
      result_success S (list_cdrval a_list, fargusedi :: fargusedrev) in
    ifb f_tag <> R_DotsSymbol /\ f_tag <> R_NilValue then
      if_success (fold%let fargusedi := 0 along supplied as b, b_, b_list do
        let b_tag := list_tagval b_list in
        let%success b_tag_sym_name := PRINTNAME S b_tag using S in
        let%success btag_name := CHAR S b_tag_sym_name using S in
        ifb b_tag <> R_NilValue /\ ftag_name = btag_name then
          ifb fargusedi = 2 then
            result_error S "[matchArgs_first] formal argument matched by multiple actual arguments."
          else ifb argused b_ = 2 then
            result_error S "[matchArgs_first] actual argument matches several formal arguments."
          else
            set%car a := list_carval b_list using S in
            let%success _ :=
              ifb list_carval b_list <> R_MissingArg then
                let%success _ := SET_MISSING S a 1 ltac:(NBits.nbits_ok) using S in
                result_success S tt
              else result_success S tt using S in
            map%pointer b with set_argused 2 ltac:(NBits.nbits_ok) using S in
            result_success S 2
        else
          result_success S fargusedi using S)
        continuation
    else continuation S 0 using S in
  result_success S (List.rev fargusedrev).

Definition matchArgs_second S
    (actuals formals supplied : SExpRec_pointer) fargused : result SExpRec_pointer :=
  fold%success (a, fargused, dots, seendots) :=
    (actuals, fargused, R_NilValue : SExpRec_pointer, false)
  along formals as _, f_tag do
      match fargused with
      | nil => result_impossible S "[matchArgs_second] fargused has an unexpected size."
      | fargusedi :: fargused =>
        let continuation S dots seendots :=
          read%list a_, a_list := a using S in
          result_success S (list_cdrval a_list, fargused, dots, seendots) in
        ifb fargusedi = 0 then
          ifb f_tag = R_DotsSymbol /\ ~ seendots then
            continuation S a true
          else
            fold%success fargusedi := fargusedi along supplied as b, b_, b_list do
              let b_tag := list_tagval b_list in
              ifb argused b_ <> 2 /\ b_tag <> R_NilValue then
                let%success pmatch := pmatch S f_tag b_tag seendots using S in
                if pmatch then
                  ifb argused b_ <> 0 then
                    result_error S "[matchArgs_second] actual argument matches several formal arguments."
                  else ifb fargusedi = 1 then
                    result_error S "[matchArgs_second] formal argument matched by multiple actual arguments."
                  else
                    (** Warning about partial arguments: should we ignore this part? **)
                    set%car a := list_carval b_list using S in
                    let%success _ :=
                      ifb list_carval b_list <> R_MissingArg then
                        let%success _ := SET_MISSING S a 0 ltac:(NBits.nbits_ok) using S in
                        result_success S tt
                      else result_success S tt using S in
                    map%pointer b with set_argused 1 ltac:(NBits.nbits_ok) using S in
                    result_success S 1
                else result_success S fargusedi
              else result_success S fargusedi using S in
            continuation S dots seendots
        else continuation S dots seendots
      end using S in
  result_success S dots.

Definition matchArgs_third S
    (formals actuals supplied : SExpRec_pointer) : result unit :=
  do%success (f, a, b, seendots) := (formals, actuals, supplied, false)
  while result_success S (decide (f <> R_NilValue /\ b <> R_NilValue /\ ~ seendots)) do
    read%list f_, f_list := f using S in
    read%list a_, a_list := a using S in
    ifb list_tagval f_list = R_DotsSymbol then
      result_success S (list_cdrval f_list, list_cdrval a_list, b, true)
    else ifb list_carval a_list <> R_MissingArg then
      result_success S (list_cdrval f_list, list_cdrval a_list, b, seendots)
    else
      read%list b_, b_list := b using S in
      ifb argused b_ <> 0 \/ list_tagval b_list <> R_NilValue then
        result_success S (f, a, list_cdrval b_list, seendots)
      else
        set%car a := list_carval b_list using S in
        let%success _ :=
          ifb list_carval b_list <> R_MissingArg then
            let%success _ := SET_MISSING S a 0 ltac:(NBits.nbits_ok) using S in
            result_success S tt
          else result_success S tt using S in
        result_success S (list_cdrval f_list, list_cdrval a_list, list_cdrval b_list, seendots)
  using S in
  result_success S tt.

Definition matchArgs_dots S
    (dots supplied : SExpRec_pointer) : result unit :=
  let%success _ := SET_MISSING S dots 0 ltac:(NBits.nbits_ok) using S in
  fold%success i := 0 along supplied as a, _ do
    read%defined a_ := a using S in
    ifb argused a_ = 0 then
      result_success S (1 + i)
    else
      result_success S i using S in
  ifb i = 0 then
    result_success S tt
  else
    let (S, a) := allocList S i in
    map%pointer a with set_type DotSxp using S in
    fold%success f := a along supplied as b, b_, b_list do
      ifb argused b_ <> 0 then
        result_success S f
      else
        set%car f := list_carval b_list using S in
        set%tag f := list_tagval b_list using S in
        read%list f_, f_list := f using S in
        result_success S (list_cdrval f_list) using S in
    set%car dots := a using S in
    result_success S tt.

Definition matchArgs_check S
    (supplied : SExpRec_pointer) : result unit :=
  fold%success acc := false along supplied as b, b_, b_list do
    result_success S (decide (acc \/ argused b_ <> 0)) using S in
  if acc : bool then
    result_error S "[matchArgs_check] Unused argument(s)."
  else
    result_success S tt.


Definition matchArgs S
    (formals supplied call : SExpRec_pointer) : result SExpRec_pointer :=
  fold%success (actuals, argi) := (R_NilValue : SExpRec_pointer, 0) along formals as _, _ do
    let (S, actuals) := CONS S R_MissingArg actuals in
    result_success S (actuals, 1 + argi) using S in
  fold%success along supplied as b, _ do
    map%pointer b with set_argused 0 ltac:(NBits.nbits_ok) using S in
    result_success S tt using S in
  let%success fargused := matchArgs_first S formals actuals supplied using S in
  let%success dots := matchArgs_second S actuals formals supplied fargused using S in
  let%success _ := matchArgs_third S formals actuals supplied using S in
  ifb dots <> R_NilValue then
    let%success _ := matchArgs_dots S dots supplied using S in
    result_success S actuals
  else
    let%success _ := matchArgs_check S supplied using S in
    result_success S actuals.


(** ** envir.c **)

(** The function names of this section corresponds to the function names
 * in the file main/envir.c. **)

Definition IS_SPECIAL_SYMBOL S symbol :=
  read%defined symbol_ := symbol using S in
  result_success S (NBits.nth_bit 12 (gp symbol_) ltac:(NBits.nbits_ok)).

Definition SET_SPECIAL_SYMBOL S x v :=
  map%gp x with @NBits.write_nbit 16 12 ltac:(NBits.nbits_ok) v using S in
  result_success S tt.

Definition R_envHasNoSpecialSymbols S (env : SExpRec_pointer) : result bool :=
  read%env env_, env_env := env using S in
  (* A note about hashtabs commented out. *)
  fold%let b := true along env_frame env_env as frame_car, frame_tag do
    let%success special := IS_SPECIAL_SYMBOL S frame_tag using S in
    if special then
      result_success S false
    else result_success S b using S.

Definition addMissingVarsToNewEnv S (env addVars : SExpRec_pointer) : result unit :=
  ifb addVars = R_NilValue then
    result_success S tt
  else
    read%defined addVars_ := addVars using S in
    ifb type addVars_ = EnvSxp then
      result_error S "[addMissingVarsToNewEnv] Additional variables should be passed as a list."
    else
      let%list addVars_, addVars_list := addVars_ using S in
      fold%success aprev := addVars along list_cdrval addVars_list as a, _, _ do
        result_success S a using S in
      read%env env_, env_env := env using S in
      set%cdr aprev := env_frame env_env using S in
      let env_env := {|
          env_frame := addVars ;
          env_enclos := env_enclos env_env
        |} in
      let env_ := {|
          NonVector_SExpRec_header := env_ ;
          NonVector_SExpRec_data := env_env
        |} in
      write%defined env := env_ using S in
      fold%let along list_cdrval addVars_list as _, end_, end_list do
        let end_tag := list_tagval end_list in
        do%success (addVars, s, sprev) := (addVars, addVars, R_NilValue : SExpRec_pointer)
        while result_success S (decide (s <> env)) do
          read%list s_, s_list := s using S in
            ifb list_tagval s_list = end_tag then
              ifb sprev = R_NilValue then
                let env_env := {|
                    env_frame := addVars ;
                    env_enclos := env_enclos env_env
                  |} in
                let env_ := {|
                    NonVector_SExpRec_header := env_ ;
                    NonVector_SExpRec_data := env_env
                  |} in
                write%defined env := env_ using S in
                result_success S (list_cdrval s_list, list_cdrval s_list, sprev)
              else
                set_cdr S (list_cdrval s_list) sprev (fun S =>
                  result_success S (addVars, list_cdrval s_list, sprev))
            else result_success S (addVars, list_cdrval s_list, s)
        using S in
        result_success S tt using S.

Definition FRAME_IS_LOCKED S rho :=
  read%defined rho_ := rho using S in
  result_success S (NBits.nth_bit 14 (gp rho_) ltac:(NBits.nbits_ok)).

Definition BINDING_IS_LOCKED S symbol :=
  read%defined symbol_ := symbol using S in
  result_success S (NBits.nth_bit 14 (gp symbol_) ltac:(NBits.nbits_ok)).

Definition IS_ACTIVE_BINDING S symbol :=
  read%defined symbol_ := symbol using S in
  result_success S (NBits.nth_bit 15 (gp symbol_) ltac:(NBits.nbits_ok)).

Definition setActiveValue S (f v : SExpRec_pointer) :=
  let%success arg_tail := lcons S v R_NilValue using S in
  let%success arg := lcons S R_QuoteSymbol arg_tail using S in
  let%success expr_tail := lcons S arg R_NilValue using S in
  let%success expr := lcons S f expr_tail using S in
  let%success _ := runs_eval runs S expr R_GlobalEnv using S in
  result_success S tt.

Definition SET_BINDING_VALUE S b val :=
  let%success locked := BINDING_IS_LOCKED S b using S in
  ifb locked then
    result_error S "[SET_BINDING_VALUE] Can not change value of locked binding."
  else
    let%success active := IS_ACTIVE_BINDING S b using S in
    read%list b_, b_list := b using S in
    ifb active then
      setActiveValue S (list_carval b_list) val
    else
      set%car b := val using S in
    result_success S tt.

Definition gsetVar S (symbol value rho : SExpRec_pointer) : result unit :=
  let%success locked := FRAME_IS_LOCKED S rho using S in
  let continuation S :=
    let%success locked := BINDING_IS_LOCKED S symbol using S in
    ifb locked then
      result_error S "[gsetVar] Can not change value of locked biding."
    else
      let%success active := IS_ACTIVE_BINDING S symbol using S in
      read%sym symbol_, symbol_sym := symbol using S in
      ifb active then
        setActiveValue S (sym_value symbol_sym) value
      else
        let symbol_sym := {|
            sym_pname := sym_pname symbol_sym ;
            sym_value := value ;
            sym_internal := sym_internal symbol_sym
          |} in
        let symbol_ := {|
            NonVector_SExpRec_header := NonVector_SExpRec_header symbol_ ;
            NonVector_SExpRec_data := symbol_sym
          |} in
        write%defined symbol := symbol_ using S in
        result_success S tt
    in
  if locked then
    read%sym symbol_, symbol_sym := symbol using S in
    ifb sym_value symbol_sym = R_UnboundValue then
      result_error S "[gsetVar] Can not add such a bidding to the base environment."
    else continuation S
  else continuation S.

Definition defineVar S (symbol value rho : SExpRec_pointer) : result unit :=
  ifb rho = R_EmptyEnv then
    result_error S "[defineVar] Can not assign values in the empty environment."
  else
    read%defined rho_ := rho using S in
    let%success inh := inherits S rho "UserDefinedDatabase" using S in
    if obj rho_ && inh then
      result_not_implemented "[defineVar] [R_ObjectTable]"
    else
      ifb rho = R_BaseNamespace \/ rho = R_BaseEnv then
        gsetVar S symbol value rho
      else
        let continuation S :=
          (** As we do not model hashtabs, we consider that the hashtab is not defined here. **)
          let%env rho_, rho_env := rho_ using S in
          fold%success ret := false along env_frame rho_env as frame, frame_, frame_list do
            if ret then
              result_success S true
            else
              ifb list_tagval frame_list = symbol then
                let%success _ := SET_BINDING_VALUE S frame value using S in
                let%success _ := SET_MISSING S frame 0 ltac:(NBits.nbits_ok) using S in
                result_success S true
              else
                result_success S false
            using S in
          if ret then
            result_success S tt
          else
            let%success locked := FRAME_IS_LOCKED S rho using S in
            ifb locked then
              result_error S "[defineVar] Can not add a binding to a locked environment."
            else
              let (S, l) := CONS S value (env_frame rho_env) in
              let rho_env := {|
                  env_frame := l ;
                  env_enclos := env_enclos rho_env
                |} in
              let rho_ := {|
                  NonVector_SExpRec_header := rho_ ;
                  NonVector_SExpRec_data := rho_env
                |} in
              write%defined rho := rho_ using S in
              set%tag env_frame rho_env := symbol using S in
              result_success S tt in
        let%success special := IS_SPECIAL_SYMBOL S symbol using S in
        if special then
          let%success _ := SET_SPECIAL_SYMBOL S rho false using S in
          continuation S
        else continuation S.

Definition setVarInFrame S (rho symbol value : SExpRec_pointer) :=
  ifb rho = R_EmptyEnv then
    result_success S (R_NilValue : SExpRec_pointer)
  else
    result_not_implemented "[setVarInFrame]".

Definition setVar S (symbol value rho : SExpRec_pointer) :=
  do%success rho := rho
  while result_success S (decide (rho <> R_EmptyEnv)) do
    let%success vl :=
      setVarInFrame S rho symbol value using S in
    ifb vl <> R_NilValue then
      result_success S (R_EmptyEnv : SExpRec_pointer)
    else
      read%env rho_, rho_env := rho using S in
      result_success S (env_enclos rho_env)
  using S in
  defineVar S symbol value R_GlobalEnv.


(** ** attrib.c **)

(** The function names of this section corresponds to the function names
 * in the file main/attrib.c. **)

Definition getAttrib0 (S : state) (vec name : SExpRec_pointer) : result SExpRec_pointer :=
  result_not_implemented "[getAttrib0] TODO".

Definition getAttrib S (vec name : SExpRec_pointer) :=
  read%defined vec_ := vec using S in
  ifb type vec_ = CharSxp then
    result_error S "[getAttrib] Can not have attributes on a [CharSxp]."
  else
    ifb attrib vec_ = R_NilValue /\ ~ (type vec_ = ListSxp \/ type vec_ = LangSxp) then
      result_success S (R_NilValue : SExpRec_pointer)
    else
      read%defined name_ := name using S in
      let continuation S (name : SExpRec_pointer) :=
        ifb name = R_RowNamesSymbol then
          let%success s := getAttrib0 S vec name using S in
          read%defined s_ := s using S in
          let%success s_int := isInteger S s using S in
          ifb s_int then
            let%defined s_length := get_VecSxp_length s_ using S in
            ifb s_length = 2 then
              let%Integer s_0 := s_ at 0 using S in
              ifb s_0 = R_NaInt then
                let%Integer s_1 := s_ at 1 using S in
                let n := abs s_1 in
                let (S, s) := alloc_vector_int S (map (id : nat -> int) (seq 1 n)) in
                result_success S s
              else result_success S s
            else result_success S s
          else result_success S s
        else getAttrib0 S vec name
      in
      ifb type name_ = StrSxp then
        read%VectorPointer name_ := name using S in
        let%success str := STRING_ELT S name 0 using S in
        let%success sym := installTrChar S str using S in
        continuation S sym
      else continuation S name.


(** ** eval.c **)

(** The function names of this section corresponds to the function names
 * in the file main/eval.c. **)

(** The function [forcePromise] evaluates a promise if needed. **)
Definition forcePromise S (e : SExpRec_pointer) : result SExpRec_pointer :=
  read%prom e_, e_prom := e using S in
  ifb prom_value e_prom = R_UnboundValue then
    let continuation S :=
      set%gp e with @NBits.nat_to_nbits 16 1 ltac:(NBits.nbits_ok) using S in
      let%success val := runs_eval runs S (prom_expr e_prom) (prom_env e_prom) using S in
      set%gp e with @NBits.nat_to_nbits 16 0 ltac:(NBits.nbits_ok) using S in
      map%pointer val with set_named_plural using S in
      read%prom e_, e_prom := e using S in
      let e_prom := {|
          prom_value := val ;
          prom_expr := prom_expr e_prom ;
          prom_env := R_NilValue
        |} in
      let e_ := {|
          NonVector_SExpRec_header := e_ ;
          NonVector_SExpRec_data := e_prom
        |} in
      write%defined e := e_ using S in
      result_success S val in
    ifb NBits.nbits_to_nat (gp e_) <> 0 then
      ifb NBits.nbits_to_nat (gp e_) = 1 then
        result_error S "[forcePromise] Promise already under evaluation."
      else
        (* Warning: restarting interrupted promise evaluation. *)
        continuation S
    else continuation S
  else result_success S (prom_value e_prom).

Definition R_execClosure (S : state)
    (call newrho sysparent rho arglist op : SExpRec_pointer) : result SExpRec_pointer :=
  result_not_implemented "[R_execClosure] TODO".

Definition applyClosure S
    (call op arglist rho suppliedvars : SExpRec_pointer) : result SExpRec_pointer :=
  read%defined rho_ := rho using S in
  ifb type rho_ <> EnvSxp then
    result_error S "[applyClosure] ‘rho’ must be an environment."
  else
    read%clo op_, op_clo := op using S in
    let formals := clo_formals op_clo in
    let savedrho := clo_env op_clo in
    let%success actuals := matchArgs S formals arglist call using S in
    let%success newrho := NewEnvironment S formals actuals savedrho using S in
    fold%success a := actuals along formals as f_car, f_tag do
      read%list a_, a_list := a using S in
      ifb list_carval a_list = R_MissingArg /\ f_car <> R_MissingArg then
        let%success newprom := mkPromise S f_car newrho using S in
        set%car a := newprom using S in
        let%success _ := SET_MISSING S a 2 ltac:(NBits.nbits_ok) using S in
        result_success S (list_cdrval a_list)
      else result_success S (list_cdrval a_list) using S in
    let%success _ :=
      ifb suppliedvars <> R_NilValue then
         addMissingVarsToNewEnv S newrho suppliedvars
       else result_success S tt using S in
    let%success _ :=
      let%success b := R_envHasNoSpecialSymbols S newrho using S in
      if b then
        let%success _ := SET_SPECIAL_SYMBOL S newrho false using S in
        result_success S tt
      else result_success S tt using S in
    R_execClosure S call newrho
      (ifb callflag (R_GlobalContext S) = Ctxt_Generic then
         sysparent (R_GlobalContext S)
       else rho)
      rho arglist op.


(** The function [eval] evaluates its argument to an unreducible value. **)
Definition eval S (e rho : SExpRec_pointer) :=
  read%defined e_ := e using S in
    match type e_ with
    | NilSxp
    | ListSxp
    | LglSxp
    | IntSxp
    | RealSxp
    | StrSxp
    | CplxSxp
    | RawSxp
    | S4Sxp
    | SpecialSxp
    | BuiltinSxp
    | EnvSxp
    | CloSxp
    | VecSxp
    | ExtptrSxp
    | WeakrefSxp
    | ExprSxp =>
      write%defined e := set_named_plural e_ using S in
      result_success S e
    | _ =>
      read%defined rho_ := rho using S in
      ifb type rho_ <> EnvSxp then
        result_error S "[eval] ‘rho’ must be an environment."
      else
        match type e_ with
        | BcodeSxp =>
          (** See https://github.com/wch/r-source/blob/trunk/src/main/eval.c#L3543
           * for a definition of this bytecode, and
           * https://github.com/wch/r-source/blob/trunk/src/main/eval.c#L5966
           * for the evaluator.
           * We do not consider byte code for now in this formalisation. **)
          result_not_implemented "[eval] byte code"
        | SymSxp =>
          ifb e = R_DotsSymbol then
            result_error S "[eval] ‘...’ used in an incorrect context."
          else
            (* TODO: https://github.com/wch/r-source/blob/trunk/src/main/eval.c#L626
             * I think that in essence, we are fetching the value of the symbol in the
             * environment, then evaluating it if we get a promise. **)
            (** There is just a story about ddfindVar vs findVar which I don’t yet
             * understand (depending on the general purpose field). I need to investigate
             * about these two functions. **)
            result_not_implemented "[eval] Symbols (TODO)"
        | PromSxp =>
          let%prom e_, e_prom := e_ using S in
          ifb prom_value e_prom = R_UnboundValue then
            let%success e := forcePromise S e using S in
            result_success S e
          else result_success S e
        | LangSxp =>
          let%list e_, e_list := e_ using S in
          let car := list_carval e_list in
          read%defined car_ := car using S in
          let%success op :=
            ifb type car_ = SymSxp then
              (* TODO: findFun3 — in essence, this is just a variable look-up. *)
              result_not_implemented "[eval] findFun3 (TODO)"
            else runs_eval runs S car rho using S in
          read%defined op_ := op using S in
            match type op_ with
            | SpecialSxp =>
              (* TODO: This is basically a direct call to PRIMFUN. *)
              result_not_implemented "[eval] PRIMFUN (TODO)"
            | BuiltinSxp =>
              (* TODO: This is basically a call to PRIMFUN after evaluating the argument list. *)
              result_not_implemented "[eval] PRIMFUN after argument evaluation (TODO)"
            | CloSxp =>
              (* TODO: https://github.com/wch/r-source/blob/trunk/src/main/eval.c
                 applyClosure(e, op, promiseArgs(CDR(e), rho), rho, R_NilValue);
               *)
              result_not_implemented "[eval] applyClosure (TODO)"
            | _ => result_error S "[eval] Attempt to apply non-function."
            end
        | DotSxp => result_error S "[eval] ‘...’ used in an incorrect context"
        | _ => result_error S "[eval] Type unimplemented in the R source code."
        end
    end.

(** Evaluates the expression in the global environment. **)
Definition eval_global S e :=
  eval S e R_GlobalEnv.

End ParameterisedRuns.


(** * Closing the Loop **)

Fixpoint runs max_step : runs_type :=
  match max_step with
  | O => {|
      runs_do_while := fun _ S _ _ _ => result_bottom S ;
      runs_eval := fun S _ _ => result_bottom S ;
      runs_inherits := fun S _ _ => result_bottom S ;
      runs_getAttrib := fun S _ _ => result_bottom S
    |}
  | S max_step =>
    let wrap {A B : Type} (f : runs_type -> B -> A) (x : B) : A :=
      (** It is important to take this additional parameter [x] as a parameter,
        * to defer the computation of [runs max_step] when it is indeed needed.
        * Without this, the application of [runs max_int] would overflow the
        * stack. **)
      f (runs max_step) x in
    let wrap_dep {A : Type -> Type} (f : runs_type -> forall B, A B) (T : Type) : A T :=
      (** A dependent version of [wrap]. **)
      f (runs max_step) T in {|
      runs_do_while := wrap_dep do_while ;
      runs_eval := wrap eval ;
      runs_inherits := wrap inherits ;
      runs_getAttrib := wrap getAttrib
    |}
  end.

End ParameterisedGlobals.

