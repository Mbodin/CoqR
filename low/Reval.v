(** Reval.
 * Describes how R evaluates expressions.
 * The content of this file is the Coq equivalent of functions from R source code.
 * Note that only relevant definitions are translated here. Some are just
 * reinterpreted in Coq without following the original algorithm of the
 * C source. **)

Set Implicit Arguments.
Require Export Monads.

(** * Global structure of the interpreter **)

(** A structure to deal with infinite execution (which is not allowed in Coq). Inspired from JSCert. **)
Record runs_type : Type := runs_type_intro {
    runs_do_while : forall A, state -> A -> (state -> A -> result bool) -> (state -> A -> result A) -> result A ;
    runs_eval : state -> SExpRec_pointer -> SExpRec_pointer -> result SExpRec_pointer
  }.


Section Parameterised.

Variable runs : runs_type.

(** * Global Definitions **)

Definition INT_MIN : int := - 2 ^ 31. (* We may want to make this a parameter. *)

Definition R_NaInt := INT_MIN.
Definition NA_LOGICAL := R_NaInt.

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


(** ** Rinlinedfuns.c **)

(** The function names of this section corresponds to the function names
 * in the file include/Rinlinedfuns.c. **)

(** The way the original functions [allocVector], [allocVector3], etc.
  * from R source code are defined are not compatible with the way the
  * memory of the C language has been formalised here. The functions
  * below are thus slightly from their C counterparts. **)

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


(** ** gram.y **)

(** The function names of this section corresponds to the function names
 * in the file main/gram.y. **)

Definition mkTrue S :=
  alloc_vector_lgl S [1 : int].

Definition mkFalse S :=
  alloc_vector_lgl S [0 : int].

Definition mkNA S :=
  alloc_vector_lgl S [NA_LOGICAL : int].


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

Definition endcontext S :=
  let cptr := R_GlobalContext S in
  let%success _ :=
    ifb cloenv cptr <> R_NilValue /\ conexit cptr <> R_NilValue then
      let s := conexit cptr in
      let S := state_with_context S (context_with_conexit cptr R_NilValue) in
      let%success _ := runs_eval runs S s (cloenv cptr) using S in
      result_success S tt
    else result_success S tt using S in
  let%defined c := nextcontext cptr using S in
  result_success (state_with_context S c) tt.


(** ** memory.c **)

(** The function names of this section corresponds to the function names
 * in the file main/memory.c. **)

Definition cons S (car cdr : SExpRec_pointer) : state * SExpRec_pointer :=
  let e_ := make_SExpRec_list R_NilValue car cdr R_NilValue in
  alloc_SExp S e_.

Definition allocList S (n : nat) : state * SExpRec_pointer :=
  let fix aux S n p :=
    match n with
    | 0 => (S, p)
    | S n =>
      let (S, p) := aux S n p in
      cons S R_NilValue p
    end
  in aux S n R_NilValue.

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
      let%sym str_, str_sym := str_ using S in
      read%VectorChar str_name_ := sym_pname str_sym using S in
      result_success S (list_to_string str_name_)
    | CharSxp =>
      let%defined str_ := get_VectorChar str_ using S in
      result_success S (list_to_string str_)
    | StrSxp =>
      result_not_implemented "[pmatch] translateChar(STRING_ELT(str, 0))"
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
  nbits_to_nat (gp e_).

Definition set_argused (used : nat) I :=
  set_gp (nat_to_nbits used I).
Arguments set_argused : clear implicits.

Definition missing e_ :=
  sub_nbits 0 4 (gp e_) ltac:(nbits_ok).

Definition set_missing (m : nat) I (e_ : SExpRec) :=
  set_gp (write_nbits 0 (nat_to_nbits m I : nbits 4) (gp e_) ltac:(nbits_ok)) e_.
Arguments set_missing : clear implicits.

Definition matchArgs_first S
    (formals actuals supplied : SExpRec_pointer) : result (list nat) :=
  fold%success (a, fargusedrev) := (actuals, nil) along formals as _, f_tag do
    read%sym f_tag_, f_tag_sym := f_tag using S in
    read%VectorChar f_tag_sym_name_ := sym_pname f_tag_sym using S in
    let ftag_name := list_to_string f_tag_sym_name_ in
    let continuation S fargusedi :=
      read%list a_, a_list := a using S in
      result_success S (list_cdrval a_list, fargusedi :: fargusedrev) in
    ifb f_tag <> R_DotsSymbol /\ f_tag <> R_NilValue then
      if_success (fold%let fargusedi := 0 along supplied as b, b_, b_list do
        let b_tag := list_tagval b_list in
        read%sym b_tag_, b_tag_sym := b_tag using S in
        read%VectorChar b_tag_sym_name_ := sym_pname b_tag_sym using S in
        let btag_name := list_to_string b_tag_sym_name_ in
        ifb b_tag <> R_NilValue /\ ftag_name = btag_name then
          ifb fargusedi = 2 then
            result_error S "[matchArgs_first] formal argument matched by multiple actual arguments."
          else ifb argused b_ = 2 then
            result_error S "[matchArgs_first] actual argument matches several formal arguments."
          else
            set%car a := list_carval b_list using S in
            let%success _ :=
              ifb list_carval b_list <> R_MissingArg then
                map%pointer a with set_missing 1 ltac:(nbits_ok) using S in
                result_success S tt
              else result_success S tt using S in
            map%pointer b with set_argused 2 ltac:(nbits_ok) using S in
            result_success S 2
        else
          result_success S fargusedi using S)
        continuation
    else continuation S 0 using S in
  result_success S (List.rev fargusedrev).

Definition matchArgs_second S
    (actuals formals supplied : SExpRec_pointer) fargused : result SExpRec_pointer :=
  fold%success (a, fargused, dots, seendots) := (actuals, fargused, R_NilValue, false)
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
                        map%pointer a with set_missing 0 ltac:(nbits_ok) using S in
                        result_success S tt
                      else result_success S tt using S in
                    map%pointer b with set_argused 1 ltac:(nbits_ok) using S in
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
            map%pointer a with set_missing 0 ltac:(nbits_ok) using S in
            result_success S tt
          else result_success S tt using S in
        result_success S (list_cdrval f_list, list_cdrval a_list, list_cdrval b_list, seendots)
  using S in
  result_success S tt.

Definition matchArgs_dots S
    (dots supplied : SExpRec_pointer) : result unit :=
  map%pointer dots with set_missing 0 ltac:(nbits_ok) using S in
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
        read%list f_, f_list := f using S in
        let f_list := {|
            list_carval := list_carval b_list ;
            list_cdrval := list_cdrval f_list ;
            list_tagval := list_tagval b_list
          |} in
        let f_ := {|
            NonVector_SExpRec_header := NonVector_SExpRec_header f_ ;
            NonVector_SExpRec_data := f_list
          |} in
        write%defined f := f_ using S in
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
  fold%success (actuals, argi) := (R_NilValue, 0) along formals as _, _ do
    let (S, actuals) := cons S R_MissingArg actuals in
    result_success S (actuals, 1 + argi) using S in
  fold%success _ := tt along supplied as b, _ do
    map%pointer b with set_argused 0 ltac:(nbits_ok) using S in
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

(** The function [mkChar] from the R source code performs a lot of things.
 * It deals with encoding, for embedded zero-characters, as well as avoid
 * allocated twice the same string, by looking through the already
 * allocated strings. We do none of the above. **)
(* FIXME: What is the difference between [intCHARSXP] and [CHARSXP]? *)
Definition mkChar S (str : string) : state * SExpRec_pointer :=
  alloc_vector_char S (string_to_list str).

Definition is_special_symbol e_ :=
  nth_bit 12 (gp e_) ltac:(nbits_ok).

Definition set_no_special_symbols (e_ : SExpRec) :=
  set_gp (write_nbit 12 (gp e_) ltac:(nbits_ok) true) e_.

Definition R_envHasNoSpecialSymbols S (env : SExpRec_pointer) : result bool :=
  read%env env_, env_env := env using S in
  (* A note about hashtabs commented out. *)
  fold%let b := true along env_frame env_env as frame_car, frame_tag do
    read%defined frame_tag_ := frame_tag using S in
    if is_special_symbol frame_tag_ then
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
      fold%let _ := tt along list_cdrval addVars_list as _, end_, end_list do
        let end_tag := list_tagval end_list in
        do%success (addVars, s, sprev) := (addVars, addVars, R_NilValue)
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

Definition defineVar (runs : runs_type) (S : state) (symbol value rho : SExpRec_pointer) : result SExpRec_pointer :=
  result_not_implemented "[defineVar] TODO".
(* TODO. *)


(** ** eval.c **)

(** The function names of this section corresponds to the function names
* in the file main/eval.c. **)

(** The function [forcePromise] evaluates a promise if needed. **)
Definition forcePromise S (e : SExpRec_pointer) : result SExpRec_pointer :=
  read%prom e_, e_prom := e using S in
  ifb prom_value e_prom = R_UnboundValue then
    let cont S :=
      map%pointer e with set_gp (@nat_to_nbits 16 1 ltac:(nbits_ok)) using S in
      let%success val := runs_eval runs S (prom_expr e_prom) (prom_env e_prom) using S in
      map%pointer e with set_gp (@nat_to_nbits 16 0 ltac:(nbits_ok)) using S in
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
    ifb nbits_to_nat (gp e_) <> 0 then
      ifb nbits_to_nat (gp e_) = 1 then
        result_error S "[forcePromise] Promise already under evaluation."
      else
        (* Warning: restarting interrupted promise evaluation. *)
        cont S
    else cont S
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
        map%pointer a with set_missing 2 ltac:(nbits_ok) using S in
        result_success S (list_cdrval a_list)
      else result_success S (list_cdrval a_list) using S in
    let%success _ :=
      ifb suppliedvars <> R_NilValue then
         addMissingVarsToNewEnv S newrho suppliedvars
       else result_success S tt using S in
    let%success _ :=
      let%success b := R_envHasNoSpecialSymbols S newrho using S in
      if b then
        map%pointer newrho with set_no_special_symbols using S in
        result_success S tt
      else result_success S tt using S in
    R_execClosure S call newrho
      (ifb callflag (R_GlobalContext S) = Ctxt_Generic then
         sysparent (R_GlobalContext S)
       else rho)
      rho arglist op.


(** The function [eval] evaluates its argument to an unreducible value. **)
Definition eval S (e rho : SExpRec_pointer) : result SExpRec_pointer :=
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


(** ** names.c **)

(** The function names of this section corresponds to the function names
* in the file main/names.c. **)

Definition install (runs : runs_type) (S : state) (name : string) : result SExpRec_pointer :=
  result_not_implemented "[install] TODO".
(* TODO. It creates a new symbol object from this string. *)


End Parameterised.

