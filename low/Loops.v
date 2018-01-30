(** RLoops.
  This file provides looping monads to easily manipulate R objects. **)

Set Implicit Arguments.
Require Export Monads Globals.

(** * Global structure of the interpreter **)

(** A structure to deal with infinite execution (which is not allowed in Coq). Inspired from JSCert. **)
Record runs_type : Type := runs_type_intro {
    runs_while_loop : forall A, state -> A -> (state -> A -> result bool) -> (state -> A -> result A) -> result A ;
    runs_set_longjump : forall A, state -> context_type -> nat -> (state -> context_type -> result A) -> result A ;
    runs_eval : state -> SExpRec_pointer -> SExpRec_pointer -> result SExpRec_pointer ;
    runs_inherits : state -> SExpRec_pointer -> string -> result bool ;
    runs_getAttrib : state -> SExpRec_pointer -> SExpRec_pointer -> result SExpRec_pointer ;
    runs_R_cycle_detected : state -> SExpRec_pointer -> SExpRec_pointer -> result bool ;
    runs_stripAttrib : state -> SExpRec_pointer -> SExpRec_pointer -> result SExpRec_pointer ;
    runs_R_isMissing : state -> SExpRec_pointer -> SExpRec_pointer -> result bool ;
    runs_AnswerType : state -> SExpRec_pointer -> bool -> bool -> BindData -> SExpRec_pointer -> result BindData ;
    runs_ListAnswer : state -> SExpRec_pointer -> bool -> BindData -> SExpRec_pointer -> result BindData ;
    runs_StringAnswer : state -> SExpRec_pointer -> BindData -> SExpRec_pointer -> result BindData ;
    runs_LogicalAnswer : state -> SExpRec_pointer -> BindData -> SExpRec_pointer -> result BindData ;
    runs_IntegerAnswer : state -> SExpRec_pointer -> BindData -> SExpRec_pointer -> result BindData ;
    runs_RealAnswer : state -> SExpRec_pointer -> BindData -> SExpRec_pointer -> result BindData ;
    runs_ComplexAnswer : state -> SExpRec_pointer -> BindData -> SExpRec_pointer -> result BindData ;
    runs_RawAnswer : state -> SExpRec_pointer -> BindData -> SExpRec_pointer -> result BindData ;
    runs_R_FunTab : funtab
  }.


(** * Frequent Patterns **)

(** The functions presented here are not from R source code, but
  represent frequent programming pattern in its source code. **)

(** ** While **)

(** A basic C-like loop **)
Definition while_loop runs A S (a : A) expr stat : result A :=
  if%success expr S a using S then
    let%success a := stat S a using S in
    runs_while_loop runs S a expr stat
  else
    result_success S a.

Notation "'do%let' a ':=' e 'while' expr 'do' stat 'using' S ',' runs" :=
  (while_loop runs S e (fun S a => expr) (fun S a => stat))
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' 'while' expr 'do' stat 'using' S ',' runs" :=
  (do%let _ := tt while expr do stat using S, runs)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ')' ':=' a 'while' expr 'do' stat 'using' S ',' runs" :=
  (do%let x := a
   while let (a1, a2) := x in expr
   do let (a1, a2) := x in stat
   using S, runs)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ')' ':=' a 'while' expr 'do' stat 'using' S ',' runs" :=
  (do%let x := a
   while let '(a1, a2, a3) := x in expr
   do let '(a1, a2, a3) := x in stat
   using S, runs)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' a 'while' expr 'do' stat 'using' S ',' runs" :=
  (do%let x := a
   while let '(a1, a2, a3, a4) := x in expr
   do let '(a1, a2, a3, a4) := x in stat
   using S, runs)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' a 'while' expr 'do' stat 'using' S ',' runs" :=
  (do%let x := a
   while let '(a1, a2, a3, a4, a5) := x in expr
   do let '(a1, a2, a3, a4, a5) := x in stat
   using S, runs)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' a 'while' expr 'do' stat 'using' S ',' runs" :=
  (do%let x := a
   while let '(a1, a2, a3, a4, a5, a6) := x in expr
   do let '(a1, a2, a3, a4, a5, a6) := x in stat
   using S, runs)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' 'while' expr 'do' stat 'using' S ',' runs 'in' cont" :=
  (run%success
     do%let while expr
     do stat
     using S, runs using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' a ':=' e 'while' expr 'do' stat 'using' S ',' runs 'in' cont" :=
  (let%success a :=
     do%let a := e
     while expr
     do stat
     using S, runs using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ')' ':=' a 'while' expr 'do' stat 'using' S ',' runs 'in' cont" :=
  (let%success (a1, a2) :=
     do%let (a1, a2) := a
     while expr
     do stat
     using S, runs using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ')' ':=' a 'while' expr 'do' stat 'using' S ',' runs 'in' cont" :=
  (let%success (a1, a2, a3) :=
     do%let (a1, a2, a3) := a
     while expr
     do stat
     using S, runs using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' a 'while' expr 'do' stat 'using' S ',' runs 'in' cont" :=
  (let%success (a1, a2, a3, a4) :=
     do%let (a1, a2, a3, a4) := a
     while expr
     do stat
     using S, runs using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' a 'while' expr 'do' stat 'using' S ',' runs 'in' cont" :=
  (let%success (a1, a2, a3, a4, a5) :=
     do%let (a1, a2, a3, a4, a5) := a
     while expr
     do stat
     using S, runs using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' a 'while' expr 'do' stat 'using' S ',' runs 'in' cont" :=
  (let%success (a1, a2, a3, a4, a5, a6) :=
     do%let (a1, a2, a3, a4, a5, a6) := a
     while expr
     do stat
     using S, runs using S in
   cont)
  (at level 50, left associativity) : monad_scope.


(** ** Fold **)

(** Looping through a list is a frequent pattern in R source code.
  [fold_left_listSxp_gen] corresponds to the C code
  [for (i = l, v = a; i != R_NilValue; i = CDR (i)) v = iterate ( *i, v); v]. **)
Definition fold_left_listSxp_gen runs (globals : Globals) A S (l : SExpRec_pointer) (a : A)
    (iterate : state -> A -> SExpRec_pointer -> SExpRec -> ListSxp_struct -> result A) : result A :=
  do%success (l, a) := (l, a)
  while result_success S (decide (l <> global_mapping globals R_NilValue))
  do
    read%list l_, l_list := l using S in
    let%success a := iterate S a l l_ l_list using S in
    result_success S (list_cdrval l_list, a)
  using S, runs in
  result_success S a.

Notation "'fold%let' a ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S ',' runs ',' globals" :=
  (fold_left_listSxp_gen runs globals S le e (fun S a l l_ l_list => iterate))
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S ',' runs ',' globals" :=
  (fold%let _ := tt
   along le
   as l, l_, l_list
   do iterate
   using S, runs, globals)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' '(' a1 ',' a2 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S ',' runs ',' globals" :=
  (fold%let x := e
   along le
   as l, l_, l_list
   do let (a1, a2) := x in iterate
   using S, runs, globals)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' '(' a1 ',' a2 ',' a3 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S ',' runs ',' globals" :=
  (fold%let x := e
   along le
   as l, l_, l_list
   do let '(a1, a2, a3) := x in iterate
   using S, runs, globals)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S ',' runs ',' globals" :=
  (fold%let x := e
   along le
   as l, l_, l_list
   do let '(a1, a2, a3, a4) := x in iterate
   using S, runs, globals)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S ',' runs ',' globals" :=
  (fold%let x := e
   along le
   as l, l_, l_list
   do let '(a1, a2, a3, a4, a5) := x in iterate
   using S, runs, globals)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S ',' runs ',' globals" :=
  (fold%let x := e
   along le
   as l, l_, l_list
   do let '(a1, a2, a3, a4, a5, a6) := x in iterate
   using S, runs, globals)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S ',' runs ',' globals 'in' cont" :=
  (run%success
     fold%let
     along le
     as l, l_, l_list
     do iterate
     using S, runs, globals using S in
   cont)
    (at level 50, left associativity) : monad_scope.

Notation "'fold%success' a ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S ',' runs ',' globals 'in' cont" :=
  (let%success a :=
     fold%let a := e
     along le
     as l, l_, l_list
     do iterate
     using S, runs, globals using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' '(' a1 ',' a2 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S ',' runs ',' globals 'in' cont" :=
  (let%success (a1, a2) :=
     fold%let (a1, a2) := e
     along le
     as l, l_, l_list
     do iterate
     using S, runs, globals using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' '(' a1 ',' a2 ',' a3 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S ',' runs ',' globals 'in' cont" :=
  (let%success (a1, a2, a3) :=
     fold%let (a1, a2, a3) := e
     along le
     as l, l_, l_list
     do iterate
     using S, runs, globals using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S ',' runs ',' globals 'in' cont" :=
  (let%success (a1, a2, a3, a4) :=
     fold%let (a1, a2, a3, a4) := e
     along le
     as l, l_, l_list
     do iterate
     using S, runs, globals using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S ',' runs ',' globals 'in' cont" :=
  (let%success (a1, a2, a3, a4, a5) :=
     fold%let (a1, a2, a3, a4, a5) := e
     along le
     as l, l_, l_list
     do iterate
     using S, runs, globals using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S ',' runs ',' globals 'in' cont" :=
  (let%success (a1, a2, a3, a4, a5, a6) :=
     fold%let (a1, a2, a3, a4, a5, a6) := e
     along le
     as l, l_, l_list
     do iterate
     using S, runs, globals using S in
   cont)
  (at level 50, left associativity) : monad_scope.


(** [fold_left_listSxp] corresponds to the C code
  [for (i = l, v = a; i != R_NilValue; i = CDR (i)) v = iterate (CAR (i), TAG (i), v); v]. **)
Definition fold_left_listSxp runs globals A S (l : SExpRec_pointer) (a : A)
    (iterate : state -> A -> SExpRec_pointer -> SExpRec_pointer -> result A) : result A :=
  fold%let a := a
  along l
  as _, _, l_list
  do iterate S a (list_carval l_list) (list_tagval l_list)
  using S, runs, globals.

Notation "'fold%let' a ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' S ',' runs ',' globals" :=
  (fold_left_listSxp runs globals S le e (fun S a l_car l_tag => iterate))
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' '(' a1 ',' a2 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' S ',' runs ',' globals" :=
  (fold%let x := e
   along le
   as l_car, l_tag
   do let (a1, a2) := x in iterate
   using S, runs, globals)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' '(' a1 ',' a2 ',' a3 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' S ',' runs ',' globals" :=
  (fold%let x := e
   along le
   as l_car, l_tag
   do let '(a1, a2, a3) := x in iterate
   using S, runs, globals)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' S ',' runs ',' globals" :=
  (fold%let x := e
   along le
   as l_car, l_tag
   do let '(a1, a2, a3, a4) := x in iterate
   using S, runs, globals)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' S ',' runs ',' globals" :=
  (fold%let x := e
   along le
   as l_car, l_tag
   do let '(a1, a2, a3, a4, a5) := x in iterate
   using S, runs, globals)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%let' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' S ',' runs ',' globals" :=
  (fold%let x := e
   along le
   as l_car, l_tag
   do let '(a1, a2, a3, a4, a5, a6) := x in iterate
   using S, runs, globals)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' S ',' runs ',' globals 'in' cont" :=
  (run%success
     fold%let _ := tt
     along le
     as l_car, l_tag
     do iterate
     using S, runs, globals using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' a ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' S ',' runs ',' globals 'in' cont" :=
  (let%success a :=
     fold%let a := e
     along le
     as l_car, l_tag
     do iterate
     using S, runs, globals using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' '(' a1 ',' a2 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' S ',' runs ',' globals 'in' cont" :=
  (let%success (a1, a2) :=
     fold%let (a1, a2) := e
     along le
     as l_car, l_tag
     do iterate
     using S, runs, globals using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' '(' a1 ',' a2 ',' a3 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' S ',' runs ',' globals 'in' cont" :=
  (let%success (a1, a2, a3) :=
     fold%let (a1, a2, a3) := e
     along le
     as l_car, l_tag
     do iterate
     using S, runs, globals using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' S ',' runs ',' globals 'in' cont" :=
  (let%success (a1, a2, a3, a4) :=
     fold%let (a1, a2, a3, a4) := e
     along le
     as l_car, l_tag
     do iterate
     using S, runs, globals using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' S ',' runs ',' globals 'in' cont" :=
  (let%success (a1, a2, a3, a4, a5) :=
     fold%let (a1, a2, a3, a4, a5) := e
     along le
     as l_car, l_tag
     do iterate
     using S, runs, globals using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' S ',' runs ',' globals 'in' cont" :=
  (let%success (a1, a2, a3, a4, a5, a6) :=
     fold%let (a1, a2, a3, a4, a5, a6) := e
     along le
     as l_car, l_tag
     do iterate
     using S, runs, globals using S in
   cont)
  (at level 50, left associativity) : monad_scope.


(** ** Return **)

(** The following notations deal with loops that may return.
  In these cases, one can use the definitions [result_rsuccess],
  or [result_rskip] for a normal ending of the loop, and
  [result_rreturn] for a breaking return. Note that this only
  breaks the current loop and its continuation, not the whole
  function. **)

Inductive normal_return A B :=
  | normal_result : A -> normal_return A B
  | return_result : B -> normal_return A B
  .
Arguments normal_result {A B}.
Arguments return_result {A B}.

Definition result_rsuccess {A B} S r : result (normal_return A B) :=
  result_success S (normal_result r).

Definition result_rskip {B} S : result (normal_return _ B) :=
  result_rsuccess S tt.

Definition result_rreturn {A B} S r : result (normal_return A B) :=
  result_success S (return_result r).

Definition match_rresult {A B C} (r : result (normal_return A B)) cont
    : result (normal_return C B) :=
  let%success res := r using S in
  match res with
  | normal_result r => cont S r
  | return_result r => result_rreturn S r
  end.

Notation "'let%return' a ':=' e 'using' S 'in' cont" :=
  (match_rresult e (fun S a => cont))
  (at level 50, left associativity) : monad_scope.

Notation "'run%return' c 'using' S 'in' cont" :=
  (let%return _ := c using S in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%return' '(' a1 ',' a2 ')' ':=' e 'using' S 'in' cont" :=
  (let%return a := e using S in
   let (a1, a2) := a in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%return' '(' a1 ',' a2 ',' a3 ')' ':=' e 'using' S 'in' cont" :=
  (let%return a := e using S in
   let '(a1, a2, a3) := a in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%return' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'using' S 'in' cont" :=
  (let%return a := e using S in
   let '(a1, a2, a3, a4) := a in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%return' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'using' S 'in' cont" :=
  (let%return a := e using S in
   let '(a1, a2, a3, a4, a5) := a in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%return' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' e 'using' S 'in' cont" :=
  (let%return a := e using S in
   let '(a1, a2, a3, a4, a5, a6) := a in cont)
  (at level 50, left associativity) : monad_scope.



(** Exiting the return-monad. **)
Definition exit_rresult {A B} (r : result (normal_return A B)) cont :=
  let%success res := r using S in
  match res with
  | normal_result r => cont S r
  | return_result r => result_success S r
  end.

Notation "'let%exit' a ':=' e 'using' S 'in' cont" :=
  (exit_rresult e (fun S a => cont))
  (at level 50, left associativity) : monad_scope.

Notation "'run%exit' c 'using' S 'in' cont" :=
  (let%exit _ := c using S in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%exit' '(' a1 ',' a2 ')' ':=' e 'using' S 'in' cont" :=
  (let%exit a := e using S in
   let (a1, a2) := a in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%exit' '(' a1 ',' a2 ',' a3 ')' ':=' e 'using' S 'in' cont" :=
  (let%exit a := e using S in
   let '(a1, a2, a3) := a in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%exit' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'using' S 'in' cont" :=
  (let%exit a := e using S in
   let '(a1, a2, a3, a4) := a in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%exit' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'using' S 'in' cont" :=
  (let%exit a := e using S in
   let '(a1, a2, a3, a4, a5) := a in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'let%exit' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' e 'using' S 'in' cont" :=
  (let%exit a := e using S in
   let '(a1, a2, a3, a4, a5, a6) := a in cont)
  (at level 50, left associativity) : monad_scope.


Definition continue_and_condition {A B} S (r : normal_return A B) cond :=
  match r with
  | normal_result r => cond S r
  | return_result r => result_success S false
  end.

Definition get_success {A B} S (r : normal_return A B) cont
    : result (normal_return A B) :=
  match r with
  | normal_result r => cont S r
  | return_result r => result_rreturn S r
  end.


Notation "'do%return' 'while' expr 'do' stat 'using' S ',' runs 'in' cont" :=
  (run%exit
     do%let ret := normal_result tt
     while continue_and_condition S ret (fun S _ => expr)
     do stat
     using S, runs
   using S in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%return' a ':=' e 'while' expr 'do' stat 'using' S ',' runs 'in' cont" :=
  (let%exit a :=
     do%let a := normal_result e
     while continue_and_condition S a (fun S a => expr)
     do get_success S a (fun S a => stat)
     using S, runs
   using S in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%return' '(' a1 ',' a2 ')' ':=' e 'while' expr 'do' stat 'using' S ',' runs 'in' cont" :=
  (do%return a := e
   while let (a1, a2) := a in expr
   do let (a1, a2) := a in stat
   using S, runs
   in let (a1, a2) := a in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%return' '(' a1 ',' a2 ',' a3 ')' ':=' e 'while' expr 'do' stat 'using' S ',' runs 'in' cont" :=
  (do%return a := e
   while let (a1, a2, a3) := a in expr
   do let (a1, a2, a3) := a in stat
   using S, runs
   in let (a1, a2, a3) := a in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%return' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'while' expr 'do' stat 'using' S ',' runs 'in' cont" :=
  (do%return a := e
   while let (a1, a2, a3, a4) := a in expr
   do let (a1, a2, a3, a4) := a in stat
   using S, runs
   in let (a1, a2, a3, a4) := a in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%return' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'while' expr 'do' stat 'using' S ',' runs 'in' cont" :=
  (do%return a := e
   while let (a1, a2, a3, a4, a5) := a in expr
   do let (a1, a2, a3, a4, a5) := a in stat
   using S, runs
   in let (a1, a2, a3, a4, a5) := a in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%return' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' e 'while' expr 'do' stat 'using' S ',' runs 'in' cont" :=
  (do%return a := e
   while let (a1, a2, a3, a4, a5, a6) := a in expr
   do let (a1, a2, a3, a4, a5, a6) := a in stat
   using S, runs
   in let (a1, a2, a3, a4, a5, a6) := a in cont)
  (at level 50, left associativity) : monad_scope.


Notation "'fold%return' a ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S ',' runs ',' globals 'in' cont" :=
  (let%exit a :=
     fold%let a := normal_result e
     along le
     as l, l_, l_list
     do get_success S a (fun S a => iterate)
     using S, runs, globals
   using S in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%return' 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S ',' runs ',' globals 'in' cont" :=
  (fold%return ret := tt
   along le
   as l, l_, l_list
   do iterate
   using S, runs, globals in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%return' '(' a1 ',' a2 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S ',' runs ',' globals 'in' cont" :=
  (fold%return a := e
   along le
   as l, l_, l_list
   do let (a1, a2) := a in iterate
   using S, runs, globals in
   let (a1, a2) := a in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%return' '(' a1 ',' a2 ',' a3 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S ',' runs ',' globals 'in' cont" :=
  (fold%return a := e
   along le
   as l, l_, l_list
   do let (a1, a2, a3) := a in iterate
   using S, runs, globals in
   let (a1, a2, a3) := a in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%return' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S ',' runs ',' globals 'in' cont" :=
  (fold%return a := e
   along le
   as l, l_, l_list
   do let (a1, a2, a3, a4) := a in iterate
   using S, runs, globals in
   let (a1, a2, a3, a4) := a in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%return' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S ',' runs ',' globals 'in' cont" :=
  (fold%return a := e
   along le
   as l, l_, l_list
   do let (a1, a2, a3, a4, a5) := a in iterate
   using S, runs, globals in
   let (a1, a2, a3, a4, a5) := a in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%return' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' e 'along' le 'as' l ',' l_ ',' l_list 'do' iterate 'using' S ',' runs ',' globals 'in' cont" :=
  (fold%return a := e
   along le
   as l, l_, l_list
   do let (a1, a2, a3, a4, a5, a6) := a in iterate
   using S, runs, globals in
   let (a1, a2, a3, a4, a5, a6) := a in
   cont)
  (at level 50, left associativity) : monad_scope.


Notation "'fold%return' a ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' S ',' runs ',' globals 'in' cont" :=
  (let%exit a :=
     fold%let a := normal_result e
     along le
     as l_car, l_tag
     do get_success S a (fun S a => iterate)
     using S, runs, globals
   using S in cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%return' 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' S ',' runs ',' globals 'in' cont" :=
  (fold%return ret := tt
   along le
   as l_car, l_tag
   do iterate
   using S, runs, globals in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%return' '(' a1 ',' a2 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' S ',' runs ',' globals 'in' cont" :=
  (fold%return a := e
   along le
   as l_car, l_tag
   do let (a1, a2) := a in iterate
   using S, runs, globals in
   let (a1, a2) := a in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%return' '(' a1 ',' a2 ',' a3 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' S ',' runs ',' globals 'in' cont" :=
  (fold%return a := e
   along le
   as l_car, l_tag
   do let (a1, a2, a3) := a in iterate
   using S, runs, globals in
   let (a1, a2, a3) := a in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%return' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' S ',' runs ',' globals 'in' cont" :=
  (fold%return a := e
   along le
   as l_car, l_tag
   do let (a1, a2, a3, a4) := a in iterate
   using S, runs, globals in
   let (a1, a2, a3, a4) := a in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%return' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' S ',' runs ',' globals 'in' cont" :=
  (fold%return a := e
   along le
   as l_car, l_tag
   do let (a1, a2, a3, a4, a5) := a in iterate
   using S, runs, globals in
   let (a1, a2, a3, a4, a5) := a in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'fold%return' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' e 'along' le 'as' l_car ',' l_tag 'do' iterate 'using' S ',' runs ',' globals 'in' cont" :=
  (fold%return a := e
   along le
   as l_car, l_tag
   do let (a1, a2, a3, a4, a5, a6) := a in iterate
   using S, runs, globals in
   let (a1, a2, a3, a4, a5, a6) := a in
   cont)
  (at level 50, left associativity) : monad_scope.


(** * Long Jump Monads **)

(** R source code uses long jumps. These monads specify their behaviour. **)

Definition set_longjump runs (A : Type) S mask (cjmpbuf : nat) (f : state -> context_type -> result A) : result A :=
  match f S mask with
  | result_success S0 a => result_success S0 a
  | result_error S0 s => result_error S0 s
  | result_longjump S0 n mask =>
    ifb cjmpbuf = n then
      runs_set_longjump runs S0 mask cjmpbuf f
    else result_longjump S0 n mask
  | result_impossible S0 s => result_impossible S0 s
  | result_not_implemented s => result_not_implemented s
  | result_bottom S0 => result_bottom S0
  end.

Notation "'set%longjump' cjmpbuf 'as' ret 'using' S ',' runs 'in' cont" :=
  (set_longjump runs S empty_context_type cjmpbuf (fun S ret => cont))
  (at level 50, left associativity) : monad_scope.


(** * Finite Loops **)

(** The following loops terminate in a finite number of steps and thus do not use fuel. **)

(** ** Along Lists **)

Definition for_list A B S (a : A) (l : list B) body :=
  fold_left (fun i (r : result A) =>
      let%success a := r using S in
      body S a i)
    (result_success S a) l.

Notation "'do%let' a ':=' e 'for' i 'in%list' l 'do' body 'using' S" :=
  (for_list S e l (fun S a i => body))
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' 'for' i 'in%list' l 'do' body 'using' S" :=
  (do%let _ := tt for i in%list l do body using S)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ')' ':=' a 'for' i 'in%list' l 'do' body 'using' S" :=
  (do%let x := a for i in%list l
   do let (a1, a2) := x in body using S)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ')' ':=' a 'for' i 'in%list' l 'do' body 'using' S" :=
  (do%let x := a for i in%list l
   do let '(a1, a2, a3) := x in body using S)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' a 'for' i 'in%list' l 'do' body 'using' S" :=
  (do%let x := a for i in%list l
   do let '(a1, a2, a3, a4) := x in body using S)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' a 'for' i 'in%list' l 'do' body 'using' S" :=
  (do%let x := a for i in%list l
   do let '(a1, a2, a3, a4, a5) := x in body using S)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' a 'for' i 'in%list' l 'do' body 'using' S" :=
  (do%let x := a for i in%list l
   do let '(a1, a2, a3, a4, a5, a6) := x in body using S)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' 'for' i 'in%list' l 'do' body 'using' S 'in' cont" :=
  (run%success
     do%let for i in%list l
     do body
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' a ':=' e 'for' i 'in%list' l 'do' body 'using' S 'in' cont" :=
  (let%success a :=
     do%let a := e
     for i in%list l
     do body
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ')' ':=' e 'for' i 'in%list' l 'do' body 'using' S 'in' cont" :=
  (let%success (a1, a2) :=
     do%let (a1, a2) := e
     for i in%list l
     do body
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ')' ':=' e 'for' i 'in%list' l 'do' body 'using' S 'in' cont" :=
  (let%success (a1, a2, a3) :=
     do%let (a1, a2, a3) := e
     for i in%list l
     do body
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'for' i 'in%list' l 'do' body 'using' S 'in' cont" :=
  (let%success (a1, a2, a3, a4) :=
     do%let (a1, a2, a3, a4) := e
     for i in%list l
     do body
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'for' i 'in%list' l 'do' body 'using' S 'in' cont" :=
  (let%success (a1, a2, a3, a4, a5) :=
     do%let (a1, a2, a3, a4, a5) := e
     for i in%list l
     do body
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' e 'for' i 'in%list' l 'do' body 'using' S 'in' cont" :=
  (let%success (a1, a2, a3, a4, a5, a6) :=
     do%let (a1, a2, a3, a4, a5, a6) := e
     for i in%list l
     do body
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.


(** ** Along Intervals **)

Definition for_loop A S (a : A) (start : nat) (last : int) body :=
  ifb last < start then
    result_success S a
  else
    (** We know that [last >= 0]. **)
    do%let x := a
    for i in%list seq start (1 + Z.to_nat last - start) do
      body S x i using S.

Notation "'do%let' a ':=' e 'for' i 'from' start 'to' last 'do' body 'using' S" :=
  (for_loop S e start last (fun S a i => body))
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' 'for' i 'from' start 'to' last 'do' body 'using' S" :=
  (do%let _ := tt for i from start to last do body using S)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ')' ':=' a 'for' i 'from' start 'to' last 'do' body 'using' S" :=
  (do%let x := a for i from start to last
   do let (a1, a2) := x in body using S)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ')' ':=' a 'for' i 'from' start 'to' last 'do' body 'using' S" :=
  (do%let x := a for i from start to last
   do let '(a1, a2, a3) := x in body using S)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' a 'for' i 'from' start 'to' last 'do' body 'using' S" :=
  (do%let x := a for i from start to last
   do let '(a1, a2, a3, a4) := x in body using S)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' a 'for' i 'from' start 'to' last 'do' body 'using' S" :=
  (do%let x := a for i from start to last
   do let '(a1, a2, a3, a4, a5) := x in body using S)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' a 'for' i 'from' start 'to' last 'do' body 'using' S" :=
  (do%let x := a for i from start to last
   do let '(a1, a2, a3, a4, a5, a6) := x in body using S)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' 'for' i 'from' start 'to' last 'do' body 'using' S 'in' cont" :=
  (run%success
     do%let for i from start to last
     do body
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' a ':=' e 'for' i 'from' start 'to' last 'do' body 'using' S 'in' cont" :=
  (let%success a :=
     do%let a := e
     for i from start to last
     do body
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ')' ':=' e 'for' i 'from' start 'to' last 'do' body 'using' S 'in' cont" :=
  (let%success (a1, a2) :=
     do%let (a1, a2) := e
     for i from start to last
     do body
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ')' ':=' e 'for' i 'from' start 'to' last 'do' body 'using' S 'in' cont" :=
  (let%success (a1, a2, a3) :=
     do%let (a1, a2, a3) := e
     for i from start to last
     do body
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'for' i 'from' start 'to' last 'do' body 'using' S 'in' cont" :=
  (let%success (a1, a2, a3, a4) :=
     do%let (a1, a2, a3, a4) := e
     for i from start to last
     do body
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'for' i 'from' start 'to' last 'do' body 'using' S 'in' cont" :=
  (let%success (a1, a2, a3, a4, a5) :=
     do%let (a1, a2, a3, a4, a5) := e
     for i from start to last
     do body
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' e 'for' i 'from' start 'to' last 'do' body 'using' S 'in' cont" :=
  (let%success (a1, a2, a3, a4, a5, a6) :=
     do%let (a1, a2, a3, a4, a5, a6) := e
     for i from start to last
     do body
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.


(** ** Along Arrays **)

Definition for_array A B S (a : A) (array : ArrayList.array B) body :=
  do%let x := a
  for i in%list ArrayList.to_list array do
    body S x i using S.

Notation "'do%let' a ':=' e 'for' i 'in%array' array 'do' body 'using' S" :=
  (for_array S e array (fun S a i => body))
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' 'for' i 'in%array' array 'do' body 'using' S" :=
  (do%let _ := tt for i in%array array do body using S)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ')' ':=' a 'for' i 'in%array' array 'do' body 'using' S" :=
  (do%let x := a for i in%array array
   do let (a1, a2) := x in body using S)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ')' ':=' a 'for' i 'in%array' array 'do' body 'using' S" :=
  (do%let x := a for i in%array array
   do let '(a1, a2, a3) := x in body using S)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' a 'for' i 'in%array' array 'do' body 'using' S" :=
  (do%let x := a for i in%array array
   do let '(a1, a2, a3, a4) := x in body using S)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' a 'for' i 'in%array' array 'do' body 'using' S" :=
  (do%let x := a for i in%array array
   do let '(a1, a2, a3, a4, a5) := x in body using S)
  (at level 50, left associativity) : monad_scope.

Notation "'do%let' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' a 'for' i 'in%array' array 'do' body 'using' S" :=
  (do%let x := a for i in%array array
   do let '(a1, a2, a3, a4, a5, a6) := x in body using S)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' 'for' i 'in%array' array 'do' body 'using' S 'in' cont" :=
  (run%success
     do%let for i in%array array
     do body
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' a ':=' e 'for' i 'in%array' array 'do' body 'using' S 'in' cont" :=
  (let%success a :=
     do%let a := e
     for i in%array array
     do body
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ')' ':=' e 'for' i 'in%array' array 'do' body 'using' S 'in' cont" :=
  (let%success (a1, a2) :=
     do%let (a1, a2) := e
     for i in%array array
     do body
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ')' ':=' e 'for' i 'in%array' array 'do' body 'using' S 'in' cont" :=
  (let%success (a1, a2, a3) :=
     do%let (a1, a2, a3) := e
     for i in%array array
     do body
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ',' a4 ')' ':=' e 'for' i 'in%array' array 'do' body 'using' S 'in' cont" :=
  (let%success (a1, a2, a3, a4) :=
     do%let (a1, a2, a3, a4) := e
     for i in%array array
     do body
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ')' ':=' e 'for' i 'in%array' array 'do' body 'using' S 'in' cont" :=
  (let%success (a1, a2, a3, a4, a5) :=
     do%let (a1, a2, a3, a4, a5) := e
     for i in%array array
     do body
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.

Notation "'do%success' '(' a1 ',' a2 ',' a3 ',' a4 ',' a5 ',' a6 ')' ':=' e 'for' i 'in%array' array 'do' body 'using' S 'in' cont" :=
  (let%success (a1, a2, a3, a4, a5, a6) :=
     do%let (a1, a2, a3, a4, a5, a6) := e
     for i in%array array
     do body
     using S using S in
   cont)
  (at level 50, left associativity) : monad_scope.
