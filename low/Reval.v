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
    runs_while : forall A, state -> A -> (state -> A -> result bool) -> (state -> A -> result A) -> result A ;
    runs_eval : state -> SExpRec_pointer -> SExpRec_pointer -> result SExpRec_pointer
  }.


(** * Interpreter functions **)

(** We recall from RinternalsAux.v that we write [p_] for the object
 * referenced by the pointer [p], and [p_f] for the field [f] or it **)

(** ** Frequent Pattern **)

(** The functions presented here are not from R source code, but
 * represent frequent programming pattern in its source code. **)

(** A basic C-like loop **)
Definition while A runs (S : state) (a : A) expr stat : result A :=
  if_success (expr S a) (fun S b =>
    if b then
      if_success (stat S a) (fun S a =>
        runs_while runs expr state S a)
    else
      return_success S a).

(** Looping through a list is a frequent pattern in R source code.
 * [fold_left_listSxp_gen] corresponds to the C code
 * [for (i = l, v = a; i != R_NilValue; i = CDR (i)) v = iterate ( *i, v); v]. **)
Definition fold_left_listSxp_gen A runs (S : state) (l : SExpRec_pointer) (a : A)
    (iterate : state -> A -> SExpRec_pointer -> SExpRec -> listsxp_struct -> result A) : result A :=
  while runs S (l, a) (fun S la =>
    let (l, a) := la in
    result_success S (decide (l <> R_NilValue)))
    (fun S la =>
      let (l, a) := la in
      if_defined S (read_SExp S l) (fun l_ =>
        if_defined S (get_listSxp l_) (fun l_list =>
          if_success (iterate S a l l_ l_list) (fun S a =>
            result_success S (list_cdrval l_list, a))))).

(* [fold_left_listSxp] corresponds to the C code
 * [for (i = l, v = a; i != R_NilValue; i = CDR (i)) v = iterate (CAR (i), TAG (i), v); v]. **)
Definition fold_left_listSxp A runs (S : state) (l : SExpRec_pointer) (a : A)
    (iterate : state -> A -> SExpRec_pointer -> SExpRec_pointer -> result A) : result A :=
  fold_left_listSxp_gen runs S l a (fun S a _ _ l_list =>
    iterate S a (list_carval l_list) (list_tagval l_list)).


(** ** memory.c **)

(** The function names of this section corresponds to the function names
 * in the file src/main/memory.c. **)

Definition cons (S : state) (car cdr : SExpRec_pointer) : state * SExpRec_pointer :=
  let e_ :=
    make_SExpRec (build_SExpRecHeader ListSxp R_NilValue)
      (make_ListSxp_struct car cdr R_NilValue) in
  alloc_SExp S e_.

Definition allocList S (n : nat) : state * SExpRec_pointer :=
  let fix aux S n p :=
    match n with
    | 0 => (S, p)
    | S n =>
      let (S, p) := aux S n p in
      cons S R_NilValue p
  in aux S n R_NilValue.


(** ** match.c **)

(** The function names of this section corresponds to the function names
 * in the file src/main/match.c. **)

Definition psmatch s1 s2 exact :=
  if exact then
    decide (s1 = s2)
  else
    String.prefix s1 s2.

Definition pmatch (S : state) (formal tag : SExpRec_pointer) exact : result bool :=
  let get_name str :=
    if_defined S (read_SExp S str) (fun str_ =>
      match type str_ with
      | SymSxp =>
        result_success S (* CHAR(PRINTNAME(str)) *)
      | CharSxp =>
        result_success S (* CHAR(str) *)
      | StrSxp =>
        result_success S (* translateChar(STRING_ELT(str, 0)) *)
      | _ =>
        result_error S "[pmatch] invalid partial string match."
      end) in
    if_success (get_name formal) (fun S f =>
      if_success (get_name tag) (fun S t =>
        psmatch f t exact)).

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
Definition set_argused (used : ¿nat?) e_ :=
  set_gp ?.

Definition argused e_ :=
  gp ?.

Definition set_missing (m : bool) e_ :=
  set_gp ?.

Definition missing e_ :=
  gp ?.

Definition matchArgs_first runs (S : state)
    (formals actuals : SExpRec_pointer) : result (list nat) :=
  if_success (fold_left_listSxp S formals (actuals, nil) (fun S a_fargusedrev _ f_tag =>
    let (a, fargusedrev) := a_fargusedrev in
    let ftag_name = (* CHAR(PRINTNAME(f_tag)) *) in
    let continuation S fargusedi :=
      if_defined S (read_SExp S a) (fun a_ =>
        if_defined S (get_listSxp a_) (fun a_list =>
          result_success S (list_cdrval a_list, fargusedi :: fargusedrev))) in
    ifb f_tag <> R_DotsSymbol /\ f_tag <> R_NilValue then
      if_success (fold_left_listSxp_gen S supplied 0 (fun S fargusedi b b_ b_list =>
        let b_tag := list_tagval b_list in
        let btag_name = (* CHAR(PRINTNAME(b_tag)) *) in
        ifb b_tag <> R_NilValue /\ ftag_name = btag_name then
          ifb fargusedi = 2 then
            result_error S "[matchArgs_first] formal argument matched by multiple actual arguments."
          else ifb argused b_ then
            result_error S "[matchArgs_first] actual argument matches several formal arguments."
          else
            set_car S (list_carval b_list) a (fun S =>
              if_success
                (ifb list_carval b <> R_MissingArg then
                  map_pointer S a (set_missing false)
                else result_success S tt) (fun S _ =>
                map_pointer S b (set_argused 2) (fun S =>
                  result_success S 2)))
        else
          result_success S fargusedi))
        continuation
    else continuation S 0))
    (fun S a_fargusedrev =>
      let (a, fargusedrev) := a_fargusedrev in
      result_success S (List.rev fargusedrev)).

Definition matchArgs_second runs (S : state)
    (actuals formals : SExpRec_pointer) fargused : result SExpRec_pointer :=
  if_success (fold_left_listSxp S formals (actuals, fargused, R_NilValue, false) (fun S a_fargused_dots_seendots _ f_tag =>
    let (a, fargused, dots, seendots) := a_fargused_dots_seendots in
    match fargused with
    | nil => result_impossible S "[matchArgs_second] fargused has an unexpected size."
    | fargusedi :: fargused =>
      let continuation S dots seendots :=
        if_defined S (read_SExp S a) (fun a_ =>
          if_defined S (get_listSxp a_) (fun a_list =>
            result_success S (list_cdrval a_list, fargused, dots, seendots))) in
      ifb fargusedi = 0 then
        ifb f_tag = R_DotsSymbol /\ ~ seendots then
          continuation S a true
        else
          if_success (fold_left_listSxp_gen S supplied fargusedi (fun S fargusedi b b_ b_list =>
            let b_tag := list_tagval b_list in
            ifb argused b_ /\ b_tag <> R_NilValue then
              if_success (pmatch S f_tag b_tag seendots) (fun S pmatch =>
                if pmatch then
                  if argused b_ then
                    result_error "[matchArgs_second] actual argument matches several formal arguments."
                  else ifb fargusedi = 1 then
                    result_error S "[matchArgs_second] formal argument matched by multiple actual arguments."
                  else
                    (** Warning about partial arguments: should we ignore this part? **)
                    set_car S (list_carval b_list) a (fun S =>
                      if_success
                        (ifb list_carval b <> R_MissingArg then
                          map_pointer S a (set_missing false)
                        else result_success S tt) (fun S _ =>
                        map_pointer S b (set_argused 1) (fun S =>
                          result_success S 1)))
                else result_success S fargusedi)
            else
              result_success S fargusedi))
            (fun S fargusedi =>
              continuation S dots seendots)
      else continuation S dots seendots
    end)
    (fun S a_fargused_dots_seendots =>
      let (a, fargused, dots, seendots) := a_fargused_dots_seendots in
      result_success S dots).

Definition matchArgs_third runs (S : state)
    (formals actuals supplied : SExpRec_pointer) : result unit :=
  if_success
    (while runs S (formals, actuals, supplied, false) (fun S f_a_b_seendots =>
      let (f, a, b, seendots) := f_a_b_seendots in
      result_success S (decide (f <> R_NilValue /\ b <> R_NilValue /\ ~ seendots)))
      (fun S f_a_b_seendots =>
        let (f, a, b, seendots) := f_a_b_seendots in
        if_defined S (read_SExp S f) (fun f_ =>
          if_defined S (get_listSxp f_) (fun f_list =>
            if_defined S (read_SExp S a) (fun a_ =>
              if_defined S (get_listSxp a_) (fun a_list =>
                ifb list_tagval f_list = R_DotsSymbol then
                  result_success S (list_cdrval f_list, list_cdrval a_list, b, true)
                else ifb list_carval a_list <> R_MissingArg then
                  result_success S (list_cdrval f_list, list_cdrval a_list, b, seendots)
                else
                  if_defined S (read_SExp S b) (fun b_ =>
                    if_defined S (get_listSxp b_) (fun b_list =>
                      ifb argused b_ \/ list_tagval b_list <> R_NilValue then
                        result_success S (f, a, list_cdrval b_list, seendots)
                      else
                        set_car S (list_carval b_list) a (fun S =>
                          if_success
                            (ifb list_carval b <> R_MissingArg then
                              map_pointer S a (set_missing false)
                            else result_success S tt) (fun S _ =>
                              result_success S (list_cdrval f_list, list_cdrval a_list, list_cdrval b_list, seendots)))))))))))
    (fun S f_a_b_seendots =>
      result_success S tt).

Definition matchArgs_dots runs (S : state)
    (dots supplied : SExpRec_pointer) : result unit :=
  map_pointer S dots (set_missing false) (fun S =>
    if_success (fold_left_listSxp S supplied 0 (fun S i a _ =>
      if_option S (read_SExp S a) (fun a_ =>
        if argused a_ then
          result_success S (1 + i)
        else
          result_success S i))
      (fun S i =>
        ifb i = 0 then
          result_success S tt
        else
          let (S, a) := allocList S i in
          map_pointer S (set_type DotSxp) (fun S =>
            if_success (fold_left_listSxp_gen runs S supplied a (fun S f b b_ b_list =>
              if argused b_ then
                result_success S f
              else
                if_defined S (read_SExp S f) (fun f_ =>
                  if_defined S (get_listSxp f_) (fun f_list =>
                    let f_list := {|
                        list_carval := list_carval b_list ;
                        list_cdrval := list_cdrval f_list ;
                        list_tagval := list_tagval b_list
                      |} in
                    let f_ := {|
                        SExpRec_header := SExpRec_header f_ ;
                        SExpRec_data := f_list
                      |} in
                    if_defined S (write_SExp S f f_) (fun S =>
                      result_success S (list_cdrval f_list)))))
              (fun S _ =>
                set_car S a dots (fun S =>
                  result_success S tt))))))).

Definition matchArgs_check runs (S : state)
    (supplied : SExpRec_pointer) : result unit :=
  if_success (fold_left_listSxp_gen runs S supplied false (fun S acc b b_ b_list =>
    result_success S (acc || argused b_))
    (fun S b =>
      if b then
        result_error S "[matchArgs_check] Unused argument(s)."
      else
        result_success S tt).


Definition matchArgs runs (S : state)
    (formals supplied call : SExpRec_pointer) : result SExpRec_pointer :=
  if_success (fold_left_listSxp S formals (R_NilValue, 0) (fun S actuals_argi _ _ =>
      let (actuals, argi) := actuals_argi in
      let (S, actuals) := cons (R_MissingArg, actuals) in
      (actuals, 1 + argi)))
    (fun S actuals_argi =>
      let (actuals, argi) := actuals_argi in
      if_success (fold_left_listSxp S supplied tt (fun S _ b _ =>
        map_pointer S b (set_argused false) (fun S =>
          result_success S tt))))
        (fun S _ =>
          if_success (matchArgs_first runs S formals actuals) (fun S fargused =>
            if_success (matchArgs_second runs S actuals formals fargused) (fun S dots =>
              if_success (matchArgs_third runs S formals actuals supplied) (fun S _ =>
                ifb dots <> R_NilValue then
                  if_success (matchArgs_dots runs runs S dots supplied) (fun S _ =>
                    return_success S actuals)
                else
                  if_success (matchArgs_check runs S supplied) (fun S _ =>
                    return_success S actuals)))))).


(** ** eval.c **)

(** The function names of this section corresponds to the function names
* in the file src/main/eval.c. **)

(** The function [forcePromise] evaluates a promise if needed. **)
Definition forcePromise runs (S : state) (e : SExpRec_pointer) : result SExpRec_pointer :=
  if_defined S (read_SExp S e) (fun e_ =>
    if_defined S (get_promSxp e_) (fun e_prom =>
      ifb prom_value e_prom = R_UnboundValue then
        (* FIXME: Do we want to catch the PRSEEN part? *)
        runs_eval runs S (prom_expr e_prom) (prom_env e_prom)
      else result_success S e)).

Definition applyClosure runs (S : state)
    (call op arglist rho suppliedvars : SExpRec_pointer) : result SExpRec_pointer :=
  if_defined S (read_SExp S rho) (fun rho_ =>
    ifb type rho_ <> EnvSxp then
      result_impossible S "[applyClosure] ‘rho’ must be an environment."
    else
      if_defined S (read_SExp S op) (fun op_ =>
        if_defined S (get_cloSxp op_) (fun op_clo =>
          let formals := clo_formals op_clo in
          let savedrho := clo_env op_clo in
          if_success (matchArgs runs S formals arglist call) (fun S actuals =>
            (* TODO, line 1507 of eval.c *)
            result_not_implemented "[applyClosure]")))).

(** The function [eval] evaluates its argument to an unreducible value. **)
Definition eval runs (S : state) (e rho : SExpRec_pointer) : result SExpRec_pointer :=
  if_defined S (read_SExp S e) (fun e_ =>
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
      if_defined S (write_SExp S e (set_named_plural e_)) (fun S =>
        result_success S e)
    | _ =>
      if_defined S (read_SExp S rho) (fun rho_ =>
        ifb type rho_ <> EnvSxp then
          result_impossible S "[eval] ‘rho’ must be an environment."
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
              result_error "[eval] ‘...’ used in an incorrect context."
            else
              (* TODO: https://github.com/wch/r-source/blob/trunk/src/main/eval.c#L626
               * I think that in essence, we are fetching the value of the symbol in the
               * environment, then evaluating it if we get a promise. **)
              (** There is just a story about ddfindVar vs findVar which I don’t yet
               * understand (depending on the general purpose field). I need to investigate
               * about these two functions. **)
              result_not_implemented "[eval] Symbols (TODO)"
          | PromSxp =>
            if_defined S (get_promSxp e_) (fun e_prom =>
              ifb prom_value e_prom = R_UnboundValue then
                if_success (forcePromise runs S e) (fun S e =>
                  result_success S e)
              else result_success S e)
          | LangSxp =>
            if_defined S (get_listSxp e_) (fun e_list =>
              let car := list_carval e_list in
              if_defined S (read_SExp S car) (fun car_ =>
                if_success
                  (ifb type car_ = SymSxp then
                     (* TODO: findFun3 — in essence, this is just a variable look-up. *)
                     result_not_implemented "[eval] findFun3 (TODO)"
                   else runs_eval runs S car rho) (fun S op =>
                  if_defined S (read_SExp S op) (fun op_ =>
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
                    end))))
          | DotSxp => result_impossible S "[eval] ‘...’ used in an incorrect context"
          | _ => result_error S "[eval] Type unimplemented in the R source code."
          end)
    end).


(** * Closing the loop **)

Fixpoint runs max_step : runs_type :=
  match max_step with
  | O => {|
      runs_while := fun _ S _ _ _ => result_bottom S ;
      runs_eval := fun S _ _ => result_bottom S
    |}
  | S max_step =>
    let wrap {A : Type} (f : runs_type -> A) : A :=
      f (runs max_step) in {|
      runs_while := wrap while ;
      runs_eval := wrap eval
    |}
  end.


(** * Proofs **)

(** It would be nice to prove that the read-eval-print-loop can not
* return a [result_impossible]. **)

(** The property we want to eventually prove is that if [eval] returns
* a result, then the C function eval does similarly. **)

