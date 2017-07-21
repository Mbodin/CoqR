(** Reval.
* Describes how R evaluates expressions.
* The content of this file is the Coq equivalent of the file src/main/eval.c from R source code. **)

Set Implicit Arguments.
Require Export Monads.

(** * Global structure of the interpreter **)

(** A structure to deal with infinite execution (which is not allowed in Coq). Inspired from JSCert. **)
Record runs_type : Type := runs_type_intro {
    runs_fold_left_listSxp : forall A, state -> SExpRec_pointer -> A ->
      (state -> A -> SExpRec_pointer -> SExpRec_pointer -> result A) -> result A ;
    runs_eval : state -> SExpRec_pointer -> SExpRec_pointer -> result SExpRec_pointer
  }.


(** * Interpreter functions **)

(** The C language performs a lot of pointer deferentiation. As a
* convention, we write [p_] for the object referenced by the pointer [p]
* in this section, and [p_f] for the field [f] or it, typically [p_sym]
* for its [symSxp_struct] part and so on. **)

(** ** Frequent Pattern **)

(** The functions presented here are not from R source code, but
 * represent frequent programming pattern in its source code. **)

(** Looping through a list is a frequent pattern in R source code.
 * [fold_left_listSxp] corresponds to the C code
 * [for (i = l, v = a; i != R_NilValue; i = CDR (i)) v = iterate (CAR (i), TAG (i), v); v]. **)
Definition fold_left_listSxp A runs (S : state) (l : SExpRec_pointer) (a : A)
    (iterate : state -> A -> SExpRec_pointer -> SExpRec_pointer -> result A) : result A :=
  ifb l = None then
    result_success S a
  else
    if_defined S (read_SExp S l) (fun l_ =>
      if_defined S (get_listSxp l_) (fun l_list =>
        if_success (iterate S a (list_carval l_list) (list_tagval l_list)) (fun S a =>
          runs_fold_left_listSxp runs S (list_cdrval l_list) a iterate))).

(** ** memory.c **)

(** The function names of this section corresponds to the function names
* in the file src/main/memory.c. **)

Definition CONS_NR (S : state) (car cdr : SExpRec_pointer) : state * SExpRec_pointer :=
  let e_ := make_SExpRec (build_SExpRecHeader ListSxp None) (make_ListSxp_struct car cdr None) in
  alloc_SExp S e_.

(* Question: there is a point at which there is just too much details.
 * There is no point in translating the entire R source code,
 * even if we are skipping R functions.
 * It is fine to understand what a given function does without translating
 * exactly its source code. *)


(** ** match.c **)

(** The function names of this section corresponds to the function names
* in the file src/main/match.c. **)

(* Understanding C code can be trikky. Here are some hints.
* psmatch (s1, s2, TRUE) is exactly s1 = s2
* psmatch (s1, s2, FALSE) is exactly String.prefix s1 s2 *)

(** The function [matchArgs] matches the arguments supplied to a given
* call with the formal, expected arguments.
* This is more complex as it may seem as arguments in R can be named
* (and thus provided in any order), or can be ‘...’.
* The algorithm presented in this function is thus crucial to understand
* the semantics of function calls in R.
* It is furthermore rather complicated. **)
Definition matchArgs runs (S : state)
    (formals supplied call : SExpRec_pointer) : SExpRec_pointer :=
  (* TODO: fold_left_listSxp *)
  .

(** ** eval.c **)

(** The function names of this section corresponds to the function names
* in the file src/main/eval.c. **)

(** The function [forcePromise] evaluates a promise if needed. **)
Definition forcePromise runs (S : state) (e : SExpRec_pointer) : result SExpRec_pointer :=
  if_defined S (read_SExp S e) (fun e_ =>
    if_defined S (get_promSxp e_) (fun e_prom =>
      If prom_value e_prom = R_UnboundValue then
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
          (* TODO : formals *)
          result_not_implemented "[applyClosure]"))).

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
      if_defined S (write_SExp S e (set_named e_)) (fun S =>
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
      runs_fold_left_listSxp := fun _ S _ _ _ => result_bottom S ;
      runs_eval := fun S _ _ => result_bottom S
    |}
  | S max_step =>
    let wrap {A : Type} (f : runs_type -> A) : A :=
      f (runs max_step) in {|
      runs_fold_left_listSxp := wrap fold_left_listSxp ;
      runs_eval := wrap eval
    |}
  end.


(** * Proofs **)

(** It would be nice to prove that the read-eval-print-loop can not
* return a [result_impossible]. **)

(** The property we want to eventually prove is that if [eval] returns
* a result, then the C function eval does similarly. **)

