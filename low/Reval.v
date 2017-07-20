(** Reval.
* Describes how R evaluates expressions.
* The content of this file is the Coq equivalent of the file src/main/eval.c. **)

Set Implicit Arguments.
Require Export Monads.

(** * Global structure of the interpreter **)

(** A structure to deal with infinite execution (which is not allowed in Coq). Inspired from JSCert. **)
Record runs_type : Type := runs_type_intro {
    runs_eval : state -> SExpRec_pointer -> SExpRec_pointer -> result SExpRec_pointer
  }.


(** * Interpreter functions **)

Definition forcePromise runs (S : state) (e : SExpRec_pointer) : result SExpRec_pointer :=
  if_defined S (read_SExp S e) (fun exp =>
    if_defined S (get_promSxp exp) (fun p =>
      If prom_value p = R_UnboundValue then
        runs_eval runs S (prom_expr p) (prom_env p)
      else result_success S e)).

(** The eval function of https://github.com/wch/r-source/blob/trunk/src/main/eval.c#L538 **)
Definition eval runs (S : state) (e rho : SExpRec_pointer) : result SExpRec_pointer :=
  if_defined S (read_SExp S e) (fun exp =>
    match type exp with
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
      if_defined S (write_SExp S e (set_named exp)) (fun S =>
        result_success S e)
    | _ =>
      if_defined S (read_SExp S rho) (fun env =>
        match type exp with
        | EnvSxp =>
          match type exp with
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
            if_defined S (get_promSxp exp) (fun p =>
              ifb prom_value p = R_UnboundValue then
                if_success (forcePromise runs S e) (fun S e =>
                  result_success S e)
              else result_success S e)
          | LangSxp =>
            if_defined S (get_listSxp exp) (fun l =>
              let pcar := list_carval l in
              if_defined S (read_SExp S pcar) (fun car =>
                if_success
                  (ifb type car = SymSxp then
                     (* TODO: findFun3 — in essence, this is just a variable look-up. *)
                     result_not_implemented "[eval] findFun3 (TODO)"
                   else runs_eval runs S pcar rho) (fun S op =>
                  if_defined S (read_SExp S op) (fun opp =>
                    match type opp with
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
          | DotSxp => result_error S "[eval] ‘...’ used in an incorrect context"
          | _ => result_error S "[eval] Type unimplemented in the R source code."
          end
        | _ => result_error S "[eval] ‘rho’ must be an environment."
        end)
    end).

(** The property we want to eventually prove is that if [eval] returns
  a result, then the C function eval does similarly. **)


(** * Closing the loop **)

Fixpoint runs max_step : runs_type :=
  match max_step with
  | O => {|
      runs_eval := fun S _ _ => result_bottom S
    |}
  | S max_step =>
    let wrap {A : Type} (f : runs_type -> A) : A :=
      f (runs max_step) in {|
      runs_eval := wrap eval
    |}
  end.

