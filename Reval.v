(** Reval.
* Describes how R evaluates expressions.
* The content of this file is the Coq equivalent of File eval.c, which can be for instance found in https://github.com/wch/r-source/blob/trunk/src/main/eval.c **)

Require Export Rinternals Monads.

(* TODO: A JSCert’s runs_type, as the following function won’t necessary terminate. *)

(** The eval function of https://github.com/wch/r-source/blob/trunk/src/main/eval.c#L538 **)
Fixpoint eval (S : state) (e rho : SExpRec_pointer) : option (state * SExpRec_pointer) :=
  if_defined (read_SExp S e) (fun exp =>
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
      Some (write_SExp S (e set_named exp), e)
    | _ =>
      if_defined (read_SExp S rho) (fun env =>
        match type exp with
        | EnvSxp =>
          match type exp with
          | BcodeSxp =>
            (** See https://github.com/wch/r-source/blob/trunk/src/main/eval.c#L3543
             * for a definition of this bytecode, and
             * https://github.com/wch/r-source/blob/trunk/src/main/eval.c#L5966
             * for the evaluator.
             * We do not consider byte code for now in this formalisation. **)
            None 
          | SymSxp =>
            (* TODO: https://github.com/wch/r-source/blob/trunk/src/main/eval.c#L626
             * I think that in essence, we are fetching the value of the symbol in the
             * environment, then evaluating it if we get a promise. **)
            (** There is just a story about ddfindVar vs findVar which I don’t yet
             * understand (depending on the general purpose field). I need to investigate
             * about these two functions. **)
          | PromSxp =>
            if_defined (get_promSxp e) (fun p =>
              Some (
                If prom_value p = R_UnboundValue then
                  forcePromise S e
                else S,
                p)
          | LangSxp =>
            if_defined (get_listSxp e) (fun l =>
              if_defined (read_SExp S (list_carval l)) (fun car =>
                if_returns
                  (If type car = SymSxp then
                     (* TODO: findFun3 — in essence, this is just a variable look-up. *)
                   else eval car rho) (fun S op =>
                  if_defined (read_SExp S op) (fun opp =>
                    match type opp with
                    | SpecialSxp =>
                      (* TODO: This is basically a direct call to PRIMFUN. *)
                    | BuiltinSxp =>
                      (* TODO: This is basically a call to PRIMFUN after evaluating the argument list. *)
                    | CloSxp =>
                      (* TODO: https://github.com/wch/r-source/blob/trunk/src/main/eval.c
                         applyClosure(e, op, promiseArgs(CDR(e), rho), rho, R_NilValue);
                       *)
                    | _ => None
                    end))))
          | DotSxp =>
            None
          | _ => None
          end
        | _ => None
        end)
    end)

with forcePromise (S : state) (e : SExpRec_pointer) : option (state * SExpRec_pointer) :=
  if_defined (read_SExp S e) (fun exp =>
    if_defined (get_promSxp e) (fun p =>
      If prom_value p = R_UnboundValue then
        eval S (prom_expr p) (prom_env p)
      else Some (S, e))).

(** The property we want to eventually prove is that if [eval] returns
  a result, then the C function eval does similarly. **)

