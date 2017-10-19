(** ParserUtils
 * Types and useful functions to be used in the parser. **)

open Low

type 'a monad_type = globals -> runs_type -> state -> 'a

(** The main type carried in the parser. **)
type token_type = sExpRec_pointer result monad_type


(** * Wrappers **)

let no_globals (f : runs_type -> state -> 'a) : 'a monad_type = fun _ -> f
let no_runs (f : globals -> state -> 'a) : 'a monad_type = fun g _ -> f g
let only_state (f : state -> 'a) : 'a monad_type = fun _ _ -> f

(** This function is inspired from the [install_and_save] function
  * of the original interpreter. It takes into advantage the fact
  * that ocamllex is functional: its behaviour is exactly the same
  * than the install function. It here serves as a wrapper, to
  * change the order of the arguments of [install]. **)
let install_and_save str : token_type = fun g r s ->
  install g r s (Print.string_to_char_list str)

let null : token_type = fun _ _ s -> Result_success (s, nULL)


(** * Composing Functions **)

let bind (comp : token_type) (cont : (sExpRec_pointer -> 'a result) monad_type) : 'a result monad_type =
  fun g r s -> if_success (comp g r s) (cont g r)

let shift (f : 'a -> 'b monad_type) : ('a -> 'b) monad_type =
  fun g r s x -> f x g r s

(** Compose a [token_type] function to a simple function which
 * only cares about its return value. **)
let lift1 f comp : token_type =
  bind comp (only_state f)
let lift2 f comp1 comp2 : token_type =
  bind comp1 (shift (fun res1 ->
    bind comp2 (only_state (fun s res2 ->
      f s res1 res2))))
let lift3 f comp1 comp2 comp3 : token_type =
  bind comp1 (shift (fun res1 ->
    bind comp2 (shift (fun res2 ->
      bind comp3 (only_state (fun s res3 ->
        f s res1 res2 res3))))))
let lift4 f comp1 comp2 comp3 comp4 : token_type =
  bind comp1 (shift (fun res1 ->
    bind comp2 (shift (fun res2 ->
      bind comp3 (shift (fun res3 ->
        bind comp4 (only_state (fun s res4 ->
          f s res1 res2 res3 res4))))))))
let lift5 f comp1 comp2 comp3 comp4 comp5 : token_type =
  bind comp1 (shift (fun res1 ->
    bind comp2 (shift (fun res2 ->
      bind comp3 (shift (fun res3 ->
        bind comp4 (shift (fun res4 ->
          bind comp5 (only_state (fun s res5 ->
            f s res1 res2 res3 res4 res5))))))))))


(** * Functions from gram.y **)

(** The function [R_atof] has not been formalised. We instead rely
 * on the OCaml functions [*_of_string]. **)
let mkFloat str : token_type = fun _ _ s ->
  let (s, e) = scalarReal s (float_of_string str) in
  Result_success (s, e)
let mkInt str : token_type = fun _ _ s ->
  let (s, e) = scalarInteger s (int_of_string str) in
  Result_success (s, e)
let mkComplex str : token_type = fun _ _ s ->
  let c = {
      rcomplex_r = 0. ;
      rcomplex_i = float_of_string str
    } in
  let (s, e) = alloc_vector_cplx s c in
  Result_success (s, e)

