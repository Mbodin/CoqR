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
Definition while A runs S (a : A) expr stat : result A :=
  if_success (expr S a) (fun S b =>
    if b : bool then
      if_success (stat S a) (fun S a =>
        runs_while runs S a expr stat)
    else
      result_success S a).

(** Looping through a list is a frequent pattern in R source code.
 * [fold_left_listSxp_gen] corresponds to the C code
 * [for (i = l, v = a; i != R_NilValue; i = CDR (i)) v = iterate ( *i, v); v]. **)
Definition fold_left_listSxp_gen A runs S (l : SExpRec_pointer) (a : A)
    (iterate : state -> A -> SExpRec_pointer -> SExpRec -> ListSxp_struct -> result A) : result A :=
  if_success
    (while runs S (l, a) (fun S la =>
      let (l, a) := la in
      result_success S (decide (l <> R_NilValue)))
      (fun S la =>
        let (l, a) := la in
        read_as_list S l (fun l_ l_list =>
          if_success (iterate S a l l_ l_list) (fun S a =>
            result_success S (list_cdrval l_list, a)))))
    (fun S la =>
      let (l, a) := la in
      result_success S a).

(* [fold_left_listSxp] corresponds to the C code
 * [for (i = l, v = a; i != R_NilValue; i = CDR (i)) v = iterate (CAR (i), TAG (i), v); v]. **)
Definition fold_left_listSxp A runs S (l : SExpRec_pointer) (a : A)
    (iterate : state -> A -> SExpRec_pointer -> SExpRec_pointer -> result A) : result A :=
  fold_left_listSxp_gen runs S l a (fun S a _ _ l_list =>
    iterate S a (list_carval l_list) (list_tagval l_list)).


(** ** memory.c **)

(** The function names of this section corresponds to the function names
 * in the file src/main/memory.c. **)

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
Definition NewEnvironment runs S (namelist valuelist rho : SExpRec_pointer) : result SExpRec_pointer :=
  let (S, newrho) := alloc_SExp S (make_SExpRec_env R_NilValue valuelist rho) in
  if_success
    (while runs S (valuelist, namelist) (fun S v_n =>
      let (v, n) := v_n in
      result_success S (decide (v <> R_NilValue /\ n <> R_NilValue)))
      (fun S v_n =>
        let (v, n) := v_n in
        read_as_list S v (fun v_ v_list =>
          read_as_list S n (fun n_ n_list =>
            let v_list := set_tag_list (list_tagval n_list) v_list in
            let v_ := {|
                NonVector_SExpRec_header := v_ ;
                NonVector_SExpRec_data := v_list
              |} in
            if_defined S (write_SExp S v v_) (fun S =>
              result_success S (list_cdrval v_list, list_cdrval n_list))))))
    (fun S _ =>
      result_success S newrho).

(** Similarly, there is a macro renaming [mkPROMISE] to [Rf_mkPROMISE]. **)
Definition mkPROMISE S (expr rho : SExpRec_pointer) : result SExpRec_pointer :=
  map_pointer S set_named_plural expr (fun S =>
    let (S, s) := alloc_SExp S (make_SExpRec_prom R_NilValue R_UnboundValue expr rho) in
    result_success S s).


(** ** match.c **)

(** The function names of this section corresponds to the function names
 * in the file src/main/match.c. **)

Definition psmatch s1 s2 exact :=
  if exact : bool then
    decide (s1 = s2)
  else
    String.prefix s1 s2.

Definition pmatch S (formal tag : SExpRec_pointer) exact : result bool :=
  let get_name str :=
    if_defined S (read_SExp S str) (fun str_ =>
      match type str_ with
      | SymSxp =>
        if_is_sym S str_ (fun str_ str_sym =>
          read_as_VectorChar S (sym_pname str_sym) (fun str_name_ =>
            result_success S (list_to_string str_name_)))
      | CharSxp =>
        if_defined S (get_VectorChar str_) (fun str_ =>
          result_success S (list_to_string str_))
      | StrSxp =>
        result_not_implemented "[pmatch] translateChar(STRING_ELT(str, 0))"
      | _ =>
        result_error S "[pmatch] invalid partial string match."
      end) in
    if_success (get_name formal) (fun S f =>
      if_success (get_name tag) (fun S t =>
        result_success S (psmatch f t exact))).

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

Definition matchArgs_first runs S
    (formals actuals supplied : SExpRec_pointer) : result (list nat) :=
  if_success (fold_left_listSxp runs S formals (actuals, nil) (fun S a_fargusedrev _ f_tag =>
    let (a, fargusedrev) := a_fargusedrev in
    read_as_sym S f_tag (fun f_tag_ f_tag_sym =>
      read_as_VectorChar S (sym_pname f_tag_sym) (fun f_tag_sym_name_ =>
        let ftag_name := list_to_string f_tag_sym_name_ in
        let continuation S fargusedi :=
          read_as_list S a (fun a_ a_list =>
            result_success S (list_cdrval a_list, fargusedi :: fargusedrev)) in
        ifb f_tag <> R_DotsSymbol /\ f_tag <> R_NilValue then
          if_success (fold_left_listSxp_gen runs S supplied 0 (fun S fargusedi b b_ b_list =>
            let b_tag := list_tagval b_list in
            read_as_sym S b_tag (fun b_tag_ b_tag_sym =>
              read_as_VectorChar S (sym_pname b_tag_sym) (fun b_tag_sym_name_ =>
                let btag_name := list_to_string b_tag_sym_name_ in
                ifb b_tag <> R_NilValue /\ ftag_name = btag_name then
                  ifb fargusedi = 2 then
                    result_error S "[matchArgs_first] formal argument matched by multiple actual arguments."
                  else ifb argused b_ = 2 then
                    result_error S "[matchArgs_first] actual argument matches several formal arguments."
                  else
                    set_car S (list_carval b_list) a (fun S =>
                      if_success
                        (ifb list_carval b_list <> R_MissingArg then
                          map_pointer S (set_missing 1 ltac:(nbits_ok)) a (fun S =>
                            result_success S tt)
                        else result_success S tt) (fun S _ =>
                        map_pointer S (set_argused 2 ltac:(nbits_ok)) b (fun S =>
                          result_success S 2)))
                else
                  result_success S fargusedi))))
            continuation
        else continuation S 0))))
    (fun S a_fargusedrev =>
      let (a, fargusedrev) := a_fargusedrev in
      result_success S (List.rev fargusedrev)).

Definition matchArgs_second runs S
    (actuals formals supplied : SExpRec_pointer) fargused : result SExpRec_pointer :=
  if_success (fold_left_listSxp runs S formals (actuals, fargused, R_NilValue, false) (fun S a_fargused_dots_seendots _ f_tag =>
    let '(a, fargused, dots, seendots) := a_fargused_dots_seendots in
    match fargused with
    | nil => result_impossible S "[matchArgs_second] fargused has an unexpected size."
    | fargusedi :: fargused =>
      let continuation S dots seendots :=
        read_as_list S a (fun a_ a_list =>
            result_success S (list_cdrval a_list, fargused, dots, seendots)) in
      ifb fargusedi = 0 then
        ifb f_tag = R_DotsSymbol /\ ~ seendots then
          continuation S a true
        else
          if_success (fold_left_listSxp_gen runs S supplied fargusedi (fun S fargusedi b b_ b_list =>
            let b_tag := list_tagval b_list in
            ifb argused b_ <> 2 /\ b_tag <> R_NilValue then
              if_success (pmatch S f_tag b_tag seendots) (fun S pmatch =>
                if pmatch then
                  ifb argused b_ <> 0 then
                    result_error S "[matchArgs_second] actual argument matches several formal arguments."
                  else ifb fargusedi = 1 then
                    result_error S "[matchArgs_second] formal argument matched by multiple actual arguments."
                  else
                    (** Warning about partial arguments: should we ignore this part? **)
                    set_car S (list_carval b_list) a (fun S =>
                      if_success
                        (ifb list_carval b_list <> R_MissingArg then
                          map_pointer S (set_missing 0 ltac:(nbits_ok)) a (fun S =>
                            result_success S tt)
                        else result_success S tt) (fun S _ =>
                        map_pointer S (set_argused 1 ltac:(nbits_ok)) b (fun S =>
                          result_success S 1)))
                else result_success S fargusedi)
            else
              result_success S fargusedi))
            (fun S fargusedi =>
              continuation S dots seendots)
      else continuation S dots seendots
    end))
    (fun S a_fargused_dots_seendots =>
      let '(a, fargused, dots, seendots) := a_fargused_dots_seendots in
      result_success S dots).

Definition matchArgs_third runs S
    (formals actuals supplied : SExpRec_pointer) : result unit :=
  if_success
    (while runs S (formals, actuals, supplied, false) (fun S f_a_b_seendots =>
      let '(f, a, b, seendots) := f_a_b_seendots in
      result_success S (decide (f <> R_NilValue /\ b <> R_NilValue /\ ~ seendots)))
      (fun S f_a_b_seendots =>
        let '(f, a, b, seendots) := f_a_b_seendots in
        read_as_list S f (fun f_ f_list =>
          read_as_list S a (fun a_ a_list =>
            ifb list_tagval f_list = R_DotsSymbol then
              result_success S (list_cdrval f_list, list_cdrval a_list, b, true)
            else ifb list_carval a_list <> R_MissingArg then
              result_success S (list_cdrval f_list, list_cdrval a_list, b, seendots)
            else
              read_as_list S b (fun b_ b_list =>
                ifb argused b_ <> 0 \/ list_tagval b_list <> R_NilValue then
                  result_success S (f, a, list_cdrval b_list, seendots)
                else
                  set_car S (list_carval b_list) a (fun S =>
                    if_success
                      (ifb list_carval b_list <> R_MissingArg then
                        map_pointer S (set_missing 0 ltac:(nbits_ok)) a (fun S =>
                          result_success S tt)
                      else result_success S tt) (fun S _ =>
                        result_success S (list_cdrval f_list, list_cdrval a_list, list_cdrval b_list, seendots))))))))
    (fun S f_a_b_seendots =>
      result_success S tt).

Definition matchArgs_dots runs S
    (dots supplied : SExpRec_pointer) : result unit :=
  map_pointer S (set_missing 0 ltac:(nbits_ok)) dots (fun S =>
    if_success (fold_left_listSxp runs S supplied 0 (fun S i a _ =>
      if_defined S (read_SExp S a) (fun a_ =>
        ifb argused a_ = 0 then
          result_success S (1 + i)
        else
          result_success S i)))
      (fun S i =>
        ifb i = 0 then
          result_success S tt
        else
          let (S, a) := allocList S i in
          map_pointer S (set_type DotSxp) a (fun S =>
            if_success (fold_left_listSxp_gen runs S supplied a (fun S f b b_ b_list =>
              ifb argused b_ <> 0 then
                result_success S f
              else
                read_as_list S f (fun f_ f_list =>
                  let f_list := {|
                      list_carval := list_carval b_list ;
                      list_cdrval := list_cdrval f_list ;
                      list_tagval := list_tagval b_list
                    |} in
                  let f_ := {|
                      NonVector_SExpRec_header := NonVector_SExpRec_header f_ ;
                      NonVector_SExpRec_data := f_list
                    |} in
                  if_defined S (write_SExp S f f_) (fun S =>
                    result_success S (list_cdrval f_list)))))
              (fun S _ =>
                set_car S a dots (fun S =>
                  result_success S tt))))).

Definition matchArgs_check runs S
    (supplied : SExpRec_pointer) : result unit :=
  if_success (fold_left_listSxp_gen runs S supplied false (fun S acc b b_ b_list =>
    result_success S (decide (acc \/ argused b_ <> 0))))
    (fun S b =>
      if b : bool then
        result_error S "[matchArgs_check] Unused argument(s)."
      else
        result_success S tt).


Definition matchArgs runs S
    (formals supplied call : SExpRec_pointer) : result SExpRec_pointer :=
  if_success (fold_left_listSxp runs S formals (R_NilValue, 0) (fun S actuals_argi _ _ =>
      let (actuals, argi) := actuals_argi in
      let (S, actuals) := cons S R_MissingArg actuals in
      result_success S (actuals, 1 + argi)))
    (fun S actuals_argi =>
      let (actuals, argi) := actuals_argi in
      if_success (fold_left_listSxp runs S supplied tt (fun S _ b _ =>
        map_pointer S (set_argused 0 ltac:(nbits_ok)) b (fun S =>
          result_success S tt)))
        (fun S _ =>
          if_success (matchArgs_first runs S formals actuals supplied) (fun S fargused =>
            if_success (matchArgs_second runs S actuals formals supplied fargused) (fun S dots =>
              if_success (matchArgs_third runs S formals actuals supplied) (fun S _ =>
                ifb dots <> R_NilValue then
                  if_success (matchArgs_dots runs S dots supplied) (fun S _ =>
                    result_success S actuals)
                else
                  if_success (matchArgs_check runs S supplied) (fun S _ =>
                    result_success S actuals)))))).


(** ** envir.c **)

(** The function names of this section corresponds to the function names
* in the file src/main/envir.c. **)

Definition is_special_symbol e_ :=
  nth_bit 12 (gp e_) ltac:(nbits_ok).

Definition set_no_special_symbols (e_ : SExpRec) :=
  set_gp (write_nbit 12 (gp e_) ltac:(nbits_ok) true) e_.

Definition R_envHasNoSpecialSymbols runs S (env : SExpRec_pointer) : result bool :=
  read_as_env S env (fun env_ env_env =>
    (* A note about hashtabs commented out. *)
    fold_left_listSxp runs S (env_frame env_env) true (fun S b frame_car frame_tag =>
      if_defined S (read_SExp S frame_tag) (fun frame_tag_ =>
        if is_special_symbol frame_tag_ then
          result_success S false
        else result_success S b))).

Definition addMissingVarsToNewEnv (runs : runs_type) (S : state) (env addVars : SExpRec_pointer) : result unit :=
  ifb addVars = R_NilValue then
    result_success S tt
  else
    if_defined S (read_SExp S addVars) (fun addVars_ =>
      ifb type addVars_ = EnvSxp then
        result_error S "[addMissingVarsToNewEnv] Additional variables should be passed as a list."
      else
        if_is_list S addVars_ (fun addVars_ addVars_list =>
          if_success
            (fold_left_listSxp_gen runs S (list_cdrval addVars_list) addVars
              (fun S aprev a a_ a_list =>
                result_success S a))
            (fun S aprev =>
              read_as_env S env (fun env_ env_env =>
                set_cdr S (env_frame env_env) aprev (fun S =>
                  let env_env := {|
                      env_frame := addVars ;
                      env_enclos := env_enclos env_env
                    |} in
                  let env_ := {|
                      NonVector_SExpRec_header := env_ ;
                      NonVector_SExpRec_data := env_env
                    |} in
                  if_defined S (write_SExp S env env_) (fun S =>
                    fold_left_listSxp_gen runs S (list_cdrval addVars_list) tt (fun S _ _ end_ end_list =>
                      let end_tag := list_tagval end_list in
                      if_success
                        (while runs S (addVars, addVars, R_NilValue) (fun S addVars_s_sprev =>
                          let '(addVars, s, sprev) := addVars_s_sprev in
                          result_success S (decide (s <> env)))
                          (fun S addVars_s_sprev =>
                            let '(addVars, s, sprev) := addVars_s_sprev in
                            read_as_list S s (fun s_ s_list =>
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
                                  if_defined S (write_SExp S env env_) (fun S =>
                                    result_success S (list_cdrval s_list, list_cdrval s_list, sprev))
                                else
                                  set_cdr S (list_cdrval s_list) sprev (fun S =>
                                    result_success S (addVars, list_cdrval s_list, sprev))
                              else result_success S (addVars, list_cdrval s_list, s))))
                        (fun S _ =>
                           result_success S tt)))))))).


(** ** eval.c **)

(** The function names of this section corresponds to the function names
* in the file src/main/eval.c. **)

(** The function [forcePromise] evaluates a promise if needed. **)
Definition forcePromise runs S (e : SExpRec_pointer) : result SExpRec_pointer :=
  read_as_prom S e (fun e_ e_prom =>
    ifb prom_value e_prom = R_UnboundValue then
      let cont S :=
        map_pointer S (set_gp (@nat_to_nbits 16 1 ltac:(nbits_ok))) e (fun S =>
          if_success (runs_eval runs S (prom_expr e_prom) (prom_env e_prom)) (fun S val =>
            map_pointer S (set_gp (@nat_to_nbits 16 0 ltac:(nbits_ok))) e (fun S =>
              map_pointer S set_named_plural val (fun S =>
                read_as_prom S e (fun e_ e_prom =>
                  let e_prom := {|
                      prom_value := val ;
                      prom_expr := prom_expr e_prom ;
                      prom_env := R_NilValue
                    |} in
                  let e_ := {|
                      NonVector_SExpRec_header := e_ ;
                      NonVector_SExpRec_data := e_prom
                    |} in
                  if_defined S (write_SExp S e e_) (fun S =>
                    result_success S val)))))) in
      ifb nbits_to_nat (gp e_) <> 0 then
        ifb nbits_to_nat (gp e_) = 1 then
          result_error S "[forcePromise] Promise already under evaluation."
        else
          (* Warning: restarting interrupted promise evaluation. *)
          cont S
      else cont S
    else result_success S (prom_value e_prom)).

Definition R_execClosure (runs : runs_type) (S : state)
    (call newrho sysparent rho arglist op : SExpRec_pointer) : result SExpRec_pointer :=
  result_not_implemented "[R_execClosure] TODO".

Definition applyClosure runs S
    (call op arglist rho suppliedvars : SExpRec_pointer) : result SExpRec_pointer :=
  if_defined S (read_SExp S rho) (fun rho_ =>
    ifb type rho_ <> EnvSxp then
      result_error S "[applyClosure] ‘rho’ must be an environment."
    else
      read_as_clo S op (fun op_ op_clo =>
        let formals := clo_formals op_clo in
        let savedrho := clo_env op_clo in
        if_success (matchArgs runs S formals arglist call) (fun S actuals =>
          if_success (NewEnvironment runs S formals actuals savedrho) (fun S newrho =>
            if_success
              (fold_left_listSxp runs S formals actuals (fun S a f_car f_tag =>
                read_as_list S a (fun a_ a_list =>
                  ifb list_carval a_list = R_MissingArg /\ f_car <> R_MissingArg then
                    if_success (mkPROMISE S f_car newrho) (fun S newprom =>
                      set_car S newprom a (fun S =>
                        map_pointer S (set_missing 2 ltac:(nbits_ok)) a (fun S =>
                          result_success S (list_cdrval a_list))))
                  else result_success S (list_cdrval a_list))))
              (fun S _ =>
                if_success
                  (ifb suppliedvars <> R_NilValue then
                     addMissingVarsToNewEnv runs S newrho suppliedvars
                   else result_success S tt) (fun S _ =>
                  if_success
                    (if_success (R_envHasNoSpecialSymbols runs S newrho) (fun S b =>
                       if b then
                         map_pointer S set_no_special_symbols newrho (fun S =>
                           result_success S tt)
                       else result_success S tt)) (fun S _ =>
                    R_execClosure runs S call newrho
                      rho(* TODO: R_GlobalContext->callflag == CTXT_GENERIC ? R_GlobalContext->sysparent : rho *)
                      rho arglist op))))))).


(** The function [eval] evaluates its argument to an unreducible value. **)
Definition eval runs S (e rho : SExpRec_pointer) : result SExpRec_pointer :=
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
            if_is_prom S e_ (fun e_ e_prom =>
              ifb prom_value e_prom = R_UnboundValue then
                if_success (forcePromise runs S e) (fun S e =>
                  result_success S e)
              else result_success S e)
          | LangSxp =>
            if_is_list S e_ (fun e_ e_list =>
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
          | DotSxp => result_error S "[eval] ‘...’ used in an incorrect context"
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
      f (runs max_step) in
    let wrap_dep {A} (f : forall B : Type, runs_type -> A B) B : A B :=
      f B (runs max_step) in {|
      runs_while := wrap_dep while ;
      runs_eval := wrap eval
    |}
  end.


(** * Proofs **)

(** It would be nice to prove that the read-eval-print-loop can not
 * return a [result_impossible]. **)

(** The property we want to eventually prove is that if [eval] returns
 * a result, then the C function eval does similarly. **)

