(** Rfeatures.
  A Coq formalisation of additionnal functions of R from its C code. **)

(* Copyright © 2018 Martin Bodin, Tomás Díaz

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

Set Implicit Arguments.
Require Export Rcore.

(** * Interpreter functions **)

Require Export FErrors.
Require Export FUtil.
Require Export FAttrib.
Require Export FCoerce.
Require Export FEnvir.
Require Export FContext.
Require Export FBind.
Require Export FEval.
Require Export FConnections.
Require Export FPrintutils.
Require Export FPrint.
Require Export FBuiltin.
Require Export FSeq.
Require Export FSign.
Require Export FComplex.
Require Export FArithmetic.
Require Export FSubset.
Require Export FRelop.
Require Export FArray.
Require Export FNames.
Require Export FLogic.
Require Export FSubassign.

(** * Closing the Loop **)

Definition dummy_function name (_ : Globals) (_ : runs_type)
    (call op args rho : SEXP) : result SEXP :=
  unimplemented_function name.

Local Instance funtab_cell_Inhab : Inhab funtab_cell.
  apply prove_Inhab. constructors; try typeclass; constructors; typeclass.
Defined.

Fixpoint runs max_step globals(*FIXME*) : runs_type :=
  match max_step with
  | O => {|
      runs_while_loop := fun _ _ _ _ => result_bottom ;
      runs_set_longjump := fun _ _ _ _ => result_bottom ;
      runs_eval := fun _ _ => result_bottom ;
      runs_getAttrib := fun _ _ => result_bottom ;
      runs_setAttrib := fun _ _ _ => result_bottom ;
      runs_R_cycle_detected := fun _ _ => result_bottom ;
      runs_duplicate1 := fun _ _ => result_bottom ;
      runs_stripAttrib := fun _ _ => result_bottom ;
      runs_evalseq := fun _ _ _ _ => result_bottom ;
      runs_R_isMissing := fun _ _ => result_bottom ;
      runs_AnswerType := fun _ _ _ _ _ => result_bottom ;
      runs_ListAnswer := fun _ _ _ _ => result_bottom ;
      runs_StringAnswer := fun _ _ _ => result_bottom ;
      runs_LogicalAnswer := fun _ _ _ => result_bottom ;
      runs_IntegerAnswer := fun _ _ _ => result_bottom ;
      runs_RealAnswer := fun _ _ _ => result_bottom ;
      runs_ComplexAnswer := fun _ _ _ => result_bottom ;
      runs_RawAnswer := fun _ _ _ => result_bottom ;
      runs_substitute := fun _ _ => result_bottom ;
      runs_substituteList := fun _ _ => result_bottom ;
      runs_R_FunTab := None
    |}
  | S max_step =>
    let wrap {A B : Type} (f : runs_type -> B -> A) (x : B) : A :=
      (** It is important to take this additional parameter [x] as a parameter,
        to defer the computation of [runs max_step] when it is indeed needed.
        Without this, the application of [runs max_int] would overflow the
        stack. **)
      f (runs max_step globals) x in
    let wrap_dep {A : Type -> Type} (f : runs_type -> forall B, A B) (T : Type) : A T :=
      (** A dependent version of [wrap]. **)
      f (runs max_step globals) T in {|
      runs_while_loop := wrap_dep while_loop ;
      runs_set_longjump := wrap_dep set_longjump ;
      runs_eval := wrap (eval globals) ;
      runs_getAttrib := wrap (getAttrib globals) ;
      runs_setAttrib := wrap (setAttrib globals) ;
      runs_R_cycle_detected := wrap (R_cycle_detected globals) ;
      runs_duplicate1 := wrap (duplicate1 globals) ;
      runs_stripAttrib := wrap (stripAttrib globals) ;
      runs_evalseq := wrap (evalseq globals) ;
      runs_R_isMissing := wrap (R_isMissing globals) ;
      runs_AnswerType := wrap (AnswerType globals) ;
      runs_ListAnswer := wrap (ListAnswer globals) ;
      runs_StringAnswer := wrap (StringAnswer globals) ;
      runs_LogicalAnswer := wrap LogicalAnswer ;
      runs_IntegerAnswer := wrap IntegerAnswer ;
      runs_RealAnswer := wrap RealAnswer ;
      runs_ComplexAnswer := wrap ComplexAnswer ;
      runs_RawAnswer := wrap RawAnswer ;
      runs_substitute := wrap (substitute globals) ;
      runs_substituteList := wrap (substituteList globals) ;
      runs_R_FunTab :=

        let eval0 := make_funtab_eval_arg false false in
        let eval1 := make_funtab_eval_arg false true in
        let eval10 := make_funtab_eval_arg true false in
        let eval11 := make_funtab_eval_arg true true in
        let eval100 := make_funtab_eval_arg false false in
        let eval101 := make_funtab_eval_arg false true in
        let eval110 := make_funtab_eval_arg true false in
        let eval111 := make_funtab_eval_arg true true in
        let eval200 := make_funtab_eval_arg false false in
        let eval201 := make_funtab_eval_arg false true in
        let eval210 := make_funtab_eval_arg true false in
        let eval211 := make_funtab_eval_arg true true in

        match max_step with
        | O => None
        | S max_step =>
          let decl name cfun code eval arity :=
            make_funtab_cell name cfun code eval arity in
          let wrap f S call op args rho :=
            (** This function waits that all arguments are given before starting
              the computation of the next [R_FunTab]. **)
            f globals (runs max_step globals) S call op args rho in
          let rdecl name cfun code eval arity kind prec rightassoc :=
            decl name (wrap cfun) code eval arity (make_PPinfo kind prec rightassoc) in
          Some (ArrayList.from_list [

              rdecl "if" do_if (0)%Z eval200 (-1)%Z PP_IF PREC_FN true ;
              rdecl "while" do_while (0)%Z eval100 (2)%Z PP_WHILE PREC_FN false ;
              rdecl "for" do_for (0)%Z eval100 (3)%Z PP_FOR PREC_FN false ;
              rdecl "repeat" do_repeat (0)%Z eval100 (1)%Z PP_REPEAT PREC_FN false ;
              rdecl "break" do_break CTXT_BREAK eval0 (0)%Z PP_BREAK PREC_FN false ;
              rdecl "next" do_break CTXT_NEXT eval0 (0)%Z PP_NEXT PREC_FN false ;
              rdecl "return" do_return (0)%Z eval0 (-1)%Z PP_RETURN PREC_FN false ;
              rdecl "function" do_function 0 eval0 (-1)%Z PP_FUNCTION PREC_FN false ;
              rdecl "<-" do_set 1 eval100 (-1)%Z PP_ASSIGN PREC_LEFT true ;
              rdecl "=" do_set 3 eval100 (-1)%Z PP_ASSIGN PREC_EQ true ;
              rdecl "<<-" do_set 2 eval100 (-1)%Z PP_ASSIGN2 PREC_LEFT true ;
              rdecl "{" do_begin (0)%Z eval200 (-1)%Z PP_CURLY PREC_FN false ;
              rdecl "(" do_paren (0)%Z eval1 (1)%Z PP_PAREN PREC_FN false ;
              rdecl ".subset" do_subset_dflt (1)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".subset2" do_subset2_dflt (2)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "[" do_subset (1)%Z eval0 (-1)%Z PP_SUBSET PREC_SUBSET false ;
              rdecl "[[" do_subset2 (2)%Z eval0 (-1)%Z PP_SUBSET PREC_SUBSET false ;
              rdecl "$" do_subset3 (3)%Z eval0 (2)%Z PP_DOLLAR PREC_DOLLAR false ;
              rdecl "@" (dummy_function "do_AT") (0)%Z eval0 (2)%Z PP_DOLLAR PREC_DOLLAR false ;
              rdecl "[<-" do_subassign (0)%Z eval0 (3)%Z PP_SUBASS PREC_LEFT true ;
              rdecl "[[<-" (dummy_function "do_subassign2") (1)%Z eval0 (3)%Z PP_SUBASS PREC_LEFT true ;
              rdecl "$<-" (dummy_function "do_subassign3") (1)%Z eval0 (3)%Z PP_SUBASS PREC_LEFT true ;
              rdecl "switch" (dummy_function "do_switch") (0)%Z eval200 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "browser" (dummy_function "do_browser") (0)%Z eval101 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".primTrace" (dummy_function "do_trace") (0)%Z eval101 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".primUntrace" (dummy_function "do_trace") (1)%Z eval101 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".Internal" do_internal (0)%Z eval200 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".Primitive" do_primitive (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "call" (dummy_function "do_call") (0)%Z eval0 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "quote" do_quote (0)%Z eval0 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "substitute" do_substitute (0)%Z eval0 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "missing" do_missing (1)%Z eval0 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "nargs" (dummy_function "do_nargs") (1)%Z eval1 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "on.exit" (dummy_function "do_onexit") (0)%Z eval100 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "forceAndCall" do_forceAndCall (0)%Z eval0 (-1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "stop" (dummy_function "do_stop") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "warning" (dummy_function "do_warning") (0)%Z eval111 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "gettext" (dummy_function "do_gettext") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "ngettext" (dummy_function "do_ngettext") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bindtextdomain" (dummy_function "do_bindtextdomain") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".addCondHands" (dummy_function "do_addCondHands") (0)%Z eval111 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".resetCondHands" (dummy_function "do_resetCondHands") (0)%Z eval111 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".signalCondition" (dummy_function "do_signalCondition") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".dfltStop" (dummy_function "do_dfltStop") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".dfltWarn" (dummy_function "do_dfltWarn") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".addRestart" (dummy_function "do_addRestart") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".getRestart" (dummy_function "do_getRestart") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".invokeRestart" (dummy_function "do_invokeRestart") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".addTryHandlers" (dummy_function "do_addTryHandlers") (0)%Z eval111 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "geterrmessage" (dummy_function "do_geterrmessage") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "seterrmessage" (dummy_function "do_seterrmessage") (0)%Z eval111 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "printDeferredWarnings" (dummy_function "do_printDeferredWarnings") (0)%Z eval111 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "interruptsSuspended" (dummy_function "do_interruptsSuspended") (0)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "as.function.default" (dummy_function "do_asfunction") (0)%Z eval11 (2)%Z PP_FUNCTION PREC_FN false ;
              rdecl "debug" (dummy_function "do_debug") (0)%Z eval111 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "undebug" (dummy_function "do_debug") (1)%Z eval111 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "isdebugged" (dummy_function "do_debug") (2)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "debugonce" (dummy_function "do_debug") (3)%Z eval111 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Recall" (dummy_function "do_recall") (0)%Z eval210 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "delayedAssign" do_delayed (0)%Z eval111 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "makeLazy" (dummy_function "do_makelazy") (0)%Z eval111 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "identical" (dummy_function "do_identical") (0)%Z eval11 (8)%Z PP_FUNCALL PREC_FN false ;
              rdecl "C_tryCatchHelper" (dummy_function "do_tryCatchHelper") (0)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "+" do_arith PLUSOP eval1 (-1)%Z PP_BINARY PREC_SUM false ;
              rdecl "-" do_arith MINUSOP eval1 (-1)%Z PP_BINARY PREC_SUM false ;
              rdecl "*" do_arith TIMESOP eval1 (2)%Z PP_BINARY PREC_PROD false ;
              rdecl "/" do_arith DIVOP eval1 (2)%Z PP_BINARY2 PREC_PROD false ;
              rdecl "^" do_arith POWOP eval1 (2)%Z PP_BINARY2 PREC_POWER true ;
              rdecl "%%" do_arith MODOP eval1 (2)%Z PP_BINARY2 PREC_PERCENT false ;
              rdecl "%/%" do_arith IDIVOP eval1 (2)%Z PP_BINARY2 PREC_PERCENT false ;
              rdecl "%*%" (dummy_function "do_matprod") (0)%Z eval1 (2)%Z PP_BINARY PREC_PERCENT false ;

              rdecl "==" do_relop EQOP eval1 (2)%Z PP_BINARY PREC_COMPARE false ;
              rdecl "!=" do_relop NEOP eval1 (2)%Z PP_BINARY PREC_COMPARE false ;
              rdecl "<" do_relop LTOP eval1 (2)%Z PP_BINARY PREC_COMPARE false ;
              rdecl "<=" do_relop LEOP eval1 (2)%Z PP_BINARY PREC_COMPARE false ;
              rdecl ">=" do_relop GEOP eval1 (2)%Z PP_BINARY PREC_COMPARE false ;
              rdecl ">" do_relop GTOP eval1 (2)%Z PP_BINARY PREC_COMPARE false ;
              rdecl "&" do_logic (1)%Z eval1 (2)%Z PP_BINARY PREC_AND false ;
              rdecl "|" do_logic (2)%Z eval1 (2)%Z PP_BINARY PREC_OR false ;
              rdecl "!" do_logic (3)%Z eval1 (1)%Z PP_UNARY PREC_NOT false ;

              rdecl "&&" do_logic2 (1)%Z eval0 (2)%Z PP_BINARY PREC_AND false ;
              rdecl "||" do_logic2 (2)%Z eval0 (2)%Z PP_BINARY PREC_OR false ;
              rdecl ":" do_colon (0)%Z eval1 (2)%Z PP_BINARY2 PREC_COLON false ;

              rdecl "~" (dummy_function "do_tilde") (0)%Z eval0 (-1)%Z PP_BINARY PREC_TILDE false ;

              rdecl "all" (dummy_function "do_logic3") (1)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "any" (dummy_function "do_logic3") (2)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "...elt" (dummy_function "do_dotsElt") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "...length" (dummy_function "do_dotsLength") (0)%Z eval1 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "length" do_length (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "length<-" (dummy_function "do_lengthgets") (0)%Z eval1 (2)%Z PP_FUNCALL PREC_LEFT true ;
              rdecl "c" do_c (0)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "oldClass" (dummy_function "do_class") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "oldClass<-" (dummy_function "do_classgets") (0)%Z eval1 (2)%Z PP_FUNCALL PREC_LEFT true ;
              rdecl "class" (dummy_function "R_do_data_class") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".cache_class" (dummy_function "R_do_data_class") (1)%Z	eval1 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "class<-" (dummy_function "R_do_set_class")	0 eval1 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "unclass" (dummy_function "do_unclass") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "names" (dummy_function "do_names") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "names<-" (dummy_function "do_namesgets") (0)%Z eval1 (2)%Z PP_FUNCALL PREC_LEFT true ;
              rdecl "dimnames" (dummy_function "do_dimnames") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "dimnames<-" (dummy_function "do_dimnamesgets") (0)%Z eval1 (2)%Z PP_FUNCALL PREC_LEFT true ;
              rdecl "dim" (dummy_function "do_dim") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "dim<-" (dummy_function "do_dimgets") (0)%Z eval1 (2)%Z PP_FUNCALL PREC_LEFT true ;
              rdecl "attributes" (dummy_function "do_attributes") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "attributes<-" (dummy_function "do_attributesgets") (0)%Z eval1 (2)%Z PP_FUNCALL PREC_LEFT true ;
              rdecl "attr" do_attr (0)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "attr<-" do_attrgets (0)%Z eval1 (3)%Z PP_FUNCALL PREC_LEFT true ;
              rdecl "@<-" do_attrgets (1)%Z eval0 (3)%Z PP_SUBASS PREC_LEFT true ;
              rdecl "levels<-" (dummy_function "do_levelsgets") (0)%Z eval1 (2)%Z PP_FUNCALL PREC_LEFT true ;

              rdecl "vector" do_makevector (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "complex" (dummy_function "do_complex") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "matrix" do_matrix (0)%Z eval11 (7)%Z PP_FUNCALL PREC_FN false ;
              rdecl "array" (dummy_function "do_array") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "diag" (dummy_function "do_diag") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "backsolve" (dummy_function "do_backsolve") (0)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "max.col" (dummy_function "do_maxcol") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "row" (dummy_function "do_rowscols") (1)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "col" (dummy_function "do_rowscols") (2)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "unlist" (dummy_function "do_unlist") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "cbind" (dummy_function "do_bind") (1)%Z eval10 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rbind" (dummy_function "do_bind") (2)%Z eval10 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "drop" (dummy_function "do_drop") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "all.names" (dummy_function "do_allnames") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "comment" (dummy_function "do_comment") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "comment<-" (dummy_function "do_commentgets") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_LEFT true ;
              rdecl "get" do_get (1)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "get0" do_get (2)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "mget" (dummy_function "do_mget") (1)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "exists" do_get (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "assign" do_assign (0)%Z eval111 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "list2env" (dummy_function "do_list2env") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "remove" (dummy_function "do_remove") (0)%Z eval111 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "duplicated" (dummy_function "do_duplicated") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "unique" (dummy_function "do_duplicated") (1)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "anyDuplicated" (dummy_function "do_duplicated") (2)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "anyNA" (dummy_function "do_anyNA") (0)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "which" (dummy_function "do_which") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "which.min" (dummy_function "do_first_min") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pmin" (dummy_function "do_pmin") (0)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pmax" (dummy_function "do_pmin") (1)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "which.max" (dummy_function "do_first_min") (1)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "match" (dummy_function "do_match") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pmatch" (dummy_function "do_pmatch") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "charmatch" (dummy_function "do_charmatch") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "match.call" (dummy_function "do_matchcall") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "crossprod" (dummy_function "do_matprod") (1)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "tcrossprod" (dummy_function "do_matprod") (2)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "lengths" (dummy_function "do_lengths") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "attach" (dummy_function "do_attach") (0)%Z eval111 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "detach" (dummy_function "do_detach") (0)%Z eval111 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "search" (dummy_function "do_search") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "setFileTime" (dummy_function "do_setFileTime") (0)%Z eval111 (2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "round" (dummy_function "do_Math2") (10001)%Z eval0 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "signif" (dummy_function "do_Math2") (10004)%Z eval0 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "log" (dummy_function "do_log") (10003)%Z eval0 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "log10" (dummy_function "do_log1arg") (10)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "log2" (dummy_function "do_log1arg") (2)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "abs" (dummy_function "do_abs") (6)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "floor" do_math1 (1)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "ceiling" do_math1 (2)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sqrt" do_math1 (3)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sign" do_math1 (4)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "trunc" (dummy_function "do_trunc") (5)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "exp" do_math1 (10)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "expm1" do_math1 (11)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "log1p" do_math1 (12)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "cos" do_math1 (20)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sin" do_math1 (21)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "tan" do_math1 (22)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "acos" do_math1 (23)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "asin" do_math1 (24)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "atan" do_math1 (25)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "cosh" do_math1 (30)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sinh" do_math1 (31)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "tanh" do_math1 (32)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "acosh" do_math1 (33)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "asinh" do_math1 (34)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "atanh" do_math1 (35)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "lgamma" do_math1 (40)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "gamma" do_math1 (41)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "digamma" do_math1 (42)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "trigamma" do_math1 (43)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "cospi" do_math1 (47)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sinpi" do_math1 (48)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "tanpi" do_math1 (49)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "atan2" (dummy_function "do_math2") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "lbeta" (dummy_function "do_math2") (2)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "beta" (dummy_function "do_math2") (3)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "lchoose" (dummy_function "do_math2") (4)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "choose" (dummy_function "do_math2") (5)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dchisq" (dummy_function "do_math2") (6)%Z eval11 (2+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pchisq" (dummy_function "do_math2") (7)%Z eval11 (2+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qchisq" (dummy_function "do_math2") (8)%Z eval11 (2+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dexp" (dummy_function "do_math2") (9)%Z eval11 (2+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pexp" (dummy_function "do_math2") (10)%Z eval11 (2+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qexp" (dummy_function "do_math2") (11)%Z eval11 (2+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dgeom" (dummy_function "do_math2") (12)%Z eval11 (2+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pgeom" (dummy_function "do_math2") (13)%Z eval11 (2+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qgeom" (dummy_function "do_math2") (14)%Z eval11 (2+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dpois" (dummy_function "do_math2") (15)%Z eval11 (2+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "ppois" (dummy_function "do_math2") (16)%Z eval11 (2+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qpois" (dummy_function "do_math2") (17)%Z eval11 (2+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dt" (dummy_function "do_math2") (18)%Z eval11 (2+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pt" (dummy_function "do_math2") (19)%Z eval11 (2+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qt" (dummy_function "do_math2") (20)%Z eval11 (2+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dsignrank" (dummy_function "do_math2") (21)%Z eval11 (2+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "psignrank" (dummy_function "do_math2") (22)%Z eval11 (2+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qsignrank" (dummy_function "do_math2") (23)%Z eval11 (2+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "besselJ" (dummy_function "do_math2") (24)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "besselY" (dummy_function "do_math2") (25)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "psigamma" (dummy_function "do_math2") (26)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "Re" (dummy_function "do_cmathfuns") (1)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Im" (dummy_function "do_cmathfuns") (2)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Mod" (dummy_function "do_cmathfuns") (3)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Arg" (dummy_function "do_cmathfuns") (4)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Conj" (dummy_function "do_cmathfuns") (5)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dbeta" (dummy_function "do_math3") (1)%Z eval11 (3+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pbeta" (dummy_function "do_math3") (2)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qbeta" (dummy_function "do_math3") (3)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dbinom" (dummy_function "do_math3") (4)%Z eval11 (3+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pbinom" (dummy_function "do_math3") (5)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qbinom" (dummy_function "do_math3") (6)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dcauchy" (dummy_function "do_math3") (7)%Z eval11 (3+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pcauchy" (dummy_function "do_math3") (8)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qcauchy" (dummy_function "do_math3") (9)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "df" (dummy_function "do_math3") (10)%Z eval11 (3+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pf" (dummy_function "do_math3") (11)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qf" (dummy_function "do_math3") (12)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dgamma" (dummy_function "do_math3") (13)%Z eval11 (3+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pgamma" (dummy_function "do_math3") (14)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qgamma" (dummy_function "do_math3") (15)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dlnorm" (dummy_function "do_math3") (16)%Z eval11 (3+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "plnorm" (dummy_function "do_math3") (17)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qlnorm" (dummy_function "do_math3") (18)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dlogis" (dummy_function "do_math3") (19)%Z eval11 (3+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "plogis" (dummy_function "do_math3") (20)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qlogis" (dummy_function "do_math3") (21)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dnbinom" (dummy_function "do_math3") (22)%Z eval11 (3+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pnbinom" (dummy_function "do_math3") (23)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qnbinom" (dummy_function "do_math3") (24)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dnorm" (dummy_function "do_math3") (25)%Z eval11 (3+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pnorm" (dummy_function "do_math3") (26)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qnorm" (dummy_function "do_math3") (27)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dunif" (dummy_function "do_math3") (28)%Z eval11 (3+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "punif" (dummy_function "do_math3") (29)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qunif" (dummy_function "do_math3") (30)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dweibull" (dummy_function "do_math3") (31)%Z eval11 (3+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pweibull" (dummy_function "do_math3") (32)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qweibull" (dummy_function "do_math3") (33)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dnchisq" (dummy_function "do_math3") (34)%Z eval11 (3+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pnchisq" (dummy_function "do_math3") (35)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qnchisq" (dummy_function "do_math3") (36)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dnt" (dummy_function "do_math3") (37)%Z eval11 (3+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pnt" (dummy_function "do_math3") (38)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qnt" (dummy_function "do_math3") (39)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dwilcox" (dummy_function "do_math3") (40)%Z eval11 (3+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pwilcox" (dummy_function "do_math3") (41)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qwilcox" (dummy_function "do_math3") (42)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "besselI" (dummy_function "do_math3") (43)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "besselK" (dummy_function "do_math3") (44)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dnbinom_mu" (dummy_function "do_math3") (45)%Z eval11 (3+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pnbinom_mu" (dummy_function "do_math3") (46)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qnbinom_mu" (dummy_function "do_math3") (47)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dhyper" (dummy_function "do_math4") (1)%Z eval11 (4+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "phyper" (dummy_function "do_math4") (2)%Z eval11 (4+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qhyper" (dummy_function "do_math4") (3)%Z eval11 (4+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dnbeta" (dummy_function "do_math4") (4)%Z eval11 (4+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pnbeta" (dummy_function "do_math4") (5)%Z eval11 (4+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qnbeta" (dummy_function "do_math4") (6)%Z eval11 (4+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dnf" (dummy_function "do_math4") (7)%Z eval11 (4+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pnf" (dummy_function "do_math4") (8)%Z eval11 (4+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qnf" (dummy_function "do_math4") (9)%Z eval11 (4+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dtukey" (dummy_function "do_math4") (10)%Z eval11 (4+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "ptukey" (dummy_function "do_math4") (11)%Z eval11 (4+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qtukey" (dummy_function "do_math4") (12)%Z eval11 (4+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "rchisq" (dummy_function "do_random1") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rexp" (dummy_function "do_random1") (1)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rgeom" (dummy_function "do_random1") (2)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rpois" (dummy_function "do_random1") (3)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rt" (dummy_function "do_random1") (4)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rsignrank" (dummy_function "do_random1") (5)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "rbeta" (dummy_function "do_random2") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rbinom" (dummy_function "do_random2") (1)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rcauchy" (dummy_function "do_random2") (2)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rf" (dummy_function "do_random2") (3)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rgamma" (dummy_function "do_random2") (4)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rlnorm" (dummy_function "do_random2") (5)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rlogis" (dummy_function "do_random2") (6)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rnbinom" (dummy_function "do_random2") (7)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rnbinom_mu" (dummy_function "do_random2") (13)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rnchisq" (dummy_function "do_random2") (12)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rnorm" (dummy_function "do_random2") (8)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "runif" (dummy_function "do_random2") (9)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rweibull" (dummy_function "do_random2") (10)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rwilcox" (dummy_function "do_random2") (11)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;

              rdecl "rhyper" (dummy_function "do_random3") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;

              rdecl "sample" (dummy_function "do_sample") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sample2" (dummy_function "do_sample2") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "RNGkind" (dummy_function "do_RNGkind") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "set.seed" (dummy_function "do_setseed") (0)%Z eval111 (3)%Z PP_FUNCALL PREC_FN false ;

              rdecl "sum" (dummy_function "do_summary") (0)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "min" (dummy_function "do_summary") (2)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "max" (dummy_function "do_summary") (3)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "prod" (dummy_function "do_summary") (4)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "mean" (dummy_function "do_summary") (1)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "range" (dummy_function "do_range") (0)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "cumsum" (dummy_function "do_cum") (1)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "cumprod" (dummy_function "do_cum") (2)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "cummax" (dummy_function "do_cum") (3)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "cummin" (dummy_function "do_cum") (4)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "as.character" do_asatomic (0)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "as.integer" do_asatomic (1)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "as.double" do_asatomic (2)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "as.numeric"do_asatomic (2)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "as.complex" do_asatomic (3)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "as.logical" do_asatomic (4)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "as.raw" do_asatomic (5)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "as.call" (dummy_function "do_ascall") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "as.environment" (dummy_function "do_as_environment") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "storage.mode<-" (dummy_function "do_storage_mode") (0)%Z eval1 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "asCharacterFactor" do_asCharacterFactor (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "as.vector" (dummy_function "do_asvector") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "paste" (dummy_function "do_paste") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "paste0" (dummy_function "do_paste") (1)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "file.path" (dummy_function "do_filepath") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "format" (dummy_function "do_format") (0)%Z eval11 (9)%Z PP_FUNCALL PREC_FN false ;
              rdecl "format.info" (dummy_function "do_formatinfo") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "cat" do_cat (0)%Z eval111 (6)%Z PP_FUNCALL PREC_FN false ;
              rdecl "do.call" (dummy_function "do_docall") (0)%Z eval211 (3)%Z PP_FUNCALL PREC_FN false ;

              rdecl "nchar" (dummy_function "do_nchar") (1)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "nzchar" (dummy_function "do_nzchar") (1)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "substr" (dummy_function "do_substr") (1)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "startsWith" (dummy_function "do_startsWith") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "endsWith" (dummy_function "do_startsWith") (1)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "substr<-" (dummy_function "do_substrgets") (1)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "strsplit" (dummy_function "do_strsplit") (1)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "abbreviate" (dummy_function "do_abbrev") (1)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "make.names" (dummy_function "do_makenames") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pcre_config" (dummy_function "do_pcre_config") (1)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "grep" (dummy_function "do_grep") (0)%Z eval11 (8)%Z PP_FUNCALL PREC_FN false ;
              rdecl "grepl" (dummy_function "do_grep") (1)%Z eval11 (8)%Z PP_FUNCALL PREC_FN false ;
              rdecl "grepRaw" (dummy_function "do_grepraw") (0)%Z eval11 (8)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sub" (dummy_function "do_gsub") (0)%Z eval11 (7)%Z PP_FUNCALL PREC_FN false ;
              rdecl "gsub" (dummy_function "do_gsub") (1)%Z eval11 (7)%Z PP_FUNCALL PREC_FN false ;
              rdecl "regexpr" (dummy_function "do_regexpr") (0)%Z eval11 (6)%Z PP_FUNCALL PREC_FN false ;
              rdecl "gregexpr" (dummy_function "do_regexpr") (1)%Z eval11 (6)%Z PP_FUNCALL PREC_FN false ;
              rdecl "regexec" (dummy_function "do_regexec") (1)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "agrep" (dummy_function "do_agrep") (0)%Z eval11 (8)%Z PP_FUNCALL PREC_FN false ;
              rdecl "agrepl" (dummy_function "do_agrep") (1)%Z eval11 (8)%Z PP_FUNCALL PREC_FN false ;
              rdecl "adist" (dummy_function "do_adist") (1)%Z eval11 (8)%Z PP_FUNCALL PREC_FN false ;
              rdecl "aregexec" (dummy_function "do_aregexec") (1)%Z eval11 (7)%Z PP_FUNCALL PREC_FN false ;
              rdecl "tolower" (dummy_function "do_tolower") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "toupper" (dummy_function "do_tolower") (1)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "chartr" (dummy_function "do_chartr") (1)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sprintf" (dummy_function "do_sprintf") (1)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "make.unique" (dummy_function "do_makeunique") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "charToRaw" (dummy_function "do_charToRaw") (1)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rawToChar" (dummy_function "do_rawToChar") (1)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rawShift" (dummy_function "do_rawShift") (1)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "intToBits" (dummy_function "do_intToBits") (1)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rawToBits" (dummy_function "do_rawToBits") (1)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "packBits" (dummy_function "do_packBits") (1)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "utf8ToInt" (dummy_function "do_utf8ToInt") (1)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "intToUtf8" (dummy_function "do_intToUtf8") (1)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "validUTF8" (dummy_function "do_validUTF8") (1)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "validEnc" (dummy_function "do_validEnc") (1)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "encodeString" (dummy_function "do_encodeString") (1)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "iconv" (dummy_function "do_iconv") (0)%Z eval11 (6)%Z PP_FUNCALL PREC_FN false ;
              rdecl "strtrim" (dummy_function "do_strtrim") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "strtoi" (dummy_function "do_strtoi") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "strrep" (dummy_function "do_strrep") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "is.null" do_is NilSxp eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.logical" do_is LglSxp eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.integer" do_is IntSxp eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.double" do_is RealSxp eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.complex" do_is CplxSxp eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.character" do_is StrSxp eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.symbol" do_is SymSxp eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.name" do_is SymSxp eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.environment" do_is EnvSxp eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.list" do_is VecSxp eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.pairlist" do_is ListSxp eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.expression" do_is ExprSxp eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.raw" do_is RawSxp eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "is.object" do_is (50)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "isS4" do_is (51)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "is.numeric" do_is (100)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.matrix" do_is (101)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.array" do_is (102)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "is.atomic" do_is (200)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.recursive" do_is (201)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "is.call" do_is (300)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.language" do_is (301)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.function" do_is (302)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "is.single" do_is (999)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "is.na" do_isna (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.nan" do_isnan (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.finite" (dummy_function "do_isfinite") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.infinite" (dummy_function "do_isinfinite") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "is.vector" do_isvector (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "proc.time" (dummy_function "do_proctime") (0)%Z eval1 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "gc.time" (dummy_function "do_gctime") (0)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "withVisible" (dummy_function "do_withVisible") (1)%Z eval10 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "expression" (dummy_function "do_expression") (1)%Z eval0 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "interactive" (dummy_function "do_interactive") (0)%Z eval1 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "invisible" do_invisible (0)%Z eval101 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rep" (dummy_function "do_rep") (0)%Z eval0 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rep.int" (dummy_function "do_rep_int") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rep_len" (dummy_function "do_rep_len") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "seq.int" (dummy_function "do_seq") (0)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "seq_len" (dummy_function "do_seq_len") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "seq_along" (dummy_function "do_seq_along") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "list" do_makelist (1)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "xtfrm" (dummy_function "do_xtfrm") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "enc2native" (dummy_function "do_enc2") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "enc2utf8" (dummy_function "do_enc2") (1)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "emptyenv" do_emptyenv (0)%Z eval1 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "baseenv" do_baseenv (0)%Z eval1 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "globalenv" do_globalenv (0)%Z eval1 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "environment<-" (dummy_function "do_envirgets") (0)%Z eval1 (2)%Z PP_FUNCALL PREC_LEFT true ;
              rdecl "pos.to.env" (dummy_function "do_pos2env") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "eapply" (dummy_function "do_eapply") (0)%Z eval10 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "lapply" (dummy_function "do_lapply") (0)%Z eval10 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "vapply" (dummy_function "do_vapply") (0)%Z eval10 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "mapply" (dummy_function "do_mapply") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;

              rdecl ".C" (dummy_function "do_dotCode") (0)%Z eval1 (-1)%Z PP_FOREIGN PREC_FN false ;
              rdecl ".Fortran" (dummy_function "do_dotCode") (1)%Z eval1 (-1)%Z PP_FOREIGN PREC_FN false ;
              rdecl ".External" (dummy_function "do_External") (0)%Z eval1 (-1)%Z PP_FOREIGN PREC_FN false ;
              rdecl ".External2" (dummy_function "do_External") (1)%Z eval201 (-1)%Z PP_FOREIGN PREC_FN false ;
              rdecl ".Call" (dummy_function "do_dotcall") (0)%Z eval1 (-1)%Z PP_FOREIGN PREC_FN false ;
              rdecl ".External.graphics" (dummy_function "do_Externalgr") (0)%Z eval1 (-1)%Z PP_FOREIGN PREC_FN false ;
              rdecl ".Call.graphics" (dummy_function "do_dotcallgr") (0)%Z eval1 (-1)%Z PP_FOREIGN PREC_FN false ;

              rdecl "Version" (dummy_function "do_version") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "machine" (dummy_function "do_machine") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "commandArgs" (dummy_function "do_commandArgs") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "internalsID" (dummy_function "do_internalsID") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;

              rdecl "system" (dummy_function "do_system") (0)%Z eval211 (3)%Z PP_FUNCALL PREC_FN false ;

              rdecl "parse" (dummy_function "do_parse") (0)%Z eval11 (6)%Z PP_FUNCALL PREC_FN false ;

              rdecl "save" (dummy_function "do_save") (0)%Z eval111 (6)%Z PP_FUNCALL PREC_FN false ;
              rdecl "saveToConn" (dummy_function "do_saveToConn") (0)%Z eval111 (6)%Z PP_FUNCALL PREC_FN false ;
              rdecl "load" (dummy_function "do_load") (0)%Z eval111 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "loadFromConn2" (dummy_function "do_loadFromConn2") (0)%Z eval111 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "serializeToConn" (dummy_function "do_serializeToConn") (0)%Z eval111 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "unserializeFromConn" (dummy_function "do_unserializeFromConn") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "deparse" (dummy_function "do_deparse") (0)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "dput" (dummy_function "do_dput") (0)%Z eval111 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "dump" (dummy_function "do_dump") (0)%Z eval111 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "quit" (dummy_function "do_quit") (0)%Z eval111 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "readline" (dummy_function "do_readln") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "print.default" (dummy_function "do_printdefault") (0)%Z eval111 (9)%Z PP_FUNCALL PREC_FN false ;
              rdecl "print.function" (dummy_function "do_printfunction") (0)%Z eval111 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "prmatrix" (dummy_function "do_prmatrix") (0)%Z eval111 (6)%Z PP_FUNCALL PREC_FN false ;
              rdecl "gc" (dummy_function "do_gc") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "gcinfo" (dummy_function "do_gcinfo") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "gctorture" (dummy_function "do_gctorture") (0)%Z eval111 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "gctorture2" (dummy_function "do_gctorture2") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "memory.profile" (dummy_function "do_memoryprofile") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "split" (dummy_function "do_split") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.loaded" (dummy_function "do_isloaded") (0)%Z eval11 (-1)%Z PP_FOREIGN PREC_FN false ;
              rdecl "recordGraphics" (dummy_function "do_recordGraphics") (0)%Z eval211 (3)%Z PP_FOREIGN PREC_FN false ;
              rdecl "dyn.load" (dummy_function "do_dynload") (0)%Z eval111 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "dyn.unload" (dummy_function "do_dynunload") (0)%Z eval111 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "ls" (dummy_function "do_ls") (1)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "typeof" do_typeof (1)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "eval" do_eval (0)%Z eval211 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "returnValue" (dummy_function "do_returnValue") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sys.parent" (dummy_function "do_sys") (1)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sys.call" (dummy_function "do_sys") (2)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sys.frame" (dummy_function "do_sys") (3)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sys.nframe" (dummy_function "do_sys") (4)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sys.calls" (dummy_function "do_sys") (5)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sys.frames" (dummy_function "do_sys") (6)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sys.on.exit" (dummy_function "do_sys") (7)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sys.parents" (dummy_function "do_sys") (8)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sys.function" (dummy_function "do_sys") (9)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "traceback" (dummy_function "do_traceback") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "browserText" (dummy_function "do_sysbrowser") (1)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "browserCondition" (dummy_function "do_sysbrowser") (2)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "browserSetDebug" (dummy_function "do_sysbrowser") (3)%Z eval111 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "parent.frame" do_parentframe (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sort" (dummy_function "do_sort") (1)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.unsorted" (dummy_function "do_isunsorted") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "psort" (dummy_function "do_psort") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qsort" (dummy_function "do_qsort") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "radixsort" (dummy_function "do_radixsort") (0)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "order" (dummy_function "do_order") (0)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rank" (dummy_function "do_rank") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "scan" (dummy_function "do_scan") (0)%Z eval11 (19)%Z PP_FUNCALL PREC_FN false ;
              rdecl "t.default" (dummy_function "do_transpose") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "aperm" (dummy_function "do_aperm") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "builtins" (dummy_function "do_builtins") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "args" (dummy_function "do_args") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "formals" (dummy_function "do_formals") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "body" do_body (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bodyCode" (dummy_function "do_bodyCode") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "environment" do_envir (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "environmentName" (dummy_function "do_envirName") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "env2list" (dummy_function "do_env2list") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "reg.finalizer" (dummy_function "do_regFinaliz") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "options" (dummy_function "do_options") (0)%Z eval211 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "getOption" (dummy_function "do_getOption") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sink" (dummy_function "do_sink") (0)%Z eval111 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sink.number" (dummy_function "do_sinknumber") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rapply" (dummy_function "do_rapply") (0)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "islistfactor" (dummy_function "do_islistfactor") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "colSums" (dummy_function "do_colsum") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "colMeans" (dummy_function "do_colsum") (1)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rowSums" (dummy_function "do_colsum") (2)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rowMeans" (dummy_function "do_colsum") (3)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "tracemem" (dummy_function "do_tracemem") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "retracemem" (dummy_function "do_retracemem") (0)%Z eval201 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "untracemem" (dummy_function "do_untracemem") (0)%Z eval101 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "inspect" (dummy_function "do_inspect") (0)%Z eval111 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "address" (dummy_function "do_address") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "refcnt" (dummy_function "do_refcnt") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "merge" (dummy_function "do_merge") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "capabilities" (dummy_function "do_capabilities") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "capabilitiesX11" (dummy_function "do_capabilitiesX11") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "new.env" do_newenv (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "parent.env" do_parentenv (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "parent.env<-" do_parentenvgets (0)%Z eval11 (2)%Z PP_FUNCALL PREC_LEFT true ;
              rdecl "topenv" (dummy_function "do_topenv") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "l10n_info" (dummy_function "do_l10n_info") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Cstack_info" (dummy_function "do_Cstack_info") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "mmap_file" (dummy_function "do_mmap_file") (0)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "munmap_file" (dummy_function "do_munmap_file") (0)%Z eval111 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "wrap_meta" (dummy_function "do_wrap_meta") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;

              rdecl "file.show" (dummy_function "do_fileshow") (0)%Z eval111 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "file.create" (dummy_function "do_filecreate") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "file.remove" (dummy_function "do_fileremove") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "file.rename" (dummy_function "do_filerename") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "file.append" (dummy_function "do_fileappend") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "file.symlink" (dummy_function "do_filesymlink") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "file.link" (dummy_function "do_filelink") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "file.copy" (dummy_function "do_filecopy") (0)%Z eval11 (6)%Z PP_FUNCALL PREC_FN false ;
              rdecl "list.files" (dummy_function "do_listfiles") (0)%Z eval11 (8)%Z PP_FUNCALL PREC_FN false ;
              rdecl "list.dirs" (dummy_function "do_listdirs") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "file.exists" (dummy_function "do_fileexists") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "file.choose" (dummy_function "do_filechoose") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "file.info" (dummy_function "do_fileinfo") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "file.access" (dummy_function "do_fileaccess") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "dir.exists" (dummy_function "do_direxists") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "dir.create" (dummy_function "do_dircreate") (0)%Z eval111 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "tempfile" (dummy_function "do_tempfile") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "tempdir" (dummy_function "do_tempdir") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "R.home" (dummy_function "do_Rhome") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "date" (dummy_function "do_date") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Sys.getenv" (dummy_function "do_getenv") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Sys.setenv" (dummy_function "do_setenv") (0)%Z eval111 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Sys.unsetenv" (dummy_function "do_unsetenv") (0)%Z eval111 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "getwd" (dummy_function "do_getwd") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "setwd" (dummy_function "do_setwd") (0)%Z eval111 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "basename" (dummy_function "do_basename") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "dirname" (dummy_function "do_dirname") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Sys.chmod" (dummy_function "do_syschmod") (0)%Z eval111 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Sys.umask" (dummy_function "do_sysumask") (0)%Z eval211 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Sys.readlink" (dummy_function "do_readlink") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Sys.info" (dummy_function "do_sysinfo") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Sys.sleep" (dummy_function "do_syssleep") (0)%Z eval111 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Sys.getlocale" (dummy_function "do_getlocale") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Sys.setlocale" (dummy_function "do_setlocale") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Sys.localeconv" (dummy_function "do_localeconv") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "path.expand" (dummy_function "do_pathexpand") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Sys.getpid" (dummy_function "do_sysgetpid") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "normalizePath" (dummy_function "do_normalizepath") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Sys.glob" (dummy_function "do_glob") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "unlink" (dummy_function "do_unlink") (0)%Z eval111 (3)%Z PP_FUNCALL PREC_FN false ;

              rdecl "polyroot" (dummy_function "do_polyroot") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "inherits" (dummy_function "do_inherits") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "UseMethod" (dummy_function "do_usemethod") (0)%Z eval200 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "NextMethod" (dummy_function "do_nextmethod") (0)%Z eval210 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "standardGeneric" (dummy_function "do_standardGeneric") (0)%Z eval201 (-1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "Sys.time" (dummy_function "do_systime") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "as.POSIXct" (dummy_function "do_asPOSIXct") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "as.POSIXlt" (dummy_function "do_asPOSIXlt") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "format.POSIXlt" (dummy_function "do_formatPOSIXlt") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "strptime" (dummy_function "do_strptime") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Date2POSIXlt" (dummy_function "do_D2POSIXlt") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "POSIXlt2Date" (dummy_function "do_POSIXlt2D") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "mkCode" (dummy_function "do_mkcode") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bcClose" (dummy_function "do_bcclose") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.builtin.internal" (dummy_function "do_is_builtin_internal") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "disassemble" (dummy_function "do_disassemble") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bcVersion" (dummy_function "do_bcversion") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "load.from.file" (dummy_function "do_loadfile") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "save.to.file" (dummy_function "do_savefile") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "growconst" (dummy_function "do_growconst") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "putconst" (dummy_function "do_putconst") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "getconst" (dummy_function "do_getconst") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "enableJIT" (dummy_function "do_enablejit") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "compilePKGS" (dummy_function "do_compilepkgs") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "setNumMathThreads" (dummy_function "do_setnumthreads") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "setMaxNumMathThreads" (dummy_function "do_setmaxnumthreads") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "stdin" (dummy_function "do_stdin") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "stdout" (dummy_function "do_stdout") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "stderr" (dummy_function "do_stderr") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "isatty" (dummy_function "do_isatty") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "readLines" (dummy_function "do_readLines") (0)%Z eval11 (6)%Z PP_FUNCALL PREC_FN false ;
              rdecl "writeLines" (dummy_function "do_writelines") (0)%Z eval111 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "readBin" (dummy_function "do_readbin") (0)%Z eval11 (6)%Z PP_FUNCALL PREC_FN false ;
              rdecl "writeBin" (dummy_function "do_writebin") (0)%Z eval211 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "readChar" (dummy_function "do_readchar") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "writeChar" (dummy_function "do_writechar") (0)%Z eval211 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "open" (dummy_function "do_open") (0)%Z eval111 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "isOpen" (dummy_function "do_isopen") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "isIncomplete" (dummy_function "do_isincomplete") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "isSeekable" (dummy_function "do_isseekable") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "close" (dummy_function "do_close") (0)%Z eval111 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "flush" (dummy_function "do_flush") (0)%Z eval111 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "file" (dummy_function "do_url") (1)%Z eval11 (6)%Z PP_FUNCALL PREC_FN false ;
              rdecl "url" (dummy_function "do_url") (0)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pipe" (dummy_function "do_pipe") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "fifo" (dummy_function "do_fifo") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "gzfile" (dummy_function "do_gzfile") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bzfile" (dummy_function "do_gzfile") (1)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "xzfile" (dummy_function "do_gzfile") (2)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "unz" (dummy_function "do_unz") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "seek" (dummy_function "do_seek") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "truncate" (dummy_function "do_truncate") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pushBack" (dummy_function "do_pushback") (0)%Z eval111 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "clearPushBack" (dummy_function "do_clearpushback") (0)%Z eval111 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pushBackLength" (dummy_function "do_pushbacklength") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rawConnection" (dummy_function "do_rawconnection") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rawConnectionValue" (dummy_function "do_rawconvalue") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "textConnection" (dummy_function "do_textconnection") (0)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "textConnectionValue" (dummy_function "do_textconvalue") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "socketConnection" (dummy_function "do_sockconn") (0)%Z eval11 (7)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sockSelect" (dummy_function "do_sockselect") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "getConnection" do_getconnection (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "getAllConnections" (dummy_function "do_getallconnections") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "summary.connection" (dummy_function "do_sumconnection") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "gzcon" (dummy_function "do_gzcon") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "memCompress" (dummy_function "do_memCompress") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "memDecompress" (dummy_function "do_memDecompress") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "readDCF" (dummy_function "do_readDCF") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;


              rdecl "lockEnvironment" (dummy_function "do_lockEnv") (0)%Z eval111 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "environmentIsLocked" (dummy_function "do_envIsLocked") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "lockBinding" (dummy_function "do_lockBnd") (0)%Z eval111 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "unlockBinding" (dummy_function "do_lockBnd") (1)%Z eval111 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bindingIsLocked" (dummy_function "do_bndIsLocked") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "makeActiveBinding" (dummy_function "do_mkActiveBnd") (0)%Z eval111 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bindingIsActive" (dummy_function "do_bndIsActive") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "mkUnbound" (dummy_function "do_mkUnbound") (0)%Z eval111 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "isNamespaceEnv" (dummy_function "do_isNSEnv") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "registerNamespace" (dummy_function "do_regNS") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "unregisterNamespace" (dummy_function "do_unregNS") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "getRegisteredNamespace" (dummy_function "do_getRegNS") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "isRegisteredNamespace" (dummy_function "do_getRegNS") (1)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "getNamespaceRegistry" (dummy_function "do_getNSRegistry") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "importIntoEnv" (dummy_function "do_importIntoEnv") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "env.profile" (dummy_function "do_envprofile") (0)%Z eval211 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "Encoding" (dummy_function "do_encoding") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "setEncoding" (dummy_function "do_setencoding") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "setTimeLimit" (dummy_function "do_setTimeLimit") (0)%Z eval111 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "setSessionTimeLimit" (dummy_function "do_setSessionTimeLimit") (0)%Z eval111 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "icuSetCollate" (dummy_function "do_ICUset") (0)%Z eval111 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "icuGetCollate" (dummy_function "do_ICUget") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "readRenviron" (dummy_function "do_readEnviron") (0)%Z eval111 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "shortRowNames" (dummy_function "do_shortRowNames") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "copyDFattr" (dummy_function "do_copyDFattr") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "getRegisteredRoutines" (dummy_function "do_getRegisteredRoutines") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "getLoadedDLLs" (dummy_function "do_getDllTable") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "getSymbolInfo" (dummy_function "do_getSymbolInfo") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".isMethodsDispatchOn" (dummy_function "do_S4on") (0)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "lazyLoadDBfetch" (dummy_function "do_lazyLoadDBfetch") (0)%Z eval1 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "lazyLoadDBflush" (dummy_function "do_lazyLoadDBflush") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "getVarsFromFrame" (dummy_function "do_getVarsFromFrame") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "lazyLoadDBinsertValue" (dummy_function "do_lazyLoadDBinsertValue") (0)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bincode" (dummy_function "do_bincode") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "tabulate" (dummy_function "do_tabulate") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "findInterval" (dummy_function "do_findinterval") (0)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pretty" (dummy_function "do_pretty") (0)%Z eval11 (7)%Z PP_FUNCALL PREC_FN false ;
              rdecl "formatC" (dummy_function "do_formatC") (0)%Z eval11 (7)%Z PP_FUNCALL PREC_FN false ;
              rdecl "crc64" (dummy_function "do_crc64") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bitwiseAnd" (dummy_function "do_bitwise") (1)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bitwiseNot" (dummy_function "do_bitwise") (2)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bitwiseOr" (dummy_function "do_bitwise") (3)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bitwiseXor" (dummy_function "do_bitwise") (4)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bitwiseShiftL" (dummy_function "do_bitwise") (5)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bitwiseShiftR" (dummy_function "do_bitwise") (6)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "serialize" (dummy_function "do_serialize") (0)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "serializeb" (dummy_function "do_serialize") (1)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "unserialize" (dummy_function "do_serialize") (2)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rowsum_matrix" (dummy_function "do_rowsum") (0)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rowsum_df" (dummy_function "do_rowsum") (1)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "setS4Object" (dummy_function "do_setS4Object") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "traceOnOff" (dummy_function "do_traceOnOff") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "debugOnOff" (dummy_function "do_traceOnOff") (1)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "La_qr_cmplx" (dummy_function "do_lapack") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_rs" (dummy_function "do_lapack") (1)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_rs_cmplx" (dummy_function "do_lapack") (2)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_rg" (dummy_function "do_lapack") (3)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_rg_cmplx" (dummy_function "do_lapack") (41)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_rs" (dummy_function "do_lapack") (5)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_rs_cmplx" (dummy_function "do_lapack") (51)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_dlange" (dummy_function "do_lapack") (6)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_dgecon" (dummy_function "do_lapack") (7)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_dtrcon" (dummy_function "do_lapack") (8)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_zgecon" (dummy_function "do_lapack") (9)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_ztrcon" (dummy_function "do_lapack") (10)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_solve_cmplx" (dummy_function "do_lapack") (11)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_solve" (dummy_function "do_lapack") (100)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_qr" (dummy_function "do_lapack") (101)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_chol" (dummy_function "do_lapack") (200)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_chol2inv" (dummy_function "do_lapack") (201)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "qr_coef_real" (dummy_function "do_lapack") (300)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qr_qy_real" (dummy_function "do_lapack") (301)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "det_ge_real" (dummy_function "do_lapack") (302)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qr_coef_cmplx" (dummy_function "do_lapack") (303)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qr_qy_cmplx" (dummy_function "do_lapack") (304)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;

              rdecl "La_svd" (dummy_function "do_lapack") (400)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_svd_cmplx" (dummy_function "do_lapack") (401)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_version" (dummy_function "do_lapack") (1000)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_library" (dummy_function "do_lapack") (1001)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;

              rdecl "bcprofcounts" (dummy_function "do_bcprofcounts") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bcprofstart" (dummy_function "do_bcprofstart") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bcprofstop" (dummy_function "do_bcprofstop") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;

              rdecl "eSoftVersion" (dummy_function "do_eSoftVersion") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "curlVersion" (dummy_function "do_curlVersion") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "curlGetHeaders" (dummy_function "do_curlGetHeaders") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "curlDownload" (dummy_function "do_curlDownload") (0)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false

            ]%string)
        end
    |}
  end.

Optimize Heap.
