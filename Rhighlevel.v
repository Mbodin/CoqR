(** Rhighlevel.v
* In the original paper “R: A Language for Data Analysis and
* Graphics”, the authors describe a fairly simple intuition on how the
* R language should behave.
* This file formalises this intuition. **)


Definition framePointer := int.

Record environment := make_environment {
    frame :> framePointer ;
    parent : option environment
  }.

Definition value :=
  | Nil
  .

Record object : Type := make_object {
    object_data :> value ;
    object_attributes : string -> option value
  }.

Inductive Expr :=
  | EvaluatedExpr : object -> Expr
  | LazyExpr : environment -> Expr -> Expr -> Expr (** Application function **)
  | Symbol : string -> Expr
  .

Inductive basicLanguagueElement : Type :=
  | BLENil : basicLanguagueElement (** A NULL pointer. **)
  | BLEList : list (basicLanguagueElement * option string) -> basicLanguagueElement (** An untyped Lisp-style list. **)
  | BLEClo : string list (** The argument list; internally represented as a Lisp-style list of symbols. **) -> Expr (** Closure body **) -> environment -> basicLanguagueElement (** A closure. **)
  | BLEEnv : environment -> basicLanguagueElement (** An environment. **)
  | BLEProm : Expr -> basicLanguagueElement (** A promise, that is an expression that may not be evaluated. **)
  | String : string -> basicLanguagueElement
  | Vector : list ? -> basicLanguagueElement
  .

Inductive frameValue :=
  | Missing : frameValue
  | FrameExpr : Expr -> frameValue
  .

Definition frame := variable -> option frameValue.

(* TODO: Semantics. *)

