(** Rhighlevel.
* In the original paper “R: A Language for Data Analysis and
* Graphics”, the authors describe a fairly simple intuition on how the
* R language should behave.
* This file formalises this intuition. **)


Definition framePointer := int.

Record environment := make_environment {
    frame :> framePointer ;
    parent : option environment
  }.

Record object value : Type := make_object {
    object_data :> value ;
    object_attributes : string -> option value
  }.

Inductive value :=
  | value_nil : value
  | value_clo : string list (** Argument list **) -> expr (** Closure body **) -> environment -> value
  | value_string : string -> value
with expr :=
  | expr_value : object value -> expr
  | expr_app : environment -> expr -> expr -> expr (** Application function **)
  | expr_symbol : environment -> string -> expr
  .

Definition Robject : object value.

Coercion expr_value : Robject >-> expr

Inductive frame_value :=
  | frame_value_missing : frame_value
  | frame_value_expr : expr -> frame_value
  .

Definition frame := variable -> option frameValue.

(* TODO: Semantics. *)

