(** intuitionR
* In the original paper “R: A Language for Data Analysis and
* Graphics”, the authors describe a fairly simple intuition on how the
* R language should behave.
* This file formalises this intuition. **)


Definition framePointer := int.

Record environment := make_environment {
    frame :> framePointer ;
    parent : option environment
  }.

Inductive basicLanguagueElement : Type :=
  | Symbol : string -> basicLanguagueElement
  | Cons : object -> object -> option string -> basicLanguagueElement
  | Environment : environment -> basicLanguagueElement
  | String : string -> basicLanguagueElement
  | Vector : list ? -> basicLanguagueElement
  .

Record object : Type := make_object {
    object_data :> basicLanguagueElement ;
    object_attributes : string -> option attribute
  }.

(* TODO: Semantics. *)
