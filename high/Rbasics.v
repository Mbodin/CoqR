(* TODO: Clean this file, or merge it with Rstructures.v *)

(** Rbasic.v
 * This file provides a higher level view from the types defined in the file Rinternals.v.
 * This file will probably move to Rhighlevel at some point. **)

Inductive mode : Type :=
  (* | mode_raw *)
  | mode_numeric
  | mode_complex
  | mode_character
  | mode_logical
  | mode_list
  | mode_function
  .

Inductive value (base_type : Type) : Type :=
  | value_NA : value base_type
  | value_value : base_type -> value base_type
  .

Definition mode_to_type m : Type :=
  match m with
  | mode_numeric => (* Need Flocq *)
  | mode_complex =>
  | mode_character =>
  | mode_logical => bool
  | mode_list =>
  | mode_function =>
  end.

Coercion mode_to_type : mode >-> Type.

Record object : Type := make_object {
    object_mode : mode ;
    object_data :> list (value object_mode) ;
    object_attributes : string -> option ?
  }.

Definition object_length (o : object) :=
  length o.

(* Coercions can be extracted from https://github.com/wch/r-source/blob/trunk/src/main/coerce.c *)

(* Context to be extracted from https://github.com/wch/r-source/blob/trunk/src/main/context.c *)

(* List of constructs: https://github.com/wch/r-source/blob/trunk/src/main/names.c and https://github.com/wch/r-source/blob/trunk/src/include/Internal.h *)

(* Relevant link: https://cran.r-project.org/doc/manuals/r-release/R-lang.html *)

