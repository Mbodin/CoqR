
(* To be related to https://github.com/wch/r-source/blob/trunk/src/include/Rinternals.h *)

Inductive mode : Type :=
  | mode_numeric
  | mode_complex
  | mode_character
  | mode_logical
  | mode_list
  | mode_function
  .

Record objects : Type :=
  make_object {
    object_mode : mode ;
    object_length : nat
  }.

Inductive value (base_type : Type) : Type :=
  | value_NA : value base_type
  | value_value : base_type -> value base_type
  .

Coercion value_value : forall T, T -> value T.

(* Coercions can be extracted from https://github.com/wch/r-source/blob/trunk/src/main/coerce.c *)

(* Context to be extracted from https://github.com/wch/r-source/blob/trunk/src/main/context.c *)

(* List of constructs: https://github.com/wch/r-source/blob/trunk/src/main/names.c and https://github.com/wch/r-source/blob/trunk/src/include/Internal.h *)

