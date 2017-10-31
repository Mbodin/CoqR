(** Debug
  Contains debuging functions. **)

open Low

type funtype =
    | Result_unit of globals -> runs_type -> state -> unit result
    | Result_int of globals -> runs_type -> state -> int result
    | Result_float of globals -> runs_type -> state -> float result
    | Result_pointer of globals -> runs_type -> state -> sExpRec_pointer result

    | Argument_unit of unit -> funtype
    | Argument_int of int -> funtype
    | Argument_float of float -> funtype
    | Argument_pointer of sExpRec_pointer -> funtype

