(** Rexpressions.
 * The internals presented in Low.Rinternals are untyped: each basic
 * language element (SExprRec) are built on three pointers, without
 * further explanation.
 * But the R interpreter assumes that some of these pointers are NULL,
 * other pointing to a simple basic language element, and other to
 * arrays.  This files makes this explicit.
 * A lot of this file is interpretation from https://cran.r-project.org/doc/manuals/r-release/R-lang.html *)

(* TODO
Definition framePointer := int.

(** Basic language elements (BLE). Each BLE corresponds to a SExpType. **)
Inductive BLE : Type :=
  | BLENil : BLE (** A special value, equivalent to the NULL pointer. **)
  | BLESym : string -> BLE (** A variable. **)
  | BLEList : BLE_list -> BLE (** An untyped list. **)
  | BLEClo : BLE_list (** The argument list **) -> BLE (** Closure body **) -> environment -> BLE (** A closure. **)
  | BLEEnv : framePointer -> option BLE (** The parent environment **) -> BLE (** An environment. **)
  | BLEProm : option BLE (** The value, if the promise already has been evaluated **) -> BLE (** The expression to be evaluated **) -> environment (** The environment **) -> BLE (** A promise, that is an expression that may not be evaluated. **)
  | BLELang : BLE (** Function to be called **) -> BLE_List (** Arguments **) -> BLE (** Language constructs **)
  | BLESpecial : internal -> BLE (** Internal functions directly manipulating the promises **)
  | BLEBuiltin : primitive -> BLE (** Built-in functions, in call-by-value **)
  | BLEChar : string -> BLE (** A string, for internal usage **)
  | BLELgl : BLE list -> BLE (** A vector containing logical values **)
  | BLEInt : BLE list -> BLE (** A vector containing integer values **)
  | BLEReal : BLE list -> BLE (** A vector containing double-precision values **)
  | BLECplx : BLE list -> BLE (** A vector containing double-precision complex values **)
  | BLEStr : BLE list -> BLE (** A vector containing character values **)
  | BLEDot : BLE_list -> BLE (** The special list of arguments of a function associated with the “...” argument **)
  | BLEAny : False -> BLE (** TODO: Understand this. **)
  | BLEVec : BLE list -> BLE (** Generic vectors **)
  | BLEExpr : BLE list -> BLE (** Expression vectors **)
  (* We probably do not want to model these objects for now.
  | BLEBcode : True (* TODO: Represent this as a Coq function? *) -> BLE (** An internal byte code **)
  | BLEExtptr : False (* TODO: Represent this as a Coq function? *) -> BLE (** External pointer **)
  | BLEWeakref : False (* TODO: Represent this as a Coq function? *) -> BLE (** Weak reference: it is similar than the external pointer, but never freed by the garbage collector **)
  | BLERaw : False (* TODO *) -> BLE (** A vector containing bytes **)
  | BLES4 : False (* TODO *) -> BLE (** A S4 object **)
  *)

with BLE_List := list (BLE (** Element **) * option string (** Optionnal tag **))

with BLE_attrib := TODO
  .
*)

