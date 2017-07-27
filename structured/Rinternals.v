(** Rinternals.
 * The internals presented in Low.Rinternals are untyped: each basic
 * language element (SExprRec) are built on three pointers, without
 * further explanation.
 * But the R interpreter assumes that some of these pointers are NULL,
 * other pointing to a simple basic language element, and other to
 * arrays.  This files makes this explicit.
 * A lot of this file is interpretation from https://cran.r-project.org/doc/manuals/r-release/R-lang.html *)


Definition framePointer := int.

(** Basic language elements (BLE). Each BLE corresponds to a SExpType. **)
Inductive BLE : Type :=
  | BLENil : BLE (** A special value, equivalent to the NULL pointer. **)
  | BLESym : string -> BLE (** A variable. **)
  | BLEList : BLE (** Element **) -> BLE (** Rest of the list **) -> option string (** The name of the element **) -> BLE (** An untyped Lisp-style list. **) (* FIXME: Wouldn’t it be better to define it as (list (BLE * option string)? What level of abstraction should we have here? *)
  | BLEClo : BLE (** The argument list; represented as a Lisp-style list of symbols. **) -> Expr (** Closure body **) -> environment -> BLE (** A closure. **)
  | BLEEnv : framePointer -> option BLE (** The parent environment **) -> BLE (** An environment. **)
  | BLEProm : option BLE (** The value, if the promise already has been evaluated **) -> BLE (** The expression to be evaluated **) -> BLE (** The environment **) -> BLE (** A promise, that is an expression that may not be evaluated. **)
  | BLELand : BLE (** Element **) -> BLE (** Rest of the list **) -> option string (** The name of the element **) -> BLE (** Language constructs, implemented as a list **) (* TODO: Understand this. *)
  | BLESpecial : internal -> BLE (** Internal functions directly manipulating the promises **)
  | BLEBuiltin : primitive -> BLE (** Built-in functions, in call-by-value **)
  | BLEChar : string -> BLE (** A string, for internal usage **)
  | BLELgl : (** Length of the array made implicit **) BLE list (** A pointer to the values of the array **) -> BLE (** A vector containing logical values **)
  | BLEInt : (** Length of the array made implicit **) BLE list (** A pointer to the values of the array **) -> BLE (** A vector containing logical values **)
  | BLEReal : (** Length of the array made implicit **) BLE list (** A pointer to the values of the array **) -> BLE (** A vector containing double-precision values **)
  | BLECplx : (** Length of the array made implicit **) BLE list (** A pointer to the values of the array **) -> BLE (** A vector containing double-precision complex values **)
  | BLEStr : (** Length of the array made implicit **) BLE list (** A pointer to the values of the array **) -> BLE (** A vector containing character values **)
  | BLEDot : BLE (** Element **) -> BLE (** Rest of the list **) -> option string (** The name of the element **) -> BLE (** The special list of arguments of a function with a “...” argument **)
  | BLEAny : False -> BLE (** TODO: Understand this. **)
  | BLEVec : (** Length of the array made implicit **) BLE list (** A pointer to the values of the array **) -> BLE (** Generic vectors **)
  | BLEExpr : (** Length of the array made implicit **) BLE list (** A pointer to the values of the array **) -> BLE (** Expression vectors vectors **)
  | BLEBcode : True (* TODO: Represent this as a Coq function? *) -> BLE (** An internal byte code **)
  | BLEExtptr : False (* TODO: Represent this as a Coq function? *) -> BLE (** External pointer **)
  | BLEWeakref : False (* TODO: Represent this as a Coq function? *) -> BLE (** Weak reference: it is similar than the external pointer, but never freed by the garbage collector **)
  | BLERaw : False (* TODO *) -> BLE (** A vector containing bytes **)
  | BLES4 : False (* TODO *) -> BLE (** A S4 object **)
  | BLENew : BLE (** A fresh node without any useful data, used by the garbage collector **)
  | BLEFree : BLE (** A node without any useful data, freed by the garbage collector **)
  | BLEFun : BLE (** A closure or a built-in **) (* TODO: Understand where this is used. *)

with BLE_attrib :=
  | make_BLE_attrib : BLE -> (
  .

