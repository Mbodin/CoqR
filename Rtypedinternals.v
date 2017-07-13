(** Rtypedinternals.v
* The internals presented in Rinternals are untyped: each basic
* language element (SExprRec) are built on three pointers, without
* further explanation.
* But the R interpreter assumes that these pointers are *)


Definition framePointer := int.

(** Basic language elements (BLE). Each BLE corresponds to a SExpType. **)
Inductive BLE : Type :=
  | BLENil : BLE (** A NULL pointer. **)
  | BLESym : string -> BLE (** A variable. **)
  | BLEList : BLE (** Element **) -> BLE (** Rest of the list **) -> option string (** The name of the element **) -> BLE (** An untyped Lisp-style list. **)
  | BLEClo : BLE (** The argument list; represented as a Lisp-style list of symbols. **) -> Expr (** Closure body **) -> environment -> BLE (** A closure. **)
  | BLEEnv : framePointer -> option BLE (** The parent environment **) -> BLE (** An environment. **)
  | BLEProm : Expr -> basicLanguagueElement (** A promise, that is an expression that may not be evaluated. **)
  | String : string -> basicLanguagueElement
  | Vector : list ? -> basicLanguagueElement
  .

