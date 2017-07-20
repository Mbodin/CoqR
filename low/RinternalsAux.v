(** RinternalsAux.
* Auxiliary definitions for the data structures defined in Rinternals. **)

Set Implicit Arguments.
Require Export Rinternals Shared.


(** * Instances **)

Instance SExpType_Comparable : Comparable SExpType.
  prove_comparable_simple_inductive.
Defined.


(** * Accessors **)

Definition get_primSxp e :=
  match e with
  | primSxp p => Some p
  | _ => None
  end.

Definition get_listSxp e :=
  match e with
  | listSxp l => Some l
  | _ => None
  end.

Definition get_envSxp e :=
  match e with
  | envSxp e => Some e
  | _ => None
  end.

Definition get_cloSxp e :=
  match e with
  | cloSxp c => Some c
  | _ => None
  end.

Definition get_promSxp e :=
  match e with
  | promSxp p => Some p
  | _ => None
  end.

Definition set_named_sxpinfo i n :=
  make_SxpInfo (type i) (obj i) n (mark i) (debug i) (trace i) (spare i) (gcgen i).

Definition set_named_to e n :=
  make_SExpRec
    (let h := SExpRec_header e in
     make_SExpRecHeader
       (set_named_sxpinfo (sxpinfo h) n)
       (attrib h)
       (gengc_prev_node h)
       (gengc_next_node h))
    (SExpRec_data e).

Definition set_named e :=
  set_named_to e named_plural.

