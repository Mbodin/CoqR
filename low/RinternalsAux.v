(** RinternalsAux.
 * Auxiliary definitions for the data structures defined in Rinternals. **)

Set Implicit Arguments.
Require Export Rinternals Shared.


(* TODO: Copy the following paragraph to the draft. *)
(** The C language performs a lot of pointer deferentiation. As a
 * convention, we write [p_] for the object referenced by the pointer [p]
 * (that is, [p_] stands for [*p] in C), and [p_f] for its field [f]—for
 * instance [p_sym] for its [symSxp_struct] part—, that is [p->f] in C. **)


(** * Instances **)

Instance SExpType_Comparable : Comparable SExpType.
  prove_comparable_simple_inductive.
Defined.


(** * Accessors and Smart Constructors **)

Definition get_primSxp e_ :=
  match e_ with
  | primSxp e_prim => Some e_prim
  | _ => None
  end.

Definition get_listSxp e_ :=
  match e_ with
  | listSxp e_list => Some e_list
  | _ => None
  end.

Definition get_envSxp e_ :=
  match e_ with
  | envSxp e_env => Some e_env
  | _ => None
  end.

Definition get_cloSxp e_ :=
  match e_ with
  | cloSxp e_clo => Some e_clo
  | _ => None
  end.

Definition get_promSxp e_ :=
  match e_ with
  | promSxp e_prom => Some e_prom
  | _ => None
  end.

Definition set_named_sxpinfo n i_info :=
  make_SxpInfo (type i_info) (obj i_info) n (mark i_info) (debug i_info) (trace i_info) (spare i_info) (gcgen i_info).

Definition set_named n e_ :=
  make_SExpRec
    (let h := SExpRec_header e_ in
     make_SExpRecHeader
       (set_named_sxpinfo n (sxpinfo h))
       (attrib h)
       (gengc_prev_node h)
       (gengc_next_node h))
    (SExpRec_data e_).

Definition set_named_plural :=
  set_named named_plural.

Definition set_type_sxpinfo t i_info :=
  make_SxpInfo t (obj i_info) (named i_info) (mark i_info) (debug i_info) (trace i_info) (spare i_info) (gcgen i_info).

Definition set_type t e_ :=
  make_SExpRec
    (let h := SExpRec_header e_ in
     make_SExpRecHeader
       (set_type_sxpinfo t (sxpinfo h))
       (attrib h)
       (gengc_prev_node h)
       (gengc_next_node h))
    (SExpRec_data e_).

Definition set_gp := ?.

Definition set_car_list car l_list :=
  make_ListSxp_struct car (list_cdrval l_list) (list_tagval l_list).


(** A smart constructor for SxpInfo **)
Definition build_SxpInfo type : SxpInfo :=
  make_SxpInfo type false named_temporary false false false false false.

(** The pointers [gengc_prev_node] and [gengc_next_node] are only used
 * by the garbage collector of R. We do not need them here as memory
 * allocation is not targetted by this formalisation. We thus offer the
 * following smart constructor for the type [SExpRecHeader]. **)
Definition build_SExpRecHeader type attrib : SExpRecHeader :=
  make_SExpRecHeader (build_SxpInfo type) attrib None None.

(** The Nil object TODO **)
Definition Nil_SExpRec :=
  make_SExpRec
    (make_SExpRecHeader NilSxp None)
    ?.

