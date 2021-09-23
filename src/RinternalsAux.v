(** RinternalsAux.
  Auxiliary definitions for the data structures defined in Rinternals. **)

(* Copyright © 2018 Martin Bodin

  This program is free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301 USA *)

Set Implicit Arguments.
Require Export Rinternals.
From Lib Require Export Common.

Open Scope comp_scope.


(** The C language performs a lot of pointer deferentiation. As a
  convention, we write [p_] for the object referenced by the pointer [p]
  (that is, [p_] stands for [*p] in C), and [p_f] for its field [f]—for
  instance [p_sym] for its [symSxp_struct] part—, that is [p->f] in C. **)


(** * Accessors **)

(** In some place in the R source code, only five digits are used to store
  the type of basic language element. This is an issue as [FunSxp] is
  associated with the value 99, which is greater than $2^5$ #2<sup>5</sup>#.
  The following function maps [FunSxp] to [CloSxp], effectivelly mapping
  a general [SExpType] to a [SExpType] stored in only five bits.
  We have indeed $99 \bmod 2^5 = 3$ #99 mod 2<sup>5</sup> = 3#. **)
Definition SExpType_restrict t :=
  match t with
  | FunSxp => CloSxp
  | _ => t
  end.

Lemma SExpType_restrict_idem : forall t,
  SExpType_restrict (SExpType_restrict t) = SExpType_restrict t.
Proof. introv. destruct* t. Qed.

Lemma SExpType_restrict_not_FunSxp : forall t,
  t <> FunSxp ->
  SExpType_restrict t = t.
Proof. introv. destruct* t. Qed.

Definition TYPE_BITS := 5.
Definition MAX_NUM_SEXPTYPE := 2 ^ TYPE_BITS.

Definition all_SExpTypes : list SExpType.
Proof. list_all_constructors. Defined.

(** All the SExpTypes that can be stored in an object. **)
Definition all_storable_SExpTypes : list SExpType.
Proof.
  let rec filter l :=
    match l with
    | nil => l
    | NewSxp :: ?l => filter l
    | FreeSxp :: ?l => filter l
    | FunSxp :: ?l => filter l
    | ?t :: ?l => let r := filter l in constr:(t :: r)
    end in
  let l := eval unfold all_SExpTypes in all_SExpTypes in
  let l := filter l in
  exact l.
Defined.

Lemma SExpType_restrict_all_storable_SExpTypes : forall t,
  mem t all_storable_SExpTypes ->
  SExpType_restrict t = t.
Proof. introv M. unfolds all_storable_SExpTypes. explode_list M; substs~. Qed.

Definition bool_to_nat (b : bool) : nat :=
  if b then 1 else 0.
Coercion bool_to_nat : bool >-> nat.

Definition SExpType_to_nat t :=
  match t with
  | NilSxp => 0
  | SymSxp => 1
  | ListSxp => 2
  | CloSxp => 3
  | EnvSxp => 4
  | PromSxp => 5
  | LangSxp => 6
  | SpecialSxp => 7
  | BuiltinSxp => 8
  | CharSxp => 9
  | LglSxp => 10
  | IntSxp => 13
  | RealSxp => 14
  | CplxSxp => 15
  | StrSxp => 16
  | DotSxp => 17
  | AnySxp => 18
  | VecSxp => 19
  | ExprSxp => 20
  | BcodeSxp => 21
  | ExtptrSxp => 22
  | WeakrefSxp => 23
  | RawSxp => 24
  | S4Sxp => 25
  | NewSxp => 30
  | FreeSxp => 31
  | FunSxp => 99
  end.
Coercion SExpType_to_nat : SExpType >-> nat.

Definition nat_to_SExpType : nat -> option SExpType.
Proof.
  intro i.
  let rec build_let l :=
    match l with
    | @nil _ => exact None
    | ?t :: ?l =>
      exact (ifb i = t then Some t else ltac:(build_let l))
    end in
  let l := eval unfold all_SExpTypes in all_SExpTypes in
  build_let l.
Defined.

Lemma nat_to_SExpType_correct : forall t i,
  nat_to_SExpType i = Some t <-> i = t.
Proof.
  introv. iff I.
  - unfolds in I. repeat cases_if; inverts I;
      lazymatch goal with
      | C : istrue (decide _) |- _ => rewrite decide_spec in C; rew_bool_eq~ in C
      end.
  - substs. unfolds. destruct t;
      let false_case := rewrite decide_spec in C; rew_bool_eq in C; false~ C in
      repeat (cases_if as C; [ reflexivity || false_case
                             | lazymatch type of C with
                               | ~ istrue (decide (?x = ?x)) => false_case
                               | _ => clear C
                               end ]).
Qed.

Definition get_NonVector e_ :=
  match e_ with
  | SExpRec_NonVector e_ => Some e_
  | _ => None
  end.

Definition get_VectorChar e_ :=
  match e_ with
  | SExpRec_VectorChar e_ => Some e_
  | _ => None
  end.

Definition get_VectorInteger e_ :=
  match e_ with
  | SExpRec_VectorInteger e_ => Some e_
  | _ => None
  end.

(** Logical values and integer values are stored the same way. **)
Definition get_VectorLogical := get_VectorInteger.
Definition SExpRec_VectorLogical := SExpRec_VectorInteger.

Definition get_VectorComplex e_ :=
  match e_ with
  | SExpRec_VectorComplex e_ => Some e_
  | _ => None
  end.

Definition get_VectorReal e_ :=
  match e_ with
  | SExpRec_VectorReal e_ => Some e_
  | _ => None
  end.

Definition get_VectorPointer e_ :=
  match e_ with
  | SExpRec_VectorPointer e_ => Some e_
  | _ => None
  end.


Definition get_SxpInfo e_ :=
  match e_ return SxpInfo with
  | SExpRec_NonVector e_ => e_
  | SExpRec_VectorChar e_ => e_
  | SExpRec_VectorInteger e_ => e_
  | SExpRec_VectorComplex e_ => e_
  | SExpRec_VectorReal e_ => e_
  | SExpRec_VectorPointer e_ => e_
  end.
Coercion get_SxpInfo : SExpRec >-> SxpInfo.

Definition get_SExpRecHeader e_ :=
  match e_ return SExpRecHeader with
  | SExpRec_NonVector e_ => e_
  | SExpRec_VectorChar e_ => e_
  | SExpRec_VectorInteger e_ => e_
  | SExpRec_VectorComplex e_ => e_
  | SExpRec_VectorReal e_ => e_
  | SExpRec_VectorPointer e_ => e_
  end.
Coercion get_SExpRecHeader : SExpRec >-> SExpRecHeader.


Definition get_primSxp e_ :=
  match e_ with
  | primSxp e_prim => Some e_prim
  | _ => None
  end.

Definition get_symSxp e_ :=
  match e_ with
  | symSxp e_sym => Some e_sym
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

Definition map_sxpinfo_in_header f h :=
  make_SExpRecHeader_direct
    (f (sxpinfo h))
    (attrib h)
    (*gengc_prev_node h*)
    (*gengc_next_node h*).

Definition map_header_NonVector_SExpRec f e_ :=
  make_NonVector_SExpRec
    (f (NonVector_SExpRec_header e_))
    (NonVector_SExpRec_data e_).

Definition map_header_Vector_SExpRec T f (e_ : Vector_SExpRec T) :=
  make_Vector_SExpRec
    (f (Vector_SExpRec_header e_))
    (Vector_SExpRec_vecsxp e_).

Definition map_header f e_ :=
  match e_ with
  | SExpRec_NonVector e_ =>
    SExpRec_NonVector (map_header_NonVector_SExpRec f e_)
  | SExpRec_VectorChar e_ =>
    SExpRec_VectorChar (map_header_Vector_SExpRec f e_)
  | SExpRec_VectorInteger e_ =>
    SExpRec_VectorInteger (map_header_Vector_SExpRec f e_)
  | SExpRec_VectorComplex e_ =>
    SExpRec_VectorComplex (map_header_Vector_SExpRec f e_)
  | SExpRec_VectorReal e_ =>
    SExpRec_VectorReal (map_header_Vector_SExpRec f e_)
  | SExpRec_VectorPointer e_ =>
    SExpRec_VectorPointer (map_header_Vector_SExpRec f e_)
  end.

Definition map_sxpinfo f :=
  map_header (map_sxpinfo_in_header f).

Definition set_named_sxpinfo n i_info :=
  make_SxpInfo (SExpType_restrict (type i_info))
    (scalar i_info) (obj i_info) (alt i_info) (gp i_info)
    (*mark i_info*) (*debug i_info*) (*trace i_info*) (*spare i_info*) (*gcgen i_info*)
    n.

Definition set_named n :=
  map_sxpinfo (set_named_sxpinfo n).

Definition set_named_temporary :=
  set_named named_temporary.

Definition set_named_unique :=
  set_named named_unique.

Definition set_named_plural :=
  set_named named_plural.

Definition map_gp_sxpinfo f i_info :=
  make_SxpInfo (SExpType_restrict (type i_info))
    (scalar i_info) (obj i_info) (alt i_info) (f (gp i_info))
    (*mark i_info*) (*debug i_info*) (*trace i_info*) (*spare i_info*) (*gcgen i_info*)
    (named i_info).

Definition set_gp_sxpinfo n i_info :=
  map_gp_sxpinfo (fun _ => n) i_info.

Definition set_gp n :=
  map_sxpinfo (set_gp_sxpinfo n).

Definition map_gp f :=
  map_sxpinfo (map_gp_sxpinfo f).

Definition set_type_sxpinfo t i_info :=
  make_SxpInfo (SExpType_restrict t)
    (scalar i_info) (obj i_info) (alt i_info) (gp i_info)
    (*mark i_info*) (*debug i_info*) (*trace i_info*) (*spare i_info*) (*gcgen i_info*)
    (named i_info).

Definition set_type t :=
  map_sxpinfo (set_type_sxpinfo t).

Definition set_obj_sxpinfo o i_info :=
  make_SxpInfo (SExpType_restrict (type i_info))
    (scalar i_info) o (alt i_info) (gp i_info)
    (*mark i_info*) (*debug i_info*) (*trace i_info*) (*spare i_info*) (*gcgen i_info*)
    (named i_info).

Definition set_obj_direct o :=
  map_sxpinfo (set_obj_sxpinfo o).

Definition set_car_list_direct car l_list :=
  make_ListSxp_struct_direct car (list_cdrval l_list) (list_tagval l_list).

Definition set_cdr_list_direct cdr l_list :=
  make_ListSxp_struct_direct (list_carval l_list) cdr (list_tagval l_list).

Definition set_tag_list_direct tag l_list :=
  make_ListSxp_struct_direct (list_carval l_list) (list_cdrval l_list) tag.

Definition set_attrib_direct a :=
  map_header (fun h => make_SExpRecHeader_direct (sxpinfo h) a).

Definition get_VecSxp_length e_ :=
  match e_ with
  | SExpRec_NonVector e_ => None
  | SExpRec_VectorChar e_ => Some (VecSxp_length e_)
  | SExpRec_VectorInteger e_ => Some (VecSxp_length e_)
  | SExpRec_VectorComplex e_ => Some (VecSxp_length e_)
  | SExpRec_VectorReal e_ => Some (VecSxp_length e_)
  | SExpRec_VectorPointer e_ => Some (VecSxp_length e_)
  end.

Definition update_Vector_SExpRec A (v : Vector_SExpRec A) (data : ArrayList.array A) := {|
    Vector_SExpRec_header := v ;
    Vector_SExpRec_vecsxp := {|
        VecSxp_length := VecSxp_length v ;
        VecSxp_truelength := VecSxp_truelength v ;
        VecSxp_data := data
      |}
  |}.

Definition VecSxp_with_truelength A (e_ : VecSxp_struct A) v := {|
    VecSxp_length := VecSxp_length e_ ;
    VecSxp_truelength := v ;
    VecSxp_data := VecSxp_data e_
  |}.

Definition Vector_SExpRec_with_truelength A (e_ : Vector_SExpRec A) v := {|
    Vector_SExpRec_header := Vector_SExpRec_header e_ ;
    Vector_SExpRec_vecsxp := VecSxp_with_truelength e_ v
  |}.



(** * Instances **)

(** ** Comparable Instances **)

Instance SExpType_Comparable : Comparable SExpType.
Proof. prove_comparable_trivial_inductive. Defined.

Instance SExpType_named_field : Comparable named_field.
Proof. prove_comparable_trivial_inductive. Defined.

Instance SExpRec_Inhab : Inhab SExpRec.
Proof.
  apply Inhab_of_val.
  refine (make_NonVector_SExpRec
            (make_SExpRecHeader_direct
              (make_SxpInfo NilSxp false false false nbits_init named_plural) None)
            (make_ListSxp_struct_direct None None None)).
Defined.

Instance SEXP_Comparable : Comparable SEXP.
Proof. prove_comparable_simple_inductive. Defined.

Instance character_Inhab : Inhab character.
Proof. apply Inhab_of_val. repeat constructors. Qed.

Instance double_Inhab : Inhab double.
Proof. apply Inhab_of_val. repeat constructors. Qed.

Instance Rcomplex_Inhab : Inhab Rcomplex.
Proof. apply Inhab_of_val. repeat constructors. Qed.

Instance Rcomplex_comparable : Comparable Rcomplex.
Proof. prove_comparable_simple_inductive. Defined.


(** ** Ordering the [named_field] type **)

Definition named_field_lt n1 n2 :=
  match n1, n2 with
  | (named_temporary | named_unique), named_plural
  | named_temporary, named_unique => true
  | _, _ => false
  end.

Instance named_field_Lt : Lt named_field :=
  Build_Lt named_field_lt.

Instance named_field_Lt_Decidable : forall n1 n2 : named_field,
  Decidable (n1 < n2).
Proof. introv. applys* Decidable_equiv (named_field_lt n1 n2). typeclass. Defined.

Definition named_field_le n1 n2 :=
  decide (n1 = n2 \/ n1 < n2).

Instance named_field_Le : Le named_field :=
  Build_Le named_field_le.

Instance named_field_Le_Decidable : forall n1 n2 : named_field,
  Decidable (n1 <= n2).
Proof. introv. applys* Decidable_equiv (named_field_le n1 n2). typeclass. Defined.

Definition named_field_gt n1 n2 :=
  decide (n2 < n1).

Instance named_field_Gt : Gt named_field :=
  Build_Gt named_field_gt.

Instance named_field_Gt_Decidable : forall n1 n2 : named_field,
  Decidable (n1 > n2).
Proof. introv. applys* Decidable_equiv (named_field_gt n1 n2). typeclass. Defined.

Definition named_field_ge n1 n2 :=
  decide (n1 = n2 \/ n1 > n2).

Instance named_field_Ge : Ge named_field :=
  Build_Ge named_field_ge.

Instance named_field_Ge_Decidable : forall n1 n2 : named_field,
  Decidable (n1 >= n2).
Proof. introv. applys* Decidable_equiv (named_field_ge n1 n2). typeclass. Defined.
