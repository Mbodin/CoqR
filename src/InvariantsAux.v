(** InvariantsAux.
  Contains lemmae about the invariants stated in Invariants. **)

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
Require Import TLC.LibBag Paco.paco.
Require Export Invariants.

Open Scope list_scope. (* FIXME: How to disable some notations of LibBag? *)

(** * Predicates about the memory **)

(** ** Valid pointers **)

Lemma bound_such_that_weaken : forall S (P1 P2 : _ -> Prop) p,
  (forall p_, P1 p_ -> P2 p_) ->
  bound_such_that S P1 p ->
  bound_such_that S P2 p.
Proof. introv I (p_&E&H). exists* p_. Qed.

Lemma bound_such_that_bound : forall S P p,
  bound_such_that S P p ->
  bound S p.
Proof. introv (p_&E&H). exists* p_. Qed.

Lemma bound_write : forall S S' p p' p_,
  write_SExp S p p_ = Some S' ->
  bound S p' ->
  bound S' p'.
Proof.
  introv W (p'_&R&_). tests D: (p = p').
  - exists p_. splits~. applys~ read_write_SExp_eq W.
  - exists p'_. splits~. rewrites~ >> read_write_SExp_neq W D.
Qed.

Lemma bound_write_exact : forall S S' p p_,
  write_SExp S p p_ = Some S' ->
  bound S' p.
Proof. introv W. exists p_. splits~. applys~ read_write_SExp_eq W. Qed.

(** ** Typed pointers **)

Lemma may_have_types_bound : forall S p l,
  may_have_types S l p ->
  bound S p.
Proof. introv. apply* bound_such_that_weaken. Qed.

Lemma bound_may_have_types : forall S p,
  bound S p ->
  may_have_types S all_SExpTypes p.
Proof. introv B. applys~ bound_such_that_weaken B. introv _. destruct type; Mem_solve. Qed.

Lemma may_have_types_nil : forall S p,
  ~ may_have_types S nil p.
Proof. introv (p_&E&M). applys~ BagInEmpty_list M. Qed.

Lemma may_have_types_cons : forall S t l p,
  may_have_types S (t :: l) p <->
  may_have_types S ([t]) p \/ may_have_types S l p.
Proof.
  introv. iff I.
  - forwards (p_&E&M): (rm I). apply BagIn_cons in M. forwards [M'|M']: (rm M).
    + left. exists p_. splits~. apply~ BagInSingle_list.
    + right. exists* p_.
  - forwards [(p_&E&M)|(p_&E&M)]: (rm I); exists p_; splits~; apply* BagIn_cons.
    left. apply~ BagInSingle_list.
Qed.

Lemma may_have_types_merge : forall S p l1 l2,
  may_have_types S l1 p ->
  may_have_types S l2 p ->
  may_have_types S (l1 \n l2) p.
Proof.
  introv (p1_&E1&M1) (p2_&E2&M2).
  rewrite E1 in E2. inverts E2. exists p2_. splits~.
  rewrite~ BagInter_list.
Qed.

Lemma may_have_types_merge_singl : forall S p t1 t2,
  may_have_types S ([t1]) p ->
  may_have_types S ([t2]) p ->
  t1 = t2.
Proof.
  introv (p_1&R1&T1) (p_2&R2&T2). rewrite R1 in R2. inverts R2. transitivity (type p_2).
  - symmetry. eapply BagInSingle_list. apply T1.
  - eapply BagInSingle_list. apply T2.
Qed.

Lemma may_have_types_weaken : forall S p l1 l2,
  may_have_types S l1 p ->
  l1 \c l2 ->
  may_have_types S l2 p.
Proof. introv T I. applys~ bound_such_that_weaken T. introv M. applys~ BagInIncl M I. Qed.

Lemma may_have_types_write_SExp : forall S S' p p' p_ l,
  write_SExp S p p_ = Some S' ->
  may_have_types S l p' ->
  p <> p' ->
  may_have_types S' l p'.
Proof. introv W (p'_&E&T) D. exists p'_. splits~. rewrites~ >> read_write_SExp_neq W D. Qed.

Lemma may_have_types_write_SExp_eq : forall S S' p p_ l,
  write_SExp S p p_ = Some S' ->
  type p_ \in l ->
  may_have_types S' l p.
Proof. introv W I. exists p_. splits~. applys~ read_write_SExp_eq W. Qed.

Lemma may_have_types_write_SExp_eq_exact : forall S S' p p_ t,
  write_SExp S p p_ = Some S' ->
  type p_ = t ->
  may_have_types S' ([t]) p.
Proof. introv W E. applys~ may_have_types_write_SExp_eq W. apply~ BagInSingle_list. Qed.

Lemma may_have_types_write_SExp_inv : forall S S' p p' p_ l,
  write_SExp S p p_ = Some S' ->
  may_have_types S' l p' ->
  p <> p' ->
  may_have_types S l p'.
Proof. introv W (p'_&E&T) D. exists p'_. splits~. rewrites~ <- >> read_write_SExp_neq W D. Qed.

Lemma may_have_types_read_SExp : forall S l p p_,
  may_have_types S l p ->
  read_SExp S p = Some p_ ->
  type p_ \in l.
Proof. introv (p_'&E&T) R. rewrite E in R. inverts~ R. Qed.

Lemma read_SExp_may_have_types_read : forall (S : state) l p p_,
  read_SExp S p = Some p_ ->
  type p_ \in l ->
  may_have_types S l p.
Proof. introv E T. exists p_. splits~. Qed.

Lemma read_SExp_may_have_types_read_exact : forall (S : state) t p p_,
  read_SExp S p = Some p_ ->
  type p_ = t ->
  may_have_types S ([t]) p.
Proof. introv E T. applys read_SExp_may_have_types_read E. substs. Mem_solve. Qed.

(** ** List pointers **)

Fixpoint list_type_ind (Pheader Pcar Ptag : _ -> Prop) S
    (P : list SExpType -> list SExpType -> list SExpType -> SEXP -> Prop)
    (f_nil : forall p l_t l_car l_tag,
       may_have_types S ([NilSxp]) p ->
       P l_t l_car l_tag p)
    (f_cons : forall p l_t l_car l_tag p_ header car cdr tag,
       read_SExp S p = Some p_ ->
       p_ = make_NonVector_SExpRec header (make_ListSxp_struct car cdr tag) ->
       type p_ \in l_t ->
       Pheader header ->
       may_have_types S l_car car ->
       Pcar car ->
       list_type_such_that Pheader Pcar Ptag S l_t l_car l_tag cdr ->
       may_have_types S l_tag tag ->
       Ptag tag ->
       P l_t l_car l_tag cdr ->
       P l_t l_car l_tag p)
    l_t l_car l_tag p (HL : list_type_such_that Pheader Pcar Ptag S l_t l_car l_tag p) : P l_t l_car l_tag p.
  refine (
    match HL in list_type_such_that _ _ _ _ l_t l_car l_tag p return P l_t l_car l_tag p with
    | @list_type_nil _ _ _ _ p l_t l_car l_tag N =>
      f_nil p l_t l_car l_tag N
    | @list_type_cons _ _ _ _ p l_t l_car l_tag N => _
    end).
  destruct N as (p_&E&h&car&cdr&tag&M&H&HH&A&HA&L&T&HT).
  refine (f_cons p l_t l_car l_tag _ _ _ _ _ E M H HH A HA L T HT _).
  applys~ list_type_ind f_nil f_cons.
Defined.

Lemma list_head_may_have_types : forall S Pheader Pcar Ptag l_t l_car l_tag p_,
  list_head_such_that Pheader Pcar Ptag S l_t l_car l_tag p_ ->
  type p_ \in l_t.
Proof. introv (h&car&cdr&tag&M&H&HH&A&HA&L&T&HT). substs~. Qed.

Lemma list_type_may_have_types : forall Pheader Pcar Ptag S l_t l_car l_tag p,
  list_type_such_that Pheader Pcar Ptag S l_t l_car l_tag p ->
  may_have_types S (l_t \u [NilSxp]) p.
Proof.
  introv I. destruct~ I as [? ? ? ? I|? ? ? ? (p_&E&h&car&cdr&tag&M&H&HH&A&AH&L&T&HT)].
  - applys~ may_have_types_weaken I. apply~ BagUnionIncl_right.
  - exists p_. splits~. applys~ BagInIncl H. apply~ BagUnionIncl_left.
Qed.

Lemma list_type_merge : forall Pheader Pcar Ptag S p l1_t l2_t l1_car l2_car l1_tag l2_tag,
  list_type_such_that Pheader Pcar Ptag S l1_t l1_car l1_tag p ->
  list_type_such_that Pheader Pcar Ptag S l2_t l2_car l2_tag p ->
  list_type_such_that Pheader Pcar Ptag S (l1_t \n l2_t) (l1_car \n l2_car) (l1_tag \n l2_tag) p.
Proof.
  introv T1 T2. gen l2_t l2_car l2_tag.
  induction T1 as [? ? ? ? I1|? ? ? ? p1_ h1 car1 cdr1 tag1 E1 M1 H1 HH1 A1 HA1 L1 T1 HT1 IH]
    using list_type_ind; introv T.
  - apply~ list_type_nil.
  - inverts T as T.
    + apply~ list_type_nil.
    + inverts T as (E2&h2&car2&cdr2&tag2&M2&H2&HH2&A2&HA2&L2&T2&HT2).
      rewrite E2 in E1. inversion E1 as [E1']. rewrite E1' in *.
      rewrite M1 in M2. inverts M2.
      apply list_type_cons. exists p1_. splits~. exists h2 car2 cdr2 tag2. splits~.
      * apply BagInter_list. splits~.
      * applys~ may_have_types_merge A1 A2.
      * applys~ may_have_types_merge T1 T2.
Qed.

Lemma list_type_head_such_that_weaken : forall (P1 P2 : _ -> _ -> _ -> _ -> _ -> Prop)
    (P1header P2header P1car P2car P1tag P2tag : _ -> Prop) S l1_t l2_t l1_car l2_car l1_tag l2_tag p_,
  l1_t \c l2_t ->
  l1_car \c l2_car ->
  l1_tag \c l2_tag ->
  (forall p, P1 S l1_t l1_car l1_tag p -> P2 S l2_t l2_car l2_tag p) ->
  (forall p, P1header p -> P2header p) ->
  (forall p, P1car p -> P2car p) ->
  (forall p, P1tag p -> P2tag p) ->
  list_type_head_such_that P1 P1header P1car P1tag S l1_t l1_car l1_tag p_ ->
  list_type_head_such_that P2 P2header P2car P2tag S l2_t l2_car l2_tag p_.
Proof.
  introv I1 I2 I3 I Iheader Icar Itag (h&car&cdr&tag&E&T&HH&Mcar&Hcar&IH&Mtag&Htag).
  exists h car cdr tag. splits~.
  - applys~ BagInIncl I1.
  - applys~ may_have_types_weaken Mcar.
  - applys~ may_have_types_weaken Mtag.
  Optimize Proof.
Qed.

Lemma list_type_weaken : forall (P1header P2header P1car P2car P1tag P2tag : _ -> Prop)
    S p l1_t l2_t l1_car l2_car l1_tag l2_tag,
  l1_t \c l2_t ->
  l1_car \c l2_car ->
  l1_tag \c l2_tag ->
  (forall p, P1header p -> P2header p) ->
  (forall p, P1car p -> P2car p) ->
  (forall p, P1tag p -> P2tag p) ->
  list_type_such_that P1header P1car P1tag S l1_t l1_car l1_tag p ->
  list_type_such_that P2header P2car P2tag S l2_t l2_car l2_tag p.
Proof.
  introv I1 I2 I3 Iheader Icar Itag T. gen l2_t l2_car l2_tag.
  induction T as [? ? ? ? I1|? ? ? ? p_ h car cdr tag E M H HH A HA L T HT IH]
    using list_type_ind; introv Incl1 Incl2 Incl3.
  - apply~ list_type_nil.
  - apply list_type_cons. exists p_. splits~. exists h car cdr tag. splits~.
    + applys~ BagInIncl H Incl1.
    + applys~ may_have_types_weaken A Incl2.
    + applys~ may_have_types_weaken T Incl3.
  Optimize Proof.
Qed.

Lemma list_head_such_that_weaken : forall (P1header P2header P1car P2car P1tag P2tag : _ -> Prop)
    S l1_t l2_t l1_car l2_car l1_tag l2_tag p_,
  l1_t \c l2_t ->
  l1_car \c l2_car ->
  l1_tag \c l2_tag ->
  (forall p, P1header p -> P2header p) ->
  (forall p, P1car p -> P2car p) ->
  (forall p, P1tag p -> P2tag p) ->
  list_head_such_that P1header P1car P1tag S l1_t l1_car l1_tag p_ ->
  list_head_such_that P2header P2car P2tag S l2_t l2_car l2_tag p_.
Proof.
  introv I1 I2 I3 Iheader Icar Itag L. applys~ list_type_head_such_that_weaken L.
  introv L'. applys~ list_type_weaken Icar Itag L'.
  Optimize Proof.
Qed.


(** * Invariants about the state **)

Lemma safe_pointer_along_path_from_incl : forall (safe_pointer' : _ -> _ -> Prop) S p path e,
  (forall S p, safe_pointer' S p -> safe_pointer_gen safe_pointer' S p) ->
  safe_pointer' S p ->
  move_along_path_from path S p = Some e ->
  e <> NULL ->
  safe_pointer' S e.
Proof.
  introv Incl OKp E D. gen p e. induction path; introv OKp E D.
  - rewrite move_along_path_from_nil in E. inverts~ E.
  - forwards (e2&E1&E2): move_along_path_from_cons_inv E.
    applys~ IHpath E2. applys~ safe_pointer_along_path_step E1.
    intro_subst. destruct path.
    + rewrite move_along_path_from_nil in E2. inverts~ E2.
    + rewrite move_along_path_from_NULL in E2; [ inverts E2 | discriminate ].
  Optimize Proof.
Qed.

Lemma safe_pointer_along_path_from : forall S p path e,
  safe_pointer S p ->
  move_along_path_from path S p = Some e ->
  e <> NULL ->
  safe_pointer S e.
Proof.
  introv. applys~ safe_pointer_along_path_from_incl.
  clear. introv OKp. rewrite~ <- safe_pointer_rewrite.
Qed.

Lemma safe_pointer_not_NULL : forall S p,
  safe_pointer S p ->
  p <> NULL.
Proof.
  introv OKp E. rewrite safe_pointer_rewrite in OKp.
  forwards (p_&B&?): pointer_bound OKp. substs. rewrite read_SExp_NULL in B. inverts~ B.
Qed.

Lemma no_null_pointer_along_path_from : forall S p p' path,
  safe_pointer S p ->
  (forall s,
    s \in path ->
    ~ null_pointer_exceptions_suffix s) ->
  move_along_path_from path S p = Some p' ->
  p' <> NULL.
Proof.
  introv OKp NE E. gen p. induction path; introv OKp E.
  - rewrite move_along_path_from_nil in E. inverts E. applys~ safe_pointer_not_NULL OKp.
  - forwards (p2&E1&E2): move_along_path_from_cons_inv (rm E).
    rewrite safe_pointer_rewrite in OKp. forwards~ D: no_null_pointer_along_path_step OKp E1.
    + introv NE'. false NE NE'. Mem_solve.
    + applys~ IHpath E2.
      * introv I. applys NE. right~.
      * applys~ safe_pointer_along_path_step OKp E1 D.
Qed.

Lemma safe_SExpRec_along_path_from : forall S p path e e_,
  safe_pointer S p ->
  move_along_path_from path S p = Some e ->
  read_SExp S e = Some e_ ->
  safe_SExpRec S e_.
Proof.
  introv OKp E R. forwards~ OKe: safe_pointer_along_path_from E.
  - intro_subst. rewrite read_SExp_NULL in R. inverts R.
  - rewrite safe_pointer_rewrite in OKe. applys~ safe_SExpRec_read OKe.
Qed.

Lemma safe_pointer_along_path : forall S path e,
  safe_state S ->
  move_along_path path S = Some e ->
  e <> NULL ->
  safe_pointer S e.
Proof.
  introv OKS E D. gen e. induction path; introv E D.
  - applys~ safe_entry_points E.
  - simpl in E. destruct move_along_path eqn:E'.
    + simpl in E. forwards~ OKs: IHpath.
      * intro_subst. rewrite move_along_path_step_NULL in E. inverts E.
      * rewrite safe_pointer_rewrite in OKs. applys~ safe_pointer_along_path_step OKs E.
    + inverts E.
Qed.

Lemma no_null_pointer_along_path : forall S path e,
  safe_state S ->
  move_along_path path S = Some e ->
  ~ null_pointer_exceptions_path path ->
  e <> NULL.
Proof.
  introv OKS E NE D. destruct path.
  - applys~ no_null_pointer_entry_point E.
    introv NE'. apply NE. applys~ null_pointer_exceptions_path_entry_point NE'.
  - simpl in E. destruct move_along_path eqn: E'.
    + forwards~ OKe: safe_pointer_along_path E'.
      * intro_subst. simpl in E. rewrite move_along_path_step_NULL in E. inverts~ E.
      * rewrite safe_pointer_rewrite in OKe. applys~ no_null_pointer_along_path_step OKe p.
        -- introv NE'. apply NE. applys~ null_pointer_exceptions_path_suffix NE'.
           unfolds. applys_eq suffix_cons 1; [apply suffix_nil|reflexivity].
        -- substs. apply E.
    + inverts E.
Qed.

Lemma safe_bindings_along_path : forall S path e,
  safe_state S ->
  move_along_path path S = Some e ->
  e <> NULL ->
  bound S e.
Proof.
  introv OKS E D. forwards~ OKe: safe_pointer_along_path E D.
  rewrite safe_pointer_rewrite in OKe. applys pointer_bound OKe.
Qed.

Lemma safe_SExpRec_along_path : forall S path e e_,
  safe_state S ->
  move_along_path path S = Some e ->
  read_SExp S e = Some e_ ->
  safe_SExpRec S e_.
Proof.
  introv OKS E R. forwards~ OKe: safe_pointer_along_path OKS E.
  - intro_subst. rewrite read_SExp_NULL in R. inverts R.
  - rewrite safe_pointer_rewrite in OKe. applys~ safe_SExpRec_read OKe.
Qed.

Lemma read_bound : forall (S : state) p p_,
  read_SExp S p = Some p_ ->
  bound S p.
Proof. introv E. exists* p_. Qed.

Lemma bound_read : forall (S : state) p,
  bound S p ->
  exists p_, read_SExp S p = Some p_.
Proof. introv (p_&E&_). exists* p_. Qed.

Lemma alloc_SExp_bound : forall S S' e e_,
  alloc_SExp S e_ = (S', e) ->
  bound S' e.
Proof. introv E. applys~ read_bound. applys~ alloc_read_SExp_Some E. Qed.

Lemma alloc_SExp_conserve_old_bindings : forall S S' e e_,
  alloc_SExp S e_ = (S', e) ->
  conserve_old_bindings S S'.
Proof.
  introv A. constructors.
  - (** conserve_old_bindings_bindings **)
    introv (p_&E&_). exists p_. splits~. exists p_. splits~.
    eapply alloc_read_SExp_neq in A.
    + rewrite~ A.
    + intro_subst. erewrite alloc_read_SExp_fresh in E; autos*. inverts* E.
  - (** conserve_old_bindings_entry_point **)
    introv. rewrites* >> move_along_entry_point_alloc_SExp A.
Qed.

Lemma write_SExp_conserve_old_bindings_when_read_None : forall (S S' : state) e e_,
  read_SExp S e = None ->
  write_SExp S e e_ = Some S' ->
  conserve_old_bindings S S'.
Proof.
  introv N W. constructors.
  - (** conserve_old_bindings_bindings **)
    introv (p_&E&_). exists p_. splits~. exists p_. splits~.
    erewrite read_write_SExp_neq; try apply W; autos~.
    intro_subst. rewrite N in E. inverts E.
  - (** conserve_old_bindings_entry_point **)
    introv. rewrites* >> move_along_entry_point_write_SExp W.
Qed.

Lemma state_equiv_conserve_old_bindings : forall (S S' : state),
  state_equiv S S' ->
  conserve_old_bindings S S'.
Proof.
  introv E. constructors.
  - (** conserve_old_bindings_bindings **)
    introv (p_&Ep&_). exists p_. splits~. exists p_. splits~.
    rewrites* <- >> read_SExp_equiv E.
  - (** conserve_old_bindings_entry_point **)
    introv. rewrites* >> move_along_entry_point_same_entry_points E.
Qed.

Lemma only_one_nil_SExpRec : forall S p1 p2 e1 e2 e1_ e2_,
  safe_state S ->
  move_along_path p1 S = Some e1 ->
  move_along_path p2 S = Some e2 ->
  read_SExp S e1 = Some e1_ ->
  read_SExp S e2 = Some e2_ ->
  type e1_ = NilSxp ->
  type e2_ = NilSxp ->
  e1 = e2.
Proof.
  introv Safe M1 M2 R1 R2 T1 T2.
  applys~ only_one_nil Safe; eexists; splits*; apply~ BagInSingle_list.
Qed.

Lemma may_have_types_NilSxp_safe_pointer : forall S globals p,
  safe_state S ->
  safe_globals S globals ->
  may_have_types S ([NilSxp]) p ->
  safe_pointer S p.
Proof.
  introv OKS OKg M. asserts_rewrite (p = read_globals globals R_NilValue).
  - applys~ only_one_nil M. applys~ R_NilValue_may_have_types OKg.
  - applys~ globals_not_NULL_safe OKg. applys~ globals_not_NULL OKg. introv A. inverts A.
Qed.

Lemma conserve_old_bindings_read : forall S S' p p_,
  conserve_old_bindings S S' ->
  read_SExp S p = Some p_ ->
  read_SExp S' p = Some p_.
Proof.
  introv C E. forwards (p1_&E1&(p2_&E2&E3)): conserve_old_bindings_bindings C p.
  - apply* read_bound.
  - rewrite E in E1. inverts E1. substs~.
Qed.

Lemma conserve_old_bindings_bound : forall S S' p,
  conserve_old_bindings S S' ->
  bound S p ->
  bound S' p.
Proof.
  introv C (p_&E&_). forwards (p1_&E1&(p2_&E2&E3)): conserve_old_bindings_bindings C p.
  - apply* read_bound.
  - rewrite E in E1. inverts E1. substs. exists~ p2_.
Qed.

Lemma conserve_old_bindings_may_have_types : forall S S' l p,
  conserve_old_bindings S S' ->
  may_have_types S l p ->
  may_have_types S' l p.
Proof.
  introv C (p_&E&T). forwards (p1_&E1&(p2_&E2&E3)): conserve_old_bindings_bindings C p.
  - apply* read_bound.
  - rewrite E in E1. inverts E1. substs. exists~ p2_.
Qed.

Lemma conserve_old_bindings_may_have_types_inv : forall S S' l p,
  conserve_old_bindings S S' ->
  may_have_types S' l p ->
  bound S p ->
  may_have_types S l p.
Proof.
  introv C (p_&E&T) B. forwards~ (p1_&E1&(p2_&E2&E3)): conserve_old_bindings_bindings C p.
  rewrite E2 in E. inverts E. substs. exists~ p_.
Qed.

Lemma conserve_old_bindings_list_type : forall Pheader Pcar Ptag S S' l_t l_car l_tag p,
  conserve_old_bindings S S' ->
  list_type_such_that Pheader Pcar Ptag S l_t l_car l_tag p ->
  list_type_such_that Pheader Pcar Ptag S' l_t l_car l_tag p.
Proof.
  introv C L. induction L as [? ? ? ? I|? ? ? ? p_ h car cdr tag E M H HH A L T IH]
    using list_type_ind.
  - apply list_type_nil. applys~ conserve_old_bindings_may_have_types C.
  - apply list_type_cons. exists p_. splits~.
    + applys~ conserve_old_bindings_read C.
    + exists h car cdr tag. splits~; applys~ conserve_old_bindings_may_have_types C.
  Optimize Proof.
Qed.

Lemma conserve_old_bindings_list_head : forall Pheader Pcar Ptag S S' l_t l_car l_tag p_,
  conserve_old_bindings S S' ->
  list_head_such_that Pheader Pcar Ptag S l_t l_car l_tag p_ ->
  list_head_such_that Pheader Pcar Ptag S' l_t l_car l_tag p_.
Proof.
  introv C (h&car&cdr&tag&L). exists h car cdr tag. splits; try apply~ L.
  - applys* conserve_old_bindings_may_have_types C.
  - applys* conserve_old_bindings_list_type C.
  - applys* conserve_old_bindings_may_have_types C.
Qed.

Lemma conserve_old_bindings_refl : forall S,
  conserve_old_bindings S S.
Proof. introv. constructors~. introv (p_&E&_). exists p_. splits~. exists* p_. Qed.

Lemma conserve_old_bindings_trans : forall S1 S2 S3,
  conserve_old_bindings S1 S2 ->
  conserve_old_bindings S2 S3 ->
  conserve_old_bindings S1 S3.
Proof.
  introv C1 C2. constructors.
  - (** conserve_old_bindings_bindings **)
    introv (p_&E&_). exists p_. splits~.
    forwards~ E1: conserve_old_bindings_read C1 (rm E).
    forwards~ E2: conserve_old_bindings_read C2 (rm E1).
    exists p_. splits~.
  - (** conserve_old_bindings_entry_point **)
    introv. rewrites >> conserve_old_bindings_entry_point C1.
    rewrites~ >> conserve_old_bindings_entry_point C2.
Qed.

Lemma conserve_old_bindings_move_along_path_step : forall S S' p e e',
  conserve_old_bindings S S' ->
  move_along_path_step p S e = Some e' ->
  move_along_path_step p S' e = Some e'.
Proof.
  introv C E. unfolds in E. destruct (read_SExp S e) eqn: R.
  - unfolds. rewrites~ >> conserve_old_bindings_read C R.
  - inverts~ E.
Qed.

Lemma conserve_old_bindings_move_along_path_from : forall S S' p e e',
  conserve_old_bindings S S' ->
  move_along_path_from p S e = Some e' ->
  move_along_path_from p S' e = Some e'.
Proof.
  introv C M. unfolds move_along_path_from.
  rewrite fold_left_eq_fold_right in *.
  gen e e'. induction (rev p); introv M.
  - inverts~ M.
  - rew_list in *. destruct fold_right eqn: F.
    + simpl in M. forwards M': conserve_old_bindings_move_along_path_step C M.
      erewrite IHl; [apply M'|]. rewrite~ F.
    + inverts~ M.
  Optimize Proof.
Qed.

Lemma conserve_old_bindings_move_along_path : forall S S' p e,
  conserve_old_bindings S S' ->
  move_along_path p S = Some e ->
  move_along_path p S' = Some e.
Proof.
  introv C E. forwards (en&pa&pe&E1&E2&E3): move_along_path_decompose E.
  rewrites >> conserve_old_bindings_entry_point C in E2.
  forwards~ E3': conserve_old_bindings_move_along_path_from C E3.
  forwards E': make_move_along_path E2 E3'. rewrite~ <- E1 in E'.
Qed.

Lemma move_along_path_step_bound : forall S s e e',
  move_along_path_step s S e = Some e' ->
  bound S e.
Proof. introv E. unfolds in E. destruct read_SExp eqn: R; inverts E. eexists. splits*. Qed.

Lemma conserve_old_bindings_move_along_path_step_inv : forall S S' s e e',
  conserve_old_bindings S S' ->
  bound S e ->
  move_along_path_step s S' e = Some e' ->
  move_along_path_step s S e = Some e'.
Proof.
  introv C B E. forwards (e_&R): bound_read B.
  unfolds move_along_path_step. rewrite R.
  rewrites >> conserve_old_bindings_read C R in E. apply~ E.
Qed.

Lemma conserve_old_bindings_move_along_path_from_inv_incl : forall (safe_pointer' : _ -> _ -> Prop) S S' p e e',
  (forall S p, safe_pointer' S p -> safe_pointer_gen safe_pointer' S p) ->
  conserve_old_bindings S S' ->
  safe_pointer' S e ->
  move_along_path_from p S' e = Some e' ->
  move_along_path_from p S e = Some e'.
Proof.
  introv Incl C OKe E. gen e e'. induction p using list_ind_last; introv OKe E.
  - rewrite move_along_path_from_nil in *. apply~ E.
  - forwards~ (e2&E1&E2): move_along_path_from_last_inv E.
    forwards~ E': IHp E1. applys~ move_along_path_from_last E'.
    applys~ conserve_old_bindings_move_along_path_step_inv E2.
    forwards~ OKe2: safe_pointer_along_path_from_incl OKe E'.
    + intro_subst. rewrite move_along_path_step_NULL in E2. inverts E2.
    + apply Incl in OKe2. applys~ pointer_bound OKe2.
Qed.

Lemma conserve_old_bindings_move_along_path_from_inv : forall S S' p e e',
  conserve_old_bindings S S' ->
  safe_pointer S e ->
  move_along_path_from p S' e = Some e' ->
  move_along_path_from p S e = Some e'.
Proof.
  introv. applys~ conserve_old_bindings_move_along_path_from_inv_incl.
  clear. introv OKp. rewrite~ <- safe_pointer_rewrite.
Qed.

Lemma conserve_old_bindings_move_along_entry_point_inv : forall S S' e p,
  conserve_old_bindings S S' ->
  move_along_entry_point e S' = Some p ->
  move_along_entry_point e S = Some p.
Proof. introv C E. rewrites~ >> conserve_old_bindings_entry_point C. Qed.

Lemma conserve_old_bindings_move_along_path_inv : forall S S' p e,
  safe_state S ->
  conserve_old_bindings S S' ->
  move_along_path p S' = Some e ->
  move_along_path p S = Some e.
Proof.
  introv OKS C E. gen e. induction p as [?|p IH s]; introv E.
  - simpls. applys~ conserve_old_bindings_move_along_entry_point_inv E.
  - simpls. destruct (move_along_path p S') eqn: E1.
    + rewrites~ >> IH. simpls.
      applys~ conserve_old_bindings_move_along_path_step_inv E.
      applys~ safe_bindings_along_path.
      intro_subst. rewrite move_along_path_step_NULL in E. inverts E.
    + inverts E.
Qed.

Lemma conserve_old_bindings_list_type_safe_aux : forall (safe_pointer1 safe_pointer2 : _ -> _ -> Prop)
    S S' l_t l_car l_tag p,
  conserve_old_bindings S S' ->
  (forall p, safe_pointer1 S p -> safe_pointer2 S' p) ->
  list_type_such_that (safe_header_gen safe_pointer1 S) (safe_pointer1 S) (safe_pointer1 S) S l_t l_car l_tag p ->
  list_type_such_that (safe_header_gen safe_pointer2 S') (safe_pointer2 S') (safe_pointer2 S') S' l_t l_car l_tag p.
Proof.
  introv C CSafe L. induction L as [? ? ? ? I|? ? ? ? p_ h car cdr tag E M H HH A L T IH]
    using list_type_ind.
  - apply list_type_nil. applys~ conserve_old_bindings_may_have_types C.
  - apply list_type_cons. exists p_. splits~.
    + applys~ conserve_old_bindings_read C.
    + exists h car cdr tag. splits~; try applys~ conserve_old_bindings_may_have_types C.
      inverts HH. constructors*. apply* conserve_old_bindings_list_type.
Qed.

Lemma conserve_old_bindings_list_head_safe_aux : forall (safe_pointer1 safe_pointer2 : _ -> _ -> Prop)
    S S' l_t l_car l_tag p_,
  conserve_old_bindings S S' ->
  (forall p, safe_pointer1 S p -> safe_pointer2 S' p) ->
  list_head_such_that (safe_header_gen safe_pointer1 S) (safe_pointer1 S) (safe_pointer1 S) S l_t l_car l_tag p_ ->
  list_head_such_that (safe_header_gen safe_pointer2 S') (safe_pointer2 S') (safe_pointer2 S') S' l_t l_car l_tag p_.
Proof.
  introv C CSafe (h&car&cdr&tag&E&T&HH&Mcar&OKcar&L&Mtag&OKtag).
  exists h car cdr tag. splits~.
  - inverts HH. constructors*. apply* conserve_old_bindings_list_type.
  - applys* conserve_old_bindings_may_have_types C.
  - applys* conserve_old_bindings_list_type_safe_aux C.
  - applys* conserve_old_bindings_may_have_types C.
Qed.

Lemma conserve_old_bindings_safe_SExpRec_type : forall S S' t p_,
  conserve_old_bindings S S' ->
  safe_SExpRec_type S t p_ ->
  safe_SExpRec_type S' t p_.
Proof.
  introv C OK. inverts OK; constructors~;
    try (introv M; match goal with P : _ |- _ =>
                     let P' := fresh P in forwards P': P M;
                     repeat (let P'' := fresh P in
                       lets (?&P''): (rm P'); rename P'' into P')
                   end; try splits);
    try applys_first (>> conserve_old_bindings_may_have_types
                         conserve_old_bindings_list_type) C; autos*.
  Optimize Proof.
Qed.

Lemma conserve_old_bindings_safe_SExpRec_aux : forall (safe_pointer1 safe_pointer2 : _ -> _ -> Prop) S S' p_,
  conserve_old_bindings S S' ->
  (forall p, safe_pointer1 S p -> safe_pointer2 S' p) ->
  safe_SExpRec_gen safe_pointer1 S p_ ->
  safe_SExpRec_gen safe_pointer2 S' p_.
Proof.
  introv C CSafe E. constructors~.
  - applys* conserve_old_bindings_safe_SExpRec_type C.
    applys~ SExpType_corresponds_to_datatype E.
  - constructors~.
    + applys~ CSafe E.
    + applys~ conserve_old_bindings_list_type C E.
Qed.

Lemma conserve_old_bindings_safe_pointer_aux : forall (safe_pointer1 safe_pointer2 : _ -> _ -> Prop) S S' p,
  conserve_old_bindings S S' ->
  (forall p, safe_pointer1 S p -> safe_pointer2 S' p) ->
  safe_pointer_gen safe_pointer1 S p ->
  safe_pointer_gen safe_pointer2 S' p.
Proof.
  introv C CSafe OKp. constructors.
  - (** pointer_bound **)
    applys conserve_old_bindings_bound C. applys~ pointer_bound OKp.
  - (** no_null_pointer_along_path_step **)
    introv NPE E. applys~ no_null_pointer_along_path_step OKp NPE.
    applys~ conserve_old_bindings_move_along_path_step_inv C OKp.
  - (** safe_pointer_along_path_step **)
    introv E D. apply CSafe. applys~ OKp. applys~ conserve_old_bindings_move_along_path_step_inv C E.
    applys~ pointer_bound OKp.
  - (** safe_SExpRec_read **)
    introv R. destruct (read_SExp S p) as [p'_|] eqn: E.
    + forwards E': conserve_old_bindings_read C E.
      rewrite E' in R. inverts~ R.
      applys~ conserve_old_bindings_safe_SExpRec_aux C.
      * introv OKp0. apply CSafe. applys~ OKp0.
      * applys~ safe_SExpRec_read OKp E.
    + false. forwards~ (?&E'): bound_read (pointer_bound OKp). rewrite E' in E. inverts E.
Qed.

Lemma conserve_old_bindings_safe_pointer : forall S S' p,
  conserve_old_bindings S S' ->
  safe_pointer S p ->
  safe_pointer S' p.
Proof.
  pcofix IH. introv C OKp. pfold. rewrite safe_pointer_rewrite in OKp.
  applys* conserve_old_bindings_safe_pointer_aux C OKp.
Qed.

Lemma conserve_old_bindings_safe_SExpRec : forall S S' p_,
  conserve_old_bindings S S' ->
  safe_SExpRec S p_ ->
  safe_SExpRec S' p_.
Proof.
  introv C OK. applys~ conserve_old_bindings_safe_SExpRec_aux C OK.
  introv. applys~ conserve_old_bindings_safe_pointer.
Qed.

Lemma conserve_old_bindings_list_type_safe : forall S S' l_t l_car l_tag p,
  conserve_old_bindings S S' ->
  list_type_safe S l_t l_car l_tag p ->
  list_type_safe S' l_t l_car l_tag p.
Proof.
  introv C L. applys~ conserve_old_bindings_list_type_safe_aux C L.
  introv. applys~ conserve_old_bindings_safe_pointer.
Qed.

Lemma conserve_old_bindings_list_head_safe : forall S S' l_t l_car l_tag p_,
  conserve_old_bindings S S' ->
  list_head_safe S l_t l_car l_tag p_ ->
  list_head_safe S' l_t l_car l_tag p_.
Proof.
  introv C L. applys~ conserve_old_bindings_list_head_safe_aux C L.
  introv. applys~ conserve_old_bindings_safe_pointer.
Qed.

Lemma alloc_SExp_safe_state : forall S S' p p_,
  safe_state S ->
  safe_SExpRec S p_ ->
  alloc_SExp S p_ = (S', p) ->
  type p_ <> NilSxp ->
  safe_state S'.
Proof.
  introv OKS OKp A D. forwards C: alloc_SExp_conserve_old_bindings A. constructors~.
  - (** no_null_pointer_entry_point **)
    introv NE E1. forwards~ E2: conserve_old_bindings_move_along_entry_point_inv C E1.
    applys~ no_null_pointer_entry_point E2.
  - (** safe_entry_points **)
    introv E1 D'. applys~ conserve_old_bindings_safe_pointer C.
    forwards~ E2: conserve_old_bindings_move_along_entry_point_inv C E1.
    applys~ safe_entry_points E2.
  - (** only_one_nil **)
    introv (p1_&E1&T1) (p2_&E2&T2). rewrites >> alloc_read_SExp_neq A in E1.
    + intro_subst. rewrites >> alloc_read_SExp_eq A in E1. inverts E1.
      false D. apply~ BagInSingle_list.
    + rewrites >> alloc_read_SExp_neq A in E2.
      * intro_subst. rewrites >> alloc_read_SExp_eq A in E2. inverts E2.
        false D. apply~ BagInSingle_list.
      * applys~ only_one_nil OKS; eexists; autos*.
  - (** safe_SymbolTable **)
    asserts E: (R_SymbolTable S' = R_SymbolTable S).
    { inverts~ A. }
    rewrite E. applys conserve_old_bindings_list_type C. applys~ safe_SymbolTable OKS.
Qed.

Lemma safe_pointer_may_have_types_all_storable_SExpTypes : forall S p,
  safe_pointer S p ->
  may_have_types S all_storable_SExpTypes p.
Proof.
  introv OKp. rewrite safe_pointer_rewrite in OKp. forwards (p_&R&_): pointer_bound OKp. exists p_. splits~.
  forwards~ OKp_: safe_SExpRec_read OKp R.
  apply SExpType_corresponds_to_datatype in OKp_. inverts OKp_; Mem_solve.
  Optimize Proof.
Qed.

Lemma list_type_safe_safe_pointer : forall S globals l_car l_tag l,
  safe_state S ->
  safe_globals S globals ->
  l_car \c all_storable_SExpTypes ->
  l_tag \c [NilSxp; CharSxp] ->
  list_type_safe S ([ListSxp]) l_car l_tag l ->
  safe_pointer S l.
Proof.
  introv OKS OKg Icar Itag L. remember ([ListSxp]) as l_t.
  induction L as [? ? ? ? L|? ? ? ? L h car cdr tag E E' T OKh Tcar OKcar L' Ttag OKtag] using list_type_ind.
  - applys~ may_have_types_NilSxp_safe_pointer OKg.
  - substs. rewrite safe_pointer_rewrite. constructors.
    + (** pointer_bound **)
      applys~ read_bound E.
    + (** no_null_pointer_along_path_step **)
      introv N Em. unfolds in Em. rewrite E in Em. simpl in Em.
      destruct s as [|?|[| |]|?|?|?|?]; inverts~ Em; applys* safe_pointer_not_NULL.
      applys~ safe_attrib OKh.
    + (** safe_pointer_along_path_step **)
      introv Em D. unfolds in Em. rewrite E in Em. simpl in Em.
      destruct s as [|?|[| |]|?|?|?|?]; inverts~ Em.
      applys~ safe_attrib OKh.
    + (** safe_SExpRec_read **)
      rewrite E. introv I. inverts I. eapply BagInSingle_list in T. constructors~.
      rewrite T. constructors~; try solve [ applys* may_have_types_weaken ].
      apply list_type_may_have_types in L'.
      applys may_have_types_weaken L'. solve_incl.
  Optimize Proof.
Qed.

Lemma conserve_old_bindings_safe_globals : forall S S' globals,
  conserve_old_bindings S S' ->
  safe_globals S globals ->
  safe_globals S' globals.
Proof.
  introv C OKglobals. constructors.
  - (** globals_not_NULL **)
    applys~ globals_not_NULL OKglobals.
  - (** globals_not_NULL_safe **)
    introv D. applys~ conserve_old_bindings_safe_pointer C. applys~ globals_not_NULL_safe D.
  - (** R_NilValue_may_have_types **)
    applys~ conserve_old_bindings_may_have_types C. applys~ R_NilValue_may_have_types.
Qed.

Lemma may_have_types_same_memory : forall S1 S2 l p,
  state_memory S1 = state_memory S2 ->
  may_have_types S1 l p ->
  may_have_types S2 l p.
Proof. introv E (p_&E'&B). exists p_. rewrite~ <- E. Qed.

Lemma list_type_same_memory : forall S1 S2 l_t l_car l_tag p,
  state_memory S1 = state_memory S2 ->
  list_type S1 l_t l_car l_tag p ->
  list_type S2 l_t l_car l_tag p.
Proof.
  introv E L. induction L using list_type_ind.
  - applys list_type_nil. applys~ may_have_types_same_memory E.
  - applys list_type_cons. rewrite E in *. eexists. splits*. do 4 eexists.
    splits*; applys~ may_have_types_same_memory E.
Qed.

Lemma safe_pointer_same_memory : forall S1 S2 p,
  state_memory S1 = state_memory S2 ->
  safe_pointer S1 p ->
  safe_pointer S2 p.
Proof.
  pcofix R. introv E OKp. pfold. rewrite safe_pointer_rewrite in OKp. constructors.
  - (** pointer_bound **)
    forwards (p_&Ep_&?): pointer_bound OKp. exists p_. rewrite~ E in Ep_.
  - (** no_null_pointer_along_path_step **)
    introv NE Ep'. applys no_null_pointer_along_path_step OKp NE.
    rewrite move_along_path_step_same_memory with (S2 := S2); autos~.
  - (** safe_pointer_along_path_step **)
    introv Ee D. rewrite <- move_along_path_step_same_memory with (S1 := S1) in Ee; autos~.
    forwards OKe: safe_pointer_along_path_step OKp Ee D.
    right. applys~ R OKe.
  - (** safe_SExpRec_read **)
    introv Ep. rewrite <- E in Ep. constructors.
    + (** SExpType_corresponds_to_datatype **)
      forwards* OKp_: SExpType_corresponds_to_datatype OKp.
      inversion OKp_; constructors~; try solve [ applys~ may_have_types_same_memory E ].
      * applys~ list_type_same_memory E.
      * introv M. applys* may_have_types_same_memory E.
      * introv M. applys* may_have_types_same_memory E.
      * introv M. applys* may_have_types_same_memory E.
    + (** SExpRec_header **)
      constructors.
      * (** safe_attrib **)
        forwards*: safe_attrib OKp.
      * (** attrib_list **)
        forwards* L: attrib_list OKp. applys~ list_type_same_memory L.
Qed.

Lemma write_SExp_move_along_path_step_inv : forall S S' p1 p2 p p_ s,
  write_SExp S p p_ = Some S' ->
  move_along_path_step s S' p1 = Some p2 ->
  p1 <> p ->
  move_along_path_step s S p1 = Some p2.
Proof.
  introv W M D. forwards (e_&R&_): move_along_path_step_bound M.
  unfolds move_along_path_step. rewrite R in M.
  rewrites~ >> read_write_SExp_neq W in R. rewrite~ R.
Qed.

Lemma safe_SExpRec_type_ListSxp_struct : forall S (p_ : SExpRec),
  type p_ \in [NilSxp ; ListSxp ; LangSxp ; DotSxp] ->
  safe_SExpRec_type S (type p_) p_ ->
  exists header car cdr tag,
    p_ = make_NonVector_SExpRec header (make_ListSxp_struct car cdr tag)
    /\ may_have_types S all_storable_SExpTypes car
    /\ may_have_types S ([NilSxp ; ListSxp ; DotSxp]) cdr
    /\ may_have_types S ([NilSxp ; CharSxp]) tag.
Proof.
  introv I OKp_. repeat inverts I as I; rewrite I in OKp_; inverts OKp_;
    simpl in I; do 4 eexists; splits; try reflexivity; autos~;
    simpl; try rewrite~ I; apply* may_have_types_weaken; solve_incl.
  Optimize Proof.
Qed.

Lemma safe_SExpRec_type_PrimSxp_struct : forall S (p_ : SExpRec),
  type p_ \in [SpecialSxp ; BuiltinSxp] ->
  safe_SExpRec_type S (type p_) p_ ->
  exists header offset,
    p_ = make_NonVector_SExpRec header (make_PrimSxp_struct offset)
    /\ safe_offset offset.
Proof. introv I OKp_. repeat inverts I as I; rewrite I in OKp_; inverts* OKp_. Qed.

Lemma safe_SExpRec_type_VectorPointer : forall S (p_ : SExpRec),
  type p_ \in [StrSxp ; VecSxp ; ExprSxp] ->
  safe_SExpRec_type S (type p_) p_ ->
  exists header array,
    p_ = SExpRec_VectorPointer (make_Vector_SExpRec header
           (make_VecSxp_struct (ArrayList.length array) (ArrayList.length array) array))
    /\ forall a,
         Mem a (ArrayList.to_list array) ->
         may_have_types S all_storable_SExpTypes a.
Proof.
  introv I OKp_. repeat inverts I as I; rewrite I in OKp_; inverts OKp_ as F;
    simpl in I; do 2 eexists; splits; try reflexivity; autos~;
    introv M; apply F in M; apply* may_have_types_weaken; solve_incl.
  Optimize Proof.
Qed.

Lemma safe_pointer_ListSxp_struct : forall S p,
  may_have_types S ([NilSxp ; ListSxp ; LangSxp ; DotSxp]) p ->
  safe_pointer S p ->
  bound_such_that S (fun p_ =>
    exists header car cdr tag,
      p_ = make_NonVector_SExpRec header (make_ListSxp_struct car cdr tag)
      /\ may_have_types S all_storable_SExpTypes car
      /\ may_have_types S ([NilSxp ; ListSxp ; DotSxp]) cdr
      /\ may_have_types S ([NilSxp ; CharSxp]) tag) p.
Proof.
  introv (p_&E&T) OKp. rewrite safe_pointer_rewrite in OKp.
  forwards~ OKp_: safe_SExpRec_read OKp E. apply SExpType_corresponds_to_datatype in OKp_.
  exists p_. splits~. applys~ safe_SExpRec_type_ListSxp_struct T OKp_.
Qed.

Lemma safe_pointer_PrimSxp_struct : forall S p,
  may_have_types S ([SpecialSxp ; BuiltinSxp]) p ->
  safe_pointer S p ->
  bound_such_that S (fun p_ =>
    exists header offset,
      p_ = make_NonVector_SExpRec header (make_PrimSxp_struct offset)
      /\ safe_offset offset) p.
Proof.
  introv (p_&E&T) OKp. rewrite safe_pointer_rewrite in OKp.
  forwards~ OKp_: safe_SExpRec_read OKp E. apply SExpType_corresponds_to_datatype in OKp_.
  exists p_. splits~. applys~ safe_SExpRec_type_PrimSxp_struct T OKp_.
Qed.

Lemma safe_pointer_VectorPointer : forall S p,
  may_have_types S ([StrSxp ; VecSxp ; ExprSxp]) p ->
  safe_pointer S p ->
  bound_such_that S (fun p_ =>
    exists header array,
      p_ = SExpRec_VectorPointer (make_Vector_SExpRec header
             (make_VecSxp_struct (ArrayList.length array) (ArrayList.length array) array))
      /\ forall a,
           Mem a (ArrayList.to_list array) ->
           may_have_types S all_storable_SExpTypes a) p.
Proof.
  introv (p_&E&T) OKp. rewrite safe_pointer_rewrite in OKp.
  forwards~ OKp_: safe_SExpRec_read OKp E. apply SExpType_corresponds_to_datatype in OKp_.
  exists p_. splits~. applys~ safe_SExpRec_type_VectorPointer T OKp_.
Qed.

Lemma make_SExpRec_char_safe : forall S attrib array,
  safe_pointer S attrib ->
  list_type S ([ListSxp]) all_storable_SExpTypes ([CharSxp]) attrib ->
  safe_SExpRec S (make_SExpRec_char attrib array).
Proof. introv OKattrib Lattrib. constructors; constructors~. Qed.

Lemma make_SExpRec_lgl_safe : forall S attrib array,
  safe_pointer S attrib ->
  list_type S ([ListSxp]) all_storable_SExpTypes ([CharSxp]) attrib ->
  safe_SExpRec S (make_SExpRec_lgl attrib array).
Proof. introv OKattrib Lattrib. constructors; constructors~. Qed.

Lemma make_SExpRec_int_safe : forall S attrib array,
  safe_pointer S attrib ->
  list_type S ([ListSxp]) all_storable_SExpTypes ([CharSxp]) attrib ->
  safe_SExpRec S (make_SExpRec_int attrib array).
Proof. introv OKattrib Lattrib. constructors; constructors~. Qed.

Lemma make_SExpRec_real_safe : forall S attrib array,
  safe_pointer S attrib ->
  list_type S ([ListSxp]) all_storable_SExpTypes ([CharSxp]) attrib ->
  safe_SExpRec S (make_SExpRec_real attrib array).
Proof. introv OKattrib Lattrib. constructors; constructors~. Qed.

Lemma make_SExpRec_cplx_safe : forall S attrib array,
  safe_pointer S attrib ->
  list_type S ([ListSxp]) all_storable_SExpTypes ([CharSxp]) attrib ->
  safe_SExpRec S (make_SExpRec_cplx attrib array).
Proof. introv OKattrib Lattrib. constructors; constructors~. Qed.

Optimize Heap.
