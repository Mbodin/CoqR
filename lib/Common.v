(** General lemmae.
  This file contains all the constructs that I consider should be in my libraries by are not.
  It can be seen as a personnal library.
  Note that as TLC is changing, some of these lemmae already have been added to it:
  this file may need some cleanup to update to fresher versions of TLC. **)

From Lib Require Import LibExec.
Require Export Heap.
From TLC Require Import LibStream LibString LibNat LibInt.
From TLC Require Export LibTactics LibReflect LibLogic LibList LibBool.

Notation " [ ] " := nil : list_scope.
Notation " [ x ] " := (cons x nil) : list_scope.
Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..) : list_scope.

Open Scope Int_scope.

Set Implicit Arguments.


(** * Useful tactics **)

(** ** Apply a list of hypotheses **)

Ltac apply_first_base L :=
  let L := list_boxer_of L in
  lazymatch L with
  | boxer ?P :: ?L' =>
    apply~ P || apply_first_base L'
  end.

Tactic Notation "apply_first" constr(E) :=
  apply_first_base E.
Tactic Notation "apply_first" constr(E0) constr(A1) :=
  apply_first (>> E0 A1).
Tactic Notation "apply_first" constr(E0) constr(A1) constr(A2) :=
  apply_first (>> E0 A1 A2).
Tactic Notation "apply_first" constr(E0) constr(A1) constr(A2) constr(A3) :=
  apply_first (>> E0 A1 A2 A3).
Tactic Notation "apply_first" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) :=
  apply_first (>> E0 A1 A2 A3 A4).
Tactic Notation "apply_first" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  apply_first (>> E0 A1 A2 A3 A4 A5).


Ltac applys_first L A :=
  let L := list_boxer_of L in
  let A := list_boxer_of A in
  lazymatch L with
  | boxer ?P :: ?L' =>
    applys_base (boxer P :: A) || applys_first L' A
  end.


(** ** Rewrite a list of equalities **)

Ltac rewrite_first L :=
  let L := list_boxer_of L in
  lazymatch L with
  | boxer ?P :: ?L' =>
    rewrite~ P || rewrite_first L'
  end.


(** ** Fresh identifiers **)

(** The original [fresh] tactic doesn’t work if given hints that are
  function applications. These tactics accept any hint.
  Unfortunately, they don’t convert Coq strings into identifiers. **)

Ltac fresh1 N :=
  match goal with
  | |- _ => let r := fresh N in r
  | |- _ => let r := fresh in r
  end.

Ltac fresh2 N1 N2 :=
  match goal with
  | |- _ => let r := fresh N1 N2 in r
  | |- _ => let r := fresh N1 in r
  | |- _ => let r := fresh N2 in r
  | |- _ => let r := fresh in r
  end.

Ltac fresh3 N1 N2 N3 :=
  match goal with
  | |- _ => let r := fresh N1 N2 N3 in r
  | |- _ => let r := fresh N1 N2 in r
  | |- _ => let r := fresh N1 N3 in r
  | |- _ => let r := fresh N2 N3 in r
  | |- _ => let r := fresh N1 in r
  | |- _ => let r := fresh N2 in r
  | |- _ => let r := fresh N3 in r
  | |- _ => let r := fresh in r
  end.


(** * May be added in TLC **)

Global Instance Forall_mem_Decidable : forall A (P : A -> Prop) l,
  (forall a, mem a l -> Decidable (P a)) ->
  Decidable (Forall P l).
Proof.
  induction l; introv F.
  - applys decidable_make true. rew_bool_eq. apply~ Forall_nil.
  - rewrite Forall_cons_eq. apply* and_decidable.
Defined.

Global Instance Forall_Decidable : forall A (P : A -> Prop) l,
  (forall a, Decidable (P a)) ->
  Decidable (Forall P l).
Proof.
  introv F. applys~ Forall_mem_Decidable.
Defined.

Lemma Forall2_inv : forall A1 A2 P (l1 : list A1) r' x1,
  Forall2 P (x1::l1) r' ->
  exists (r2:list A2) x2,
  r' = x2::r2 /\ P x1 x2 /\ Forall2 P l1 r2.
Proof using. introv H. inverts* H. Qed.

Lemma Forall2_iff_forall_Nth : forall A1 A2 (P : A1 -> A2 -> Prop) (l1 : list A1) (l2 : list A2),
  Forall2 P l1 l2 <->
  length l1 = length l2 /\ (forall n v1 v2, Nth n l1 v1 -> Nth n l2 v2 -> P v1 v2).
Proof using.
  introv. gen l2.
  induction l1 as [|x1 l1]; intros [|x2 l2]; (iff I; [ splits | inverts I as I1 I2 ]);
    try solve [ inverts~ I ]; tryfalse~.
  - introv N1. inverts N1.
  - constructors.
  - do 2 rewrite length_cons. inverts I as I1 I2. rewrite* IHl1 in I2.
  - introv N1 N2. inverts I as I1 I2. rewrite IHl1 in I2. inverts N1; inverts~ N2.
    apply* (proj2 I2).
  - constructors.
    apply~ I2; constructors.
    rewrite IHl1. splits~. introv N1 N2. apply~ I2; constructors*.
Qed.

Lemma Forall2_compose : forall A1 A2 A3 (P Q R : _ -> _ -> Prop)
    (l1 : list A1) (l2 : list A2) (l3 : list A3),
  Forall2 P l1 l2 ->
  Forall2 Q l2 l3 ->
  (forall x y z, P x y -> Q y z -> R x z) ->
  Forall2 R l1 l3.
Proof using.
  introv F12 F23 I. rewrite Forall2_iff_forall_Nth in *. splits.
  - transitivity (length l2); autos*.
  - introv N1 N2. asserts (v&N): (exists v, Nth n l2 v); [| autos* ].
    apply Nth_inbound_inv. rewrite (proj1 F23). apply* Nth_inbound.
Qed.

Lemma Forall2_Forall : forall A1 A2 (P : _ -> Prop) (Q : _ -> _ -> Prop)
    (l1 : list A1) (l2 : list A2),
  Forall P l1 ->
  Forall2 Q l1 l2 ->
  Forall2 (fun a b => P a /\ Q a b) l1 l2.
Proof. introv F F2. gen l2. induction F; introv F2; inverts F2; constructors~. Qed.

Local Transparent combine.

Lemma Forall2_combine : forall A1 A2 A3 (P Q : _ -> _ -> Prop)
    (l1 : list A1) (l2 : list A2) (l3 : list A3),
  Forall2 P l1 l2 ->
  Forall2 Q l1 l3 ->
  Forall2 (fun a bc => P a (fst bc) /\ Q a (snd bc)) l1 (combine l2 l3).
Proof. introv F1 F2. gen l3. induction F1; introv F2; inverts F2; constructors~. Qed.

Instance Forall2_Decidable_mem : forall A B (P : A -> B -> Prop) l1 l2,
  (forall a b, mem a l1 -> mem b l2 -> Decidable (P a b)) ->
  Decidable (Forall2 P l1 l2).
Proof.
  introv F. gen l2. induction l1 as [|a l1]; introv F.
  - destruct l2.
    + applys Decidable_equiv True.
      * iff~ I. constructors.
      * typeclass.
    + applys Decidable_equiv False.
      * iff I; tryfalse. inverts~ I.
      * typeclass.
  - destruct l2 as [|b l2].
    + applys Decidable_equiv False.
      * iff I; tryfalse. inverts~ I.
      * typeclass.
    + applys Decidable_equiv (P a b /\ Forall2 P l1 l2).
      * iff I.
        -- constructors*.
        -- inverts* I.
      * apply and_decidable.
        -- apply* F.
        -- apply IHl1. introv M1 M2. apply* F.
Defined.

Global Instance Forall2_Decidable : forall A B (P : A -> B -> Prop) l1 l2,
  (forall a b, Decidable (P a b)) ->
  Decidable (Forall2 P l1 l2).
Proof.
  introv F. apply~ Forall2_Decidable_mem.
Defined.

Lemma Forall2_eq : forall A (l : list A),
  Forall2 eq l l.
Proof. induction l; constructors~. Qed.

Lemma Nth_equiv : forall A (l1 l2 : list A),
  (forall n x, Nth n l1 x <-> Nth n l2 x) ->
  l1 = l2.
Proof.
  induction l1 as [|a1 l1]; introv E; destruct~ l2 as [|a2 l2].
  - forwards N: Nth_zero l2 a2. apply E in N. inverts~ N.
  - forwards N: Nth_zero l1 a1. apply E in N. inverts~ N.
  - fequals.
    + forwards N: Nth_zero l1 a1. apply E in N. inverts~ N.
    + apply~ IHl1. introv. iff I.
      * forwards N: Nth_succ a1 I. apply E in N. inverts~ N.
      * forwards N: Nth_succ a2 I. apply E in N. inverts~ N.
Qed.

Global Instance Comparable_list : forall A,
  Comparable A ->
  Comparable (list A).
Proof.
  introv C. constructors. intros l1 l2.
  applys Decidable_equiv (Forall2 eq l1 l2); [| typeclass ]. splits.
  - introv F. apply Nth_equiv. introv. forwards L: Forall2_inv_length F.
    splits; introv N;
      forwards I: Nth_inbound N; [ rewrite L in I | rewrite <- L in I ];
      forwards (?&N'): Nth_inbound_inv I.
    + forwards: Forall2_Nth_inv F N N'. substs~.
    + forwards: Forall2_Nth_inv F N' N. substs~.
  - intro_subst. apply~ Forall2_eq.
Defined.

Lemma mem_last_inv : forall A l (x e : A),
  mem x (l & e) ->
  x = e \/ mem x l.
Proof. introv. rewrite* mem_last_eq. Qed.

Lemma mem_in_last : forall A l (x e : A),
  mem x l ->
  mem x (l & e).
Proof. introv M. apply* mem_last. Qed.

Lemma Nth_add_last : forall A l (x e : A) n,
  Nth n l x ->
  Nth n (l & e) x.
Proof. introv N. induction N; rew_list; constructors~. Qed.

Lemma Nth_last : forall A l (x : A),
  Nth (length l) (l & x) x.
Proof. introv. induction l; rew_list; constructors~. Qed.

Lemma map_List_map : map = List.map.
Proof. extens. intros A B f l. induction~ l. simpl. rewrite map_cons. fequals~. Qed.

Lemma mem_map_inv : forall A B (f : A -> B) l y,
  mem y (map f l) ->
  exists x,
    mem x l /\ y = f x.
Proof.
  induction l; introv M.
  - inverts M.
  - rewrite map_cons in M. inverts M as M.
    + exists* a.
    + forwards* (x&Mx&Ex): (rm IHl) M.
Qed.

Lemma map_nth : forall A B `{Inhab A} `{Inhab B} (f : A -> B) l n,
  n < length l ->
  nth n (map f l) = f (nth n l).
Proof.
  introv I. gen l. induction n; introv I; destruct l; try solve [false; rew_list in I; nat_math]; rewrite map_cons.
  - do 2 rewrite nth_zero. reflexivity.
  - do 2 rewrite nth_succ. apply~ IHn. rew_list in I. nat_math.
Qed.

Lemma map_Nth : forall A B (f : A -> B) l n x,
  Nth n l x ->
  Nth n (map f l) (f x).
Proof.
  introv N. induction N.
  - apply~ Nth_zero.
  - rewrite map_cons. apply~ Nth_succ.
Qed.

Lemma remove_correct : forall A `{Comparable A} l (a1 a2 : A),
  mem a1 (remove a2 l) <-> mem a1 l /\ a1 <> a2.
Proof. intros A C l a1 a2. rewrite* mem_remove_eq. Qed.


Lemma head_tail : forall A l (a : A),
  List.hd_error l = Some a ->
  a :: List.tl l = l.
Proof. introv E. destruct l; inverts~ E. Qed.

Lemma head_Nth : forall A l (a : A),
  List.hd_error l = Some a <-> Nth 0 l a.
Proof.
  introv. destruct l.
  - iff I; inverts~ I.
  - iff I; inverts~ I.
Qed.

Lemma cut_list_cons : forall A l (a : A),
  l <> nil ->
  Nth 0 l a ->
  exists l', l = a :: l'.
Proof. introv D N. destruct l; inverts* N. Qed.

Lemma Nth_rev : forall A l n (a : A),
  n < length l ->
  Nth n l a <-> Nth (length l - 1 - n) (rev l) a.
Proof.
  introv In. gen n. induction l; introv; rew_list; iff I.
  - inverts I.
  - inverts I.
  - simpl. inverts I as I.
    + asserts_rewrite (length l - 0 - 0 = 0 + length (rev l)); [rew_list; math|].
      apply* Nth_app_r.
    + eapply Nth_app_l. apply IHl in I.
      asserts_rewrite (length l - 0 - S n0 = length l - 1 - n0); [math|].
      apply~ I. math.
  - simpl in I. forwards [N|(m&E&N)]: Nth_app_inv I.
    + destruct n.
      * apply Nth_inbound in N. rew_list in N. false. math.
      * asserts_rewrite (length l - 0 - S n = length l - 1 - n) in N; [math|].
        apply IHl in N; [ apply~ Nth_succ | math ].
    + repeat inverts N as N. rew_list in E.
      asserts: (n = 0); [ math |]. substs. constructors~.
Qed.

Lemma cut_list_last : forall A l (a : A),
  l <> nil ->
  Nth (length l - 1) l a ->
  exists l', l = l' & a.
Proof.
  introv D N. exists (rev (List.tl (rev l))). apply rev_inj. rew_list.
  rewrite~ head_tail. apply~ head_Nth. apply~ Nth_rev.
  + destruct l; tryfalse. rew_list. math.
  + rew_list.
    asserts_rewrite (length l - 1 - 0 = length l - 1); [ math | apply~ N ].
Qed.

Lemma length_datatype_length : forall A (l : list A),
  length l = Datatypes.length l.
Proof. introv. induction~ l. simpl. rewrite~ length_cons. Qed.

Lemma nat_seq_shift : forall start len,
  nat_seq (S start) len = map S (nat_seq start len).
Proof.
  introv. gen start. induction len; introv.
  - repeat rewrite~ nat_seq_zero.
  - repeat rewrite nat_seq_succ. rewrite map_cons. fequals~.
Qed.

Lemma nat_seq_Nth : forall len start n,
  n < len ->
  Nth n (nat_seq start len) (start + n).
Proof.
  introv I. gen start n. induction len; introv I.
  - false. math.
  - rewrite nat_seq_succ. destruct n.
    + simpl. asserts_rewrite (start + 0 = start); [ math | constructors~ ].
    + apply Nth_succ. rewrite nat_seq_shift.
      asserts_rewrite (start + S n = S (start + n)); [math|].
      apply map_Nth. apply IHlen. math.
Qed.

Lemma nat_seq_last : forall start len,
  nat_seq start (S len) = nat_seq start len & (start + len).
Proof.
  introv. apply Nth_equiv. introv. iff I.
  - forwards N: nat_seq_Nth (S len) start n.
    + forwards I': Nth_inbound I. rewrite length_nat_seq in I'. math.
    + forwards: Nth_functional I N. substs.
      tests: (n = len).
      * asserts E: (len = 0 + length (nat_seq start len)).
        { rewrite length_nat_seq. math. }
        rewrite E at 1.
        apply* Nth_app_r.
      * applys Nth_app_l. apply~ nat_seq_Nth.
        apply Nth_inbound in I. rewrite length_nat_seq in I. math.
  - forwards [N|(m&E&N)]: Nth_app_inv (rm I).
    + forwards N': nat_seq_Nth len start n.
      * forwards I: Nth_inbound N. rewrite length_nat_seq in I. math.
      * forwards: Nth_functional N N'. substs.
        apply~ nat_seq_Nth. apply Nth_inbound in N. rewrite length_nat_seq in N. math.
    + repeat inverts N as N. rewrite length_nat_seq in E.
      asserts_rewrite (n = len); [math|]. apply~ nat_seq_Nth.
Qed.

Lemma nat_seq_0 : forall start,
  nat_seq start 0 = nil.
Proof. reflexivity. Qed.

Lemma nat_seq_1 : forall start,
  nat_seq start 1 = cons start nil.
Proof. reflexivity. Qed.

Lemma nat_seq_split : forall start len k,
  k <= len ->
  nat_seq start len = nat_seq start k ++ nat_seq (start + k) (len - k).
Proof.
  introv I. apply Nth_equiv. introv. tests I': (n < k); iff N.
  - apply Nth_app_l. forwards N': nat_seq_Nth len start n.
    { forwards~ L: Nth_inbound N. rewrite length_nat_seq in L. math. }
    forwards: Nth_functional N N'. substs.
    applys~ nat_seq_Nth.
  - forwards [N'|(m&E&N')]: Nth_app_inv (rm N).
    + forwards N: nat_seq_Nth k start n.
      { forwards~ L: Nth_inbound N'. }
      forwards: Nth_functional N N'. substs.
      applys~ nat_seq_Nth. math.
    + forwards N: nat_seq_Nth (len - k) (start + k) m.
      { forwards~ L: Nth_inbound N'. rewrite length_nat_seq in L. math. }
      forwards E': Nth_functional N N'. rewrite <- E'. rewrite <- Nat.add_assoc.
      rewrite length_nat_seq in *. rewrite E. applys~ nat_seq_Nth. math.
  - asserts_rewrite (n = (n - k) + length (nat_seq start k)); [rewrite length_nat_seq; math|].
    apply Nth_app_r.
    forwards N': nat_seq_Nth len start n.
    { forwards N': Nth_inbound N. rewrite length_nat_seq in N'. math. }
    forwards: Nth_functional N N'. substs.
    asserts_rewrite (start + n = (start + k) + (n - k)); [math|].
    applys~ nat_seq_Nth. apply Nth_inbound in N. rewrite length_nat_seq in N. math.
  - forwards [N'|(m&E&N')]: Nth_app_inv (rm N).
    + forwards N: nat_seq_Nth k start n.
      { forwards L: Nth_inbound N'. rewrite length_nat_seq in L. math. }
      forwards: Nth_functional N N'; substs.
      applys~ nat_seq_Nth. apply Nth_inbound in N. rewrite length_nat_seq in N. math.
    + forwards N: nat_seq_Nth (len - k) (start + k) m.
      { forwards L: Nth_inbound N'. rewrite length_nat_seq in L. math. }
      forwards: Nth_functional N N'; substs.
      rewrite length_nat_seq in *. rewrite <- Nat.add_assoc.
      applys~ nat_seq_Nth. apply Nth_inbound in N. rewrite length_nat_seq in N. math.
Qed.

Lemma In_mem : forall A l (a : A),
  mem a l <-> List.In a l.
Proof.
  introv. iff I.
  - induction I; [left~|right~].
  - induction l; inverts I as I; constructors~.
Qed.

Lemma noduplicates_NoDup : forall A (l : list A),
  noduplicates l <-> List.NoDup l.
Proof. introv. iff D; induction D; constructors~; introv I; apply In_mem in I; autos~. Qed.

Global Instance mem_Decidable : forall A `{Comparable A} (a : A) l,
    Decidable (mem a l).
  intros A C a l. induction l as [|b l].
  - applys decidable_make false. rew_istrue. introv N. inverts~ N.
  - rewrite mem_cons_eq. typeclass.
Defined.

Global Instance noduplicates_decidable : forall A (l : list A),
    Comparable A ->
    Decidable (noduplicates l).
  introv C. induction l.
   applys Decidable_equiv True.
    splits; constructors~.
    typeclass.
   applys Decidable_equiv (~ mem a l /\ noduplicates l).
    splits.
     introv (NM&ND). constructors~.
     introv ND. inverts~ ND.
    typeclass.
Defined.

Definition find_index_def A n (a : A) l :=
  fold_right (fun e n => If a = e then 0 else n + 1) n l.

Definition find_index A :=
  nosimpl (@find_index_def A 0).

Lemma find_index_def_length : forall A (a : A) l n,
  ~ mem a l ->
  find_index_def n a l = n + length l.
Proof.
  introv N. unfold find_index_def. gen n. induction l using list_ind_last; introv.
   simpl. rewrite~ length_nil.
   rewrite fold_right_last. rewrite IHl.
    case_if.
     false N. apply* mem_last.
     rewrite length_last. rewrite~ PeanoNat.Nat.add_assoc.
    introv M. false N. apply* mem_in_last.
Qed.

Lemma find_index_nth : forall A (a : A) l,
  mem a l ->
  Nth (find_index a l) l a.
Proof.
  introv M. unfold find_index. generalize 0. induction l using list_ind_last; introv.
   inverts* M.
   unfolds find_index_def. rewrite fold_right_last. apply mem_last_inv in M.
    tests M': (mem a l).
     apply* Nth_add_last.
     case_if.
      fold (find_index_def 0 a l). rewrite~ find_index_def_length. subst. apply* Nth_last.
      inverts* M.
Qed.

Fixpoint nth_option A n (l : list A) {struct l} :=
  match l with
  | nil => None
  | x :: l =>
    match n with
    | 0 => Some x
    | S n => nth_option n l
    end
  end.

Lemma nth_option_length : forall A n (l : list A),
  nth_option n l = None <-> length l <= n.
Proof.
  introv. gen n. induction l; iff I.
   rew_list. math.
   reflexivity.
   rew_list. simpl in I. destruct n; inverts I as I'. rewrite IHl in I'. math.
   rew_list in I. destruct n.
    false. math.
    simpl. rewrite IHl. math.
Qed.

Lemma nth_option_defined : forall A (H : Inhab A) n (l : list A) x,
  nth_option n l = Some x ->
  nth n l = x.
Proof.
  introv E. gen n. induction l; introv E.
   inverts E.
   destruct n.
    inverts E. reflexivity.
    simpl in E. rewrite nth_succ. apply~ IHl.
Qed.

Lemma nth_option_Some : forall A (H : Inhab A) n (l : list A),
  n < length l ->
  nth_option n l = Some (nth n l).
Proof.
  introv I. destruct nth_option eqn: E.
   eapply nth_option_defined in E. rewrite~ <- E.
   apply nth_option_length in E. false. math.
Qed.

Lemma nth_option_update_eq : forall A l i (v : A),
  i < length l ->
  nth_option i (update i v l) = Some v.
Proof.
  introv I. gen i. induction l; introv I; rew_list in I.
   false. math.
   simpl. destruct i as [|i'].
    reflexivity.
    apply~ IHl. math.
Qed.

Lemma nth_option_update_neq : forall A l i j (v : A),
  i < length l ->
  i <> j ->
  nth_option j (update i v l) = nth_option j l.
Proof.
  introv I D. gen i j. induction l; introv I D; rew_list in I.
   false. math.
   simpl. destruct i as [|i'], j as [|j']; try reflexivity; tryfalse.
    simpl. apply~ IHl. math.
Qed.

Lemma nth_option_zero : forall A l (a : A),
  nth_option 0 (a :: l) = Some a.
Proof. reflexivity. Qed.

Lemma nth_option_cons : forall A l n (a : A),
  nth_option (S n) (a :: l) = nth_option n l.
Proof. reflexivity. Qed.

Lemma Nth_nth_option : forall A (l : list A) n a,
  Nth n l a <-> nth_option n l = Some a.
Proof.
  induction l; (split; [ introv N; inverts~ N | introv E; tryfalse ]); simpls.
  - apply~ IHl.
  - destruct n.
    + inverts~ E.
    + constructors. apply~ IHl.
Qed.

Lemma update_out : forall A l i (v : A),
  i >= length l ->
  update i v l = l.
Proof.
  induction l; introv I; rew_list in I.
   reflexivity.
   simpl. destruct i as [|i'].
    false. math.
    rewrite update_cons. fequals. apply~ IHl. math.
Qed.


Lemma stream_head_nth : forall A (s : stream A),
  stream_head s = LibStream.nth 0 s.
Proof. introv. destruct* s. Qed.

Lemma stream_tail_nth : forall A (s : stream A) n,
  LibStream.nth n (stream_tail s) = LibStream.nth (1 + n) s.
Proof. introv. destruct* s. Qed.



Definition list_to_string l :=
  fold_left (fun c str => String c str) EmptyString (rev l).

Fixpoint string_to_list (str : string) :=
  match str with
  | EmptyString => nil
  | String c str =>
    c :: string_to_list str
  end.

Definition ascii_to_string c := list_to_string (cons c nil).

Global Coercion ascii_to_string : Ascii.ascii >-> string.

Fixpoint divide_list {A} (l : list A) :=
  match l with
  | nil => (nil, nil)
  | x :: nil => (x :: nil, nil)
  | x :: y :: l =>
    let (l1, l2) := divide_list l in
    (x :: l1, y :: l2)
  end.

Lemma divide_list_cons : forall A (l l1 l2: list A) x,
  divide_list l = (l1, l2) ->
  divide_list (x :: l) = (x :: l2, l1).
Proof.
  introv E. gen l1 l2. induction l; introv E.
  - inverts~ E.
  - simpls. destruct (divide_list l) as [la lb]. forwards~ E': (rm IHl).
    destruct l as [|e l]; simpls.
    + inverts E. inverts~ E'.
    + destruct divide_list. inverts E. inverts~ E'.
Qed.

Lemma divide_list_mem : forall A l (x : A) l1 l2,
  mem x l ->
  divide_list l = (l1, l2) ->
  mem x l1 \/ mem x l2.
Proof.
  introv M E. gen l1 l2. induction M; introv E.
  - destruct l; inverts E as E; autos~. destruct divide_list. inverts~ E.
  - destruct (divide_list l) as [la lb] eqn: El. erewrite divide_list_cons in E; autos*.
    inverts E. forwards*: (rm IHM).
Qed.

Lemma divide_list_mem_inv : forall A l (x : A) l1 l2,
  mem x l1 \/ mem x l2 ->
  divide_list l = (l1, l2) ->
  mem x l.
Proof.
  induction l; introv O E.
  - inverts E. inverts* O.
  - destruct (divide_list l) as [la lb] eqn: El. erewrite divide_list_cons in E; autos*.
    inverts E. inverts O as O.
    + inverts O as O.
      * constructors*.
      * constructors. eapply IHl; [| reflexivity ]. right~.
    + constructors*.
Qed.

Lemma divide_list_noduplicates : forall A (l l1 l2 : list A),
  noduplicates l ->
  divide_list l = (l1, l2) ->
  noduplicates l1 /\ noduplicates l2.
Proof.
  introv ND E. gen l1 l2. induction l; introv E.
  - inverts~ E.
  - destruct (divide_list l) as [la lb] eqn: El. erewrite divide_list_cons in E; autos*.
    inverts E. forwards~ (ND1&ND2): (rm IHl).
    + inverts~ ND.
    + splits~. constructors~. introv M. forwards M': divide_list_mem_inv El.
      * right*.
      * inverts* ND.
Qed.

Lemma divide_list_mem_noduplicates : forall A l (x : A) l1 l2,
  mem x l ->
  noduplicates l ->
  divide_list l = (l1, l2) ->
  mem x l1 ->
  mem x l2 ->
  False.
Proof.
  introv M ND E. gen l1 l2. induction l; introv E M1 M2.
  - inverts E. invert M1.
  - destruct (divide_list l) as [la lb] eqn: El. erewrite divide_list_cons in E; autos*.
    inverts E. inverts M1 as M1.
    + forwards: divide_list_mem_inv El.
      * left*.
      * inverts* ND.
    + applys~ IHl.
      * applys~ divide_list_mem_inv El.
      * inverts~ ND.
Qed.


Lemma Z_to_nat_sub : forall a b : nat,
  a >= b ->
  Z.to_nat (a - b) = (a - b)%nat.
Proof.
  introv I. gen a. induction b; introv I.
  - math.
  - destruct a.
    + false. math.
    + simpl. rewrite <- IHb; try fequals; math.
Qed.


Instance nat_lt_Decidable : forall n1 n2 : nat,
  Decidable (n1 < n2)%nat.
Proof.
  intros. applys Decidable_equiv.
  - symmetry. apply nat_compare_lt.
  - typeclass.
Defined.

Instance positive_lt_Decidable : forall n1 n2,
  Decidable (n1 < n2)%positive.
Proof.
  typeclass.
Defined.

Instance Z_lt_Decidable : forall n1 n2,
  Decidable (n1 < n2)%Z.
Proof.
  intros. applys Decidable_equiv Z.compare_lt_iff. typeclass.
Defined.

Instance lt_Decidable : forall n1 n2,
  Decidable (n1 < n2).
Proof.
  intros. applys Decidable_equiv (n1 < n2)%Z.
  - math.
  - typeclass.
Defined.

(*
Instance lt_nat_Decidable : forall n1 n2,
  Decidable (@lt nat (@lt_from_le nat le_nat_inst) n1 n2).
Proof.
  intros. applys Decidable_equiv (lt_Decidable n1 n2). math.
Defined.
*)

Instance nat_gt_Decidable : forall n1 n2 : nat,
  Decidable (n1 > n2)%nat.
Proof.
  intros. applys Decidable_equiv.
  - symmetry. apply nat_compare_lt.
  - typeclass.
Defined.

Instance positive_gt_Decidable : forall n1 n2,
  Decidable (n1 > n2)%positive.
Proof.
  typeclass.
Defined.

Instance Z_gt_Decidable : forall n1 n2,
  Decidable (n1 > n2)%Z.
Proof.
  intros. applys sumbool_decidable Z_gt_dec.
Defined.

Instance gt_Decidable : forall n1 n2,
  Decidable (n1 > n2).
Proof.
  intros. applys Decidable_equiv (n1 > n2)%Z.
  - math.
  - typeclass.
Defined.

(*
Instance gt_nat_Decidable : forall n1 n2,
  Decidable (@gt nat (@gt_from_le nat le_nat_inst) n1 n2).
Proof.
  intros. applys Decidable_equiv (gt_Decidable n1 n2). math.
Defined.
*)

(*
Instance ge_nat_Decidable : forall n1 n2 : nat,
  Decidable (@ge nat (@ge_from_le nat le_nat_inst) n1 n2).
Proof.
  intros. applys Decidable_equiv (n1 >= n2)%Z.
  - math.
  - typeclass.
Defined.
*)

Instance positive_ge_Decidable : forall n1 n2,
  Decidable (n1 >= n2)%positive.
Proof.
  typeclass.
Defined.

(*
Instance ge_Decidable : forall n1 n2 : int%I,
  Decidable (n1 >= n2).
Proof.
  intros. applys Decidable_equiv (n1 >= n2)%Z.
  - math.
  - typeclass.
Defined.
*)

Instance le_nat_Decidable : forall n1 n2 : nat,
  Decidable (@le nat le_nat_inst n1 n2).
Proof.
  intros. applys Decidable_equiv (n1 <= n2)%Z.
  - math.
  - typeclass.
Defined.

Instance positive_le_Decidable : forall n1 n2,
  Decidable (n1 <= n2)%positive.
Proof.
  typeclass.
Defined.

Instance le_Decidable : forall n1 n2,
  Decidable (n1 <= n2).
Proof.
  intros. applys Decidable_equiv (n1 <= n2)%Z.
  - math.
  - typeclass.
Defined.


Instance positive_Comparable : Comparable positive.
Proof.
  apply make_comparable. intros.
  applys Decidable_equiv (let (x, y) := (Pos.to_nat x, Pos.to_nat y) in x >= y /\ x <= y).
  - transitivity (Pos.to_nat x = Pos.to_nat y).
    + nat_math.
    + apply Pos2Nat.inj_iff.
  - typeclass.
Defined.

Instance Ascii_comparable : Comparable Ascii.ascii.
Proof.
  apply make_comparable. intros. applys sumbool_decidable Ascii.ascii_dec.
Defined.


(** * Tactics about Comparable **)

Instance Comparable_Decidable : forall A (a1 a2 : A),
    Comparable A ->
    Decidable (a1 = a2).
Proof.
  introv C. inverts* C.
Defined.

(** Builds an instance of [Comparable] from a non-recursive inductive. **)
Ltac prove_decidable_eq :=
  let prove_injection Eq :=
    solve [ injection Eq; intros; substs~
          | intros; substs~; reflexivity ] in
  let rec t tr :=
    match goal with
    (** Trivial cases **)
    | _ =>
      applys decidable_make false; abstract (rew_bool_eq; discriminate)
    | _ =>
      applys decidable_make true; abstract (rew_bool_eq; reflexivity)
    (** Look for already defined typeclasses **)
    | _ =>
      typeclass || (apply Comparable_Decidable; typeclass)
    (** A little trivial case **)
    | _ =>
      lazymatch goal with
      |- Decidable (?f1 = ?f2) =>
        abstract (
          let D := fresh "D" in asserts D: (tr f1 <> tr f2);
          [ discriminate
          | applys decidable_make false; rew_bool_eq;
            let AE := fresh "AE" in intro AE; rewrite AE in *; false* ])
      end
    (** General case **)
    | |- Decidable (?f1 ?x1 = ?f2 ?x2) =>
      let tf := type of f1 in
      let Decf := fresh "Dec_f" in let Decx := fresh "Dec_x" in
      let tr' := constr:(fun f : tf => tr (f x1)) in
      asserts Decx: (Decidable (x1 = x2));
      [ let T := type of x1 in try (typeclass || solve [ t (@id T) ])
      | asserts Decf: (Decidable (f1 = f2));
        [ t tr'
        | applys decidable_make (decide (f1 = f2 /\ x1 = x2));
          abstract (
            let I := fresh "I" in
            let I1 := fresh "I_f" in let I2 := fresh "I_x" in
            rewrite decide_spec; rew_bool_eq; iff I;
            [ lets (I1&I2): (rm I); try rewrite I1; try rewrite I2; reflexivity
            | inverts I as I; splits~;
              let Eq := fresh "Eq" in
              asserts Eq: (tr (f1 x1) = tr (f2 x2));
              [ rewrite~ I | prove_injection Eq ]
            ]) ] ]
    | _ =>
      (** Nothing intelligent to do, let us nevertheless simplify the
         task of the user to know what is the context. **)
      let TR := fresh "tr" in set (TR := tr)
    end in
  lazymatch goal with
  | |- Decidable (?x = _) =>
    let T := type of x in
    t (@id T)
  end.

Ltac prove_comparable_simple_inductive :=
  let x := fresh "x" in let y := fresh "y" in
  apply make_comparable; intros x y; destruct x; destruct y;
  prove_decidable_eq.

Ltac prove_comparable_trivial_inductive :=
  let aux T f :=
    refine (let f : (T -> T -> bool) :=
      ltac:(intros t1 t2; remember t1 as t1' eqn: E1; remember t2 as t2' eqn: E2; destruct t1, t2;
            let t1 := type of E1 in let t2 := type of E2 in clear E1 E2;
            match t1 with
            | _ = ?t =>
              match t2 with
              | _ = t => exact true
              | _ => exact false
              end
            end) in _);
    let I := fresh "I" in
    constructors; intros t1 t2; applys Decidable_equiv (f t1 t2); [| apply bool_decidable ];
    destruct t1, t2; simpl; iff I; (inversion I || reflexivity) in
  match goal with
  | |- Comparable ?T =>
    let f := fresh T "_compare" in
    aux T f
  | |- Comparable ?T =>
    let f := fresh "compare" in
    aux T f
  end.

(* The next two tactics are inspired from the message of Pierre Courtieu:
  [Coq-Club] using Ltac to retrieve the name of an induction principle from the type. *)
Ltac hd_of_app t :=
  lazymatch t with
  | (?f _) => hd_of_app f
  | _ => t
  end.

Ltac find_elem typ :=
  constr:(ltac:(constructors*):typ).

Ltac find_rec typ :=
  let X := constr:(fun x : typ => ltac:(induction x; exact I) : True) in
  let h := find_elem typ in
  let app := eval lazy beta in (X h) in
  let hd := hd_of_app app in
  hd.

Ltac find_rect t typ :=
  let T := type of t in
  let X := constr:(fun x : typ => ltac:(induction x; exact t) : T) in
  let h := find_elem typ in
  let app := eval lazy beta in (X h) in
  let hd := hd_of_app app in
  hd.

Ltac list_all_constructors :=
  lazymatch goal with
  | |- list ?T =>
    let rec aux t :=
      match t with
      | ?C = _ -> ?t =>
        let l := aux t in
        constr:(C :: l)
      | _ ?C -> ?t =>
        let l := aux t in
        constr:(C :: l)
      | _ => constr:(@nil T)
      end in
    let h := find_elem T in
    let ind_princip := find_rec T in
    let ind := constr:(ind_princip (fun x => x = h)) in
    let t := type of ind in
    let l := aux t in
    exact l
  end.

Ltac prove_comparable_trivial_inductive_faster :=
  let aux T f :=
    refine (let f : (T -> nat) := ltac:(
      lazymatch goal with
      | |- ?T -> _ =>
        let rec aux i t b :=
          lazymatch t with
          | ?C -> ?t =>
            let f := aux (S i) t b in
            constr:(f i)
          | _ => constr:(b)
          end in
        let ind_princip := find_rect O T in
        let ind := constr:(ind_princip (fun _ => nat)) in
        let t := type of ind in
        let f := aux O t ind in
        exact f
      end) in _);
    let I := fresh "I" in
    constructors; intros t1 t2; applys Decidable_equiv (f t1 = f t2); [| typeclass ];
    iff I; [ destruct t1; abstract (destruct t2; solve [ inversion I | reflexivity ]) | rewrite~ I ] in
  match goal with
  | |- Comparable ?T =>
    let f := fresh T "_to_nat" in
    aux T f
  | |- Comparable ?T =>
    let f := fresh "to_nat" in
    aux T f
  end.

Global Instance unit_comparable : Comparable unit.
Proof.
  prove_comparable_trivial_inductive.
Defined.

Global Instance False_comparable : Comparable False.
Proof.
  prove_comparable_trivial_inductive.
Defined.


(** * Some tactics about mem and Forall. **)

Ltac mem_solve :=
  solve [
      repeat first [ solve [ apply mem_here ] | apply mem_next ]
    | let M := fresh "M" in introv M; solve [ repeat inverts M as M ] ].

Ltac No_duplicates_solve :=
  repeat constructors; mem_solve.

Ltac Forall_splits :=
  repeat splits;
  repeat first [ apply Forall_nil | apply Forall_cons ].

Ltac Forall2_splits :=
  repeat splits;
  repeat first [ apply Forall2_nil | apply Forall2_cons ].


(** * Some extensions of LibContainer. **)

From TLC Require Import LibContainer.

Global Instance Comparable_BagIn_list : forall T,
    Comparable T ->
    BagIn T (list T) :=
  fun T C => Build_BagIn (@mem _).

Global Instance Comparable_BagIn_Decidable : forall T (t : T) (l : list T) `{Comparable T},
  Decidable (t \in l).
Proof. introv. simpl. typeclass. Qed.

Lemma BagIn_cons : forall T `{Comparable T} (x y : T) l,
  x \in (y :: l) <-> x = y \/ x \in l.
Proof. introv. iff I; (inverts I as I; [ left~ | right~ ]). Qed.

Global Instance BagEmpty_list : forall T,
    BagEmpty (list T) :=
  fun T => Build_BagEmpty nil.

Lemma BagInEmpty_list : forall T `{Comparable T} (t : T),
  t \notin (\{} : list T).
Proof. introv I. simpl in I. applys* mem_nil_inv I. Qed.

Global Instance BagSingle_list : forall T,
    BagSingle T (list T) :=
  fun T => Build_BagSingle (fun t => t :: nil).

Lemma BagInSingle_list : forall T `{Comparable T} (t1 t2 : T),
  t1 \in (\{t2} : list T) <-> t1 = t2.
Proof. introv. simpl. iff I; [repeat inverts I as I | substs ]; autos~. Qed.

Global Instance Comparable_BagRemove_list : forall T,
    Comparable T ->
    BagRemove (list T) T :=
  fun T C => Build_BagRemove (fun l t => LibList.remove t l).

Lemma BagRemove_list_notin : forall T `{Comparable T} l (t : T),
  t \notin l \- t.
Proof.
  introv I. simpl in I. rewrite remove_correct in I; autos*.
Qed.

Lemma BagRemove_list_in : forall T `{Comparable T} l (t1 t2 : T),
  t1 <> t2 ->
  t1 \in l ->
  t1 \in l \- t2.
Proof. introv D I. simpl in *. rewrite* remove_correct. Qed.

Global Instance Comparable_BagRemove_list_list : forall T,
    Comparable T ->
    BagRemove (list T) (list T) :=
  fun T C => Build_BagRemove (fun l1 l2 =>
    filter (fun t => decide (t \notin l2)) l1).

Lemma BagRemove_list_list : forall T `{Comparable T} (l1 l2 : list T) t,
  t \in l1 \- l2 <-> t \in l1 /\ t \notin l2.
Proof. introv. simpl. rewrite mem_filter_eq. rewrite decide_spec. rew_bool_eq*. Qed.

Global Instance Comparable_BagUnion_list : forall T,
    Comparable T ->
    BagUnion (list T) :=
  fun T C => Build_BagUnion (fun l1 l2 => l1 ++ (l2 \- l1)).

Lemma BagUnion_list : forall T `{Comparable T} (l1 l2 : list T) t,
  t \in l1 \u l2 <-> t \in l1 \/ t \in l2.
Proof.
  introv. simpl. rewrite mem_app_eq. rewrite mem_filter_eq.
  rewrite decide_spec. rew_bool_eq. iff~ [I|I].
  - inverts~ I.
  - tests I': (t \in l1); autos~.
Qed.

Global Instance Comparable_BagInter_list : forall T,
    Comparable T ->
    BagInter (list T) :=
  fun T C => Build_BagInter (fun l1 l2 =>
    filter (fun t => decide (t \in l1)) l2).

Lemma BagInter_list : forall T `{Comparable T} (l1 l2 : list T) t,
  t \in l1 \n l2 <-> t \in l1 /\ t \in l2.
Proof.
  introv. simpl. rewrite mem_filter_eq. rewrite decide_spec. rew_istrue*.
Qed.

Global Instance Comparable_BagIncl_list : forall T,
    Comparable T ->
    BagIncl (list T) :=
  fun T C => Build_BagIncl (fun l1 l2 => Forall (fun t => mem t l2) l1).

Global Instance Comparable_BagIncl_Decidable : forall T `{Comparable T} (l1 l2 : list T),
  Decidable (l1 \c l2).
Proof. introv. simpl. typeclass. Qed.

Lemma BagIncl_refl : forall T `{Comparable T} (l : list T),
  l \c l.
Proof. introv. simpl. rewrite~ Forall_eq_forall_mem. Qed.

Lemma BagInIncl : forall T `{Comparable T} (l1 l2 : list T) t,
  t \in l1 ->
  l1 \c l2 ->
  t \in l2.
Proof.
  introv I C. simpls. rewrite~ Forall_eq_forall_mem in C.
Qed.

Lemma BagInIncl_make : forall T `{Comparable T} (l1 l2 : list T),
  (forall_ t \in l1, t \in l2) ->
  l1 \c l2.
Proof.
  introv I. simpls. rewrite~ Forall_eq_forall_mem.
Qed.

Lemma BagIncl_trans : forall T `{Comparable T} (l1 l2 l3 : list T),
  l1 \c l2 ->
  l2 \c l3 ->
  l1 \c l3.
Proof.
  introv I1 I2. applys BagInIncl_make. simpls. rewrite Forall_eq_forall_mem in *. autos*.
Qed.

Lemma BagInclEmpty : forall T `{Comparable T} (l : list T),
  \{} \c l.
Proof. introv. apply BagInIncl_make. introv I. false~ BagInEmpty_list I. Qed.

Lemma BagIncl_cons : forall T `{Comparable T} l1 l2 (t : T),
  t \in l2 ->
  l1 \c l2 ->
  (t :: l1) \c l2.
Proof. introv M I. applys~ Forall_cons. Qed.

Lemma BagUnionIncl_left : forall T `{Comparable T} (l1 l2 : list T),
  l1 \c l1 \u l2.
Proof. introv. apply BagInIncl_make. introv I. rewrite* BagUnion_list. Qed.

Lemma BagUnionIncl_right : forall T `{Comparable T} (l1 l2 : list T),
  l2 \c l1 \u l2.
Proof. introv. apply BagInIncl_make. introv I. rewrite* BagUnion_list. Qed.

Lemma BagInterIncl_left : forall T `{Comparable T} (l1 l2 : list T),
  l1 \n l2 \c l1.
Proof. introv. apply BagInIncl_make. introv I. rewrite* BagInter_list in I. Qed.

Lemma BagInterIncl_right : forall T `{Comparable T} (l1 l2 : list T),
  l1 \n l2 \c l2.
Proof. introv. apply BagInIncl_make. introv I. rewrite* BagInter_list in I. Qed.

Lemma BagUnionIncl_combine : forall T `{Comparable T} (l1 l2 l3 : list T),
  l1 \c l3 ->
  l2 \c l3 ->
  l1 \u l2 \c l3.
Proof.
  introv I1 I2. apply BagInIncl_make. introv Iu. apply BagUnion_list in Iu.
  inverts Iu as I; applys~ BagInIncl I.
Qed.

Lemma BagInterIncl_combine : forall T `{Comparable T} (l1 l2 l3 : list T),
  l1 \c l2 ->
  l1 \c l3 ->
  l1 \c l2 \n l3.
Proof. introv I1 I2. apply BagInIncl_make. introv I. apply BagInter_list. splits~; applys~ BagInIncl I. Qed.

Global Instance Comparable_BagDisjoint_list : forall T,
    Comparable T ->
    BagDisjoint (list T) :=
  fun T C => Build_BagDisjoint (fun l1 l2 => Forall (fun t => ~ mem t l1) l2).

Global Instance Comparable_BagDisjoint_Decidable : forall T `{Comparable T} (l1 l2 : list T),
  Decidable (l1 \# l2).
Proof. introv. simpl. typeclass. Qed.

Lemma BagDisjoint_in : forall T `{Comparable T} (l1 l2 : list T),
  l1 \# l2 <-> ~ exists t, t \in l1 /\ t \in l2.
Proof.
  introv. simpl. rewrite Forall_eq_forall_mem. rew_logic*.
Qed.

Lemma BagDisjoint_com : forall T `{Comparable T} (l1 l2 : list T),
  l1 \# l2 <-> l2 \# l1.
Proof. introv. repeat rewrite BagDisjoint_in. rew_logic*. Qed.


(** Tries to solve a goal of the form [l1 \c l2]. **)
Ltac solve_incl :=
  repeat first [
      apply~ BagUnionIncl_combine
    | apply~ BagInterIncl_combine ];
  solve [
      apply~ BagIncl_refl
    | apply~ BagInclEmpty
    | apply~ BagUnionIncl_left
    | apply~ BagUnionIncl_right
    | apply~ BagInterIncl_left
    | apply~ BagInterIncl_right
    | repeat (apply~ BagIncl_cons; [mem_solve|]); apply~ BagInclEmpty
    | autos~
    | apply* BagInIncl_make ].


(** * Case analysis on lists **)

(** Given an hypothesis [T] stating that an element is present in a list,
  it explodes the goal in as many subgoal as needed, each of them only
  considering only one element of the list.
  For instance [x \in [a ; b]] is replaced by two goals, one with [x = a]
  and the other with [x = b].
  It supports various ways to state that an element is in a list. **)
Ltac explode_list T :=
  lazymatch type of T with
  | ?x \in nil =>
    false~ BagInEmpty_list T
  | ?x \in (cons ?y nil) =>
    let T' := fresh1 T in
    asserts T': (x = y); [ eapply BagInSingle_list; apply T |];
    clear T; rename T' into T
  | ?x \in (?y :: ?l) =>
    apply BagIn_cons in T;
    let T' := fresh1 T in
    lets [T'|T']: (rm T);
    [ try rename T' into T
    | (rename T' into T ; explode_list T) || explode_list T' ]
  | mem ?x nil =>
    rewrite mem_nil_eq in T; false~ T
  | mem ?x (?y :: ?l) =>
    rewrite mem_cons_eq in T;
    let T' := fresh1 T in
    lets [T'|T']: (rm T);
    [ try rename T' into T
    | (rename T' into T ; explode_list T) || explode_list T' ]
  | decide _ =>
    rewrite decide_spec in T; rew_bool_eq in T; explode_list T
  | List.In ?x nil =>
    false~ List.in_nil T
  | List.In ?x (?y :: ?l) =>
    let T' := fresh1 T in
    lets [T'|T']: List.in_inv (rm T);
    [ try rename T' into T
    | (rename T' into T ; explode_list T) || explode_list T' ]
  end.


(** * Miscellaneous **)

(** See message “[Coq-Club] finer control over typeclass instance refinement” on the Coq list. **)

Tactic Notation "oexact'" open_constr(term) :=
  exact term.

Tactic Notation "oexact" uconstr(term) :=
  lazymatch goal with
  |- ?G => oexact' (term : G)
  end.

Tactic Notation "orefine" uconstr(term) :=
  unshelve oexact term;
  shelve_unifiable.

Tactic Notation "simple" "orefine" uconstr(term) :=
  unshelve oexact term.

