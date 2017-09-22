(** General lemmae.
  * This file contains all the construct that I consider should be in my libraries by are not.
  * It can be seen as a personnal library. **)

Require Import TLC.LibStream TLC.LibHeap TLC.LibString TLC.LibNat TLC.LibInt.
Require Export TLC.LibTactics TLC.LibReflect TLC.LibLogic TLC.LibList TLC.LibBool.

Notation " [ ] " := nil : list_scope.
Notation " [ x ] " := (cons x nil) : list_scope.
Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..) : list_scope.

Set Implicit Arguments.

Lemma length_datatype_length : forall A (l : list A),
  length l = Datatypes.length l.
Proof. introv. induction~ l. simpl. rewrite~ length_cons. Qed.

Lemma seq_length : forall len start,
  length (seq start len) = len.
Proof. introv. rewrite length_datatype_length. apply~ seq_length. Qed.

(** * To be added in TLC when the library will be ready. **)

(* The following lemmae should be added in TLC. I have a version of
  the commit in this computer, but the branch coq-8.6 of TLC is frozen
  and the branch coq-8.6-new does not yet compile. Frustration. *)

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
   introv N1. inverts N1.
   constructors.
   do 2 rewrite length_cons. inverts I as I1 I2. rewrite* IHl1 in I2.
   introv N1 N2. inverts I as I1 I2. rewrite IHl1 in I2. inverts N1; inverts~ N2.
    apply* (proj2 I2).
   constructors.
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
   transitivity (length l2); autos*.
   introv N1 N2. asserts (v&N): (exists v, Nth n l2 v); [| autos* ].
    apply length_Nth_lt. rewrite (proj1 F23). apply* Nth_lt_length.
Qed.

Lemma Forall2_Forall : forall A1 A2 (P : _ -> Prop) (Q : _ -> _ -> Prop)
    (l1 : list A1) (l2 : list A2),
  Forall P l1 ->
  Forall2 Q l1 l2 ->
  Forall2 (fun a b => P a /\ Q a b) l1 l2.
Proof.
  introv F F2. gen l2. induction F; introv F2; inverts F2; constructors~.
Qed.

Lemma Forall2_combine : forall A1 A2 A3 (P Q : _ -> _ -> Prop)
    (l1 : list A1) (l2 : list A2) (l3 : list A3),
  Forall2 P l1 l2 ->
  Forall2 Q l1 l3 ->
  Forall2 (fun a bc => P a (fst bc) /\ Q a (snd bc)) l1 (combine l2 l3).
Proof.
  introv F1 F2. gen l3. induction F1; introv F2; inverts F2; constructors~.
Qed.

Instance Forall2_Decidable_Mem : forall A B (P : A -> B -> Prop) l1 l2,
  (forall a b, Mem a l1 -> Mem b l2 -> Decidable (P a b)) ->
  Decidable (Forall2 P l1 l2).
Proof.
  introv F. gen l2. induction l1 as [|a l1]; introv F.
   destruct l2.
    applys Decidable_equiv True.
     iff~ I. constructors.
     typeclass.
    applys Decidable_equiv False.
     iff I; tryfalse. inverts~ I.
     typeclass.
   destruct l2 as [|b l2].
    applys Decidable_equiv False.
     iff I; tryfalse. inverts~ I.
     typeclass.
    applys Decidable_equiv (P a b /\ Forall2 P l1 l2).
     iff I.
      constructors*.
      inverts* I.
     apply and_decidable.
      typeclass.
      apply IHl1. introv M1 M2. apply* F.
Defined.

Global Instance Forall2_Decidable : forall A B (P : A -> B -> Prop) l1 l2,
  (forall a b, Decidable (P a b)) ->
  Decidable (Forall2 P l1 l2).
Proof.
  introv F. apply~ Forall2_Decidable_Mem.
Defined.


Lemma Mem_Nth : forall A l (x : A),
  Mem x l ->
  exists n, Nth n l x.
Proof. introv M. rewrite Mem_mem in M. apply* mem_Nth. Qed.

Lemma Nth_Mem : forall A l (x : A) n,
  Nth n l x ->
  Mem x l.
Proof. introv N. rewrite Mem_mem. apply* Nth_mem. Qed.


Lemma Mem_last_inv : forall A l (x e : A),
  Mem x (l & e) ->
  x = e \/ Mem x l.
Proof. introv M. rewrite Mem_mem in *. rewrite mem_last in M. rew_refl~ in M. Qed.

Lemma Mem_in_last : forall A l (x e : A),
  Mem x l ->
  Mem x (l & e).
Proof. introv M. rewrite Mem_mem in *. rewrite mem_last. rew_refl*. Qed.

Lemma Nth_add_last : forall A l (x e : A) n,
  Nth n l x ->
  Nth n (l & e) x.
Proof. introv N. induction N; constructors~. Qed.

Lemma Nth_last : forall A l (x : A),
  Nth (length l) (l & x) x.
Proof. introv. induction l; rew_list; constructors~. Qed.

Lemma Mem_map_inv : forall A B (f : A -> B) l y,
  Mem y (map f l) ->
  exists x,
    Mem x l /\ y = f x.
Proof.
  induction l; introv M.
  - inverts M.
  - rewrite map_cons in M. inverts M as M.
    + exists* a.
    + forwards* (x&Mx&Ex): (rm IHl) M.
Qed.

Global Instance No_duplicates_decidable : forall A (l : list A),
    Comparable A ->
    Decidable (No_duplicates l).
  introv C. induction l.
   applys Decidable_equiv True.
    splits~.
    typeclass.
   applys Decidable_equiv (~ Mem a l /\ No_duplicates l).
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
  ~ Mem a l ->
  find_index_def n a l = n + length l.
Proof.
  introv N. unfold find_index_def. gen n. induction l using list_ind_last; introv.
   simpl. rewrite~ length_nil.
   rewrite fold_right_last. rewrite IHl.
    cases_if.
     false N. apply* Mem_last.
     rewrite length_last. rewrite~ PeanoNat.Nat.add_assoc.
    introv M. false N. apply* Mem_in_last.
Qed.

Lemma find_index_nth : forall A (a : A) l,
  Mem a l ->
  Nth (find_index a l) l a.
Proof.
  introv M. unfold find_index. generalize 0. induction l using list_ind_last; introv.
   inverts* M.
   unfolds find_index_def. rewrite fold_right_last. apply Mem_last_inv in M.
    tests M': (Mem a l).
     apply* Nth_add_last.
     cases_if.
      fold (find_index_def 0 a0 l). rewrite~ find_index_def_length. simpl. apply* Nth_last.
      inverts* M.
Qed.

Fixpoint nth_option A n (l : list A) {struct l} :=
  match l with
  | [] => None
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


Lemma stream_head_nth : forall A (s : stream A),
  stream_head s = LibStream.nth 0 s.
Proof. introv. destruct* s. Qed.

Lemma stream_tail_nth : forall A (s : stream A) n,
  LibStream.nth n (stream_tail s) = LibStream.nth (1 + n) s.
Proof. introv. destruct* s. Qed.


Lemma read_option_indom : forall K `{Comparable K} V (h : heap K V) k v,
  read_option h k = Some v ->
  indom h k.
Proof. introv E. forwards B: @read_option_binds E. applys~ @binds_indom B. Qed.

Lemma indom_read_option : forall K `{Comparable K} V (h : heap K V) k,
  indom h k ->
  exists v, read_option h k = Some v.
Proof.
  introv I. forwards (v&B): @indom_binds I.
  exists v. applys~ @binds_read_option B.
Qed.

Lemma read_option_write_same : forall K `{Comparable K} V (h : heap K V) k v,
  read_option (write h k v) k = Some v.
Proof. introv. apply binds_read_option. applys~ @binds_write_eq. Qed.

Lemma not_indom_write : forall K V (h : heap K V) k k' v',
  k <> k' ->
  ~ indom h k ->
  ~ indom (write h k' v') k.
Admitted.

Lemma read_option_write : forall K `{Comparable K} V (h : heap K V) k k' v,
  k <> k' ->
  read_option (write h k v) k' = read_option h k'.
Proof.
  introv D. tests I: (indom h k').
   forwards (v'&E): indom_read_option I. rewrite E.
    apply read_option_binds in E. apply binds_read_option.
    applys~ @binds_write_neq E.
   rewrite (not_indom_read_option I). forwards I': not_indom_write I.
    introv E. apply D. symmetry. apply* E.
    rewrite~ (not_indom_read_option I').
Qed.


Definition list_to_string :=
  fold_left (fun c str => String c str) EmptyString.

Fixpoint string_to_list (str : string) :=
  match str with
  | EmptyString => nil
  | String c str =>
    c :: string_to_list str
  end.


Fixpoint divide_list {A} (l : list A) :=
  match l with
  | nil => (nil, nil)
  | x :: nil => ([x], nil)
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

Lemma divide_list_Mem : forall A l (x : A) l1 l2,
  Mem x l ->
  divide_list l = (l1, l2) ->
  Mem x l1 \/ Mem x l2.
Proof.
  introv M E. gen l1 l2. induction M; introv E.
  - destruct l; inverts E as E; autos~. destruct divide_list. inverts~ E.
  - destruct (divide_list l) as [la lb] eqn: El. erewrite divide_list_cons in E; autos*.
    inverts E. forwards*: (rm IHM).
Qed.

Lemma divide_list_Mem_inv : forall A l (x : A) l1 l2,
  Mem x l1 \/ Mem x l2 ->
  divide_list l = (l1, l2) ->
  Mem x l.
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

Lemma divide_list_No_duplicates : forall A (l l1 l2 : list A),
  No_duplicates l ->
  divide_list l = (l1, l2) ->
  No_duplicates l1 /\ No_duplicates l2.
Proof.
  introv ND E. gen l1 l2. induction l; introv E.
  - inverts~ E.
  - destruct (divide_list l) as [la lb] eqn: El. erewrite divide_list_cons in E; autos*.
    inverts E. forwards~ (ND1&ND2): (rm IHl).
    + inverts~ ND.
    + splits~. constructors~. introv M. forwards M': divide_list_Mem_inv El.
      * right*.
      * inverts* ND.
Qed.

Lemma divide_list_Mem_No_duplicates : forall A l (x : A) l1 l2,
  Mem x l ->
  No_duplicates l ->
  divide_list l = (l1, l2) ->
  Mem x l1 ->
  Mem x l2 ->
  False.
Proof.
  introv M ND E. gen l1 l2. induction l; introv E M1 M2.
  - inverts E. invert M1.
  - destruct (divide_list l) as [la lb] eqn: El. erewrite divide_list_cons in E; autos*.
    inverts E. inverts M1 as M1.
    + forwards: divide_list_Mem_inv El.
      * left*.
      * inverts* ND.
    + applys~ IHl.
      * applys~ divide_list_Mem_inv El.
      * inverts~ ND.
Qed.


Instance nat_lt_Decidable : forall n1 n2 : nat,
    Decidable (n1 < n2)%nat.
  intros. applys Decidable_equiv.
   symmetry. apply nat_compare_lt.
   typeclass.
Defined.

Instance Z_lt_Decidable : forall n1 n2,
    Decidable (n1 < n2)%Z.
  intros. applys Decidable_equiv Z.compare_lt_iff. typeclass.
Defined.

Instance lt_Decidable : forall n1 n2,
    Decidable (n1 < n2).
  intros. applys Decidable_equiv (n1 < n2)%Z.
   math.
   typeclass.
Defined.

Instance lt_nat_Decidable : forall n1 n2,
    Decidable (@lt nat (@lt_from_le nat le_nat_inst) n1 n2).
  intros. applys Decidable_equiv (lt_Decidable n1 n2). math.
Defined.

Instance nat_gt_Decidable : forall n1 n2 : nat,
    Decidable (n1 > n2)%nat.
  intros. applys Decidable_equiv.
   symmetry. apply nat_compare_lt.
   typeclass.
Defined.

Instance Z_gt_Decidable : forall n1 n2,
    Decidable (n1 > n2)%Z.
  intros. applys sumbool_decidable Z_gt_dec.
Defined.

Instance gt_Decidable : forall n1 n2,
    Decidable (n1 > n2).
  intros. applys Decidable_equiv (n1 > n2)%Z.
   math.
   typeclass.
Defined.

Instance gt_nat_Decidable : forall n1 n2,
    Decidable (@gt nat (@gt_from_le nat le_nat_inst) n1 n2).
  intros. applys Decidable_equiv (gt_Decidable n1 n2). math.
Defined.


Instance Ascii_comparable : Comparable Ascii.ascii.
  apply make_comparable. intros. applys sumbool_decidable Ascii.ascii_dec.
Defined.


(** * Tactics about Comparable **)

Instance Comparable_Decidable : forall A (a1 a2 : A),
    Comparable A ->
    Decidable (a1 = a2).
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
      applys decidable_make false; abstract (fold_bool; rew_refl; discriminate)
    | _ =>
      applys decidable_make true; abstract (fold_bool; rew_refl; reflexivity)
    (** Look for already defined typeclasses **)
    | _ =>
      typeclass || (apply Comparable_Decidable; typeclass)
    (** A little trivial case **)
    | _ =>
      match goal with
      |- Decidable (?f1 = ?f2) =>
        abstract (
          let D := fresh "D" in asserts D: (tr f1 <> tr f2);
          [ discriminate
          | applys decidable_make false; fold_bool; rew_refl;
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
            rewrite decide_spec; rewrite isTrue_eq_isTrue; iff I;
            [ lets (I1&I2): (rm I); try rewrite I1; rewrite~ I2
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
  match goal with
  | |- Decidable (?x = _) =>
    let T := type of x in
    t (@id T)
  end.

Ltac prove_comparable_simple_inductive :=
  let x := fresh "x" in let y := fresh "y" in
  apply make_comparable; intros x y; destruct x; destruct y;
  prove_decidable_eq.


Global Instance unit_comparable : Comparable unit.
  prove_comparable_simple_inductive.
Defined.

Global Instance False_comparable : Comparable False.
  prove_comparable_simple_inductive.
Defined.


(** * Some tactics about Mem and Forall. **)

Ltac Mem_solve :=
  solve [
      repeat first [ solve [ apply Mem_here ] | apply Mem_next ]
    | let M := fresh "M" in introv M; solve [ repeat inverts M as M ] ].

Ltac No_duplicates_solve :=
  repeat constructors; Mem_solve.

Ltac Forall_splits :=
  repeat splits;
  repeat first [ apply Forall_nil | apply Forall_cons ].

Ltac Forall2_splits :=
  repeat splits;
  repeat first [ apply Forall2_nil | apply Forall2_cons ].

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

