(** This file formalises bit fields of a given size. **)

Set Implicit Arguments.
From Lib Require Export Common.
From Lib Require Export LibExec.
From TLC Require Import LibInt LibNat LibLogic.


(** * Structure Definition **)

Fixpoint nbits (n : nat) : Type :=
  match n with
  | O => unit
  | S n => bool * nbits n
  end.


(** * Reading **)

Definition nth_bit (m n : nat) : nbits m -> (n < m)%nat -> bool.
  introv a I. gen m. induction n as [|n]; introv a I; destruct m; try solve [ false; nat_math ].
  - exact (fst a).
  - applys IHn (snd a). nat_math.
Defined.
Global Arguments nth_bit [m] n.

(** A tactic to fill out the [n < m] part.
  The call to nth_bit should be on the form [nth_bit n a ltac:nbits_ok]. **)
Ltac nbits_ok :=
  clear;
  repeat match goal with
  | |- context [ ?a ] =>
    match type of a with
    | Z => unfold a
    | nat => unfold a
    end
  end;
  abstract
    lazymatch goal with
    | [ |- (_ < _)%nat ] =>
      (* The [math] tactic does not work with the [^] operator.
        We thus first eliminate it. *)
      repeat rewrite Nat.pow_succ_r;
      repeat rewrite Nat.pow_0_r;
      nat_math
    end.

Lemma rewrite_nth_bit : forall n m (a : nbits m) (I I' : (n < m)%nat),
  nth_bit n a I = nth_bit n a I'.
Proof.
  induction n; introv; destruct m; try solve [ false; nat_math ].
  - reflexivity.
  - simpl. erewrite IHn. reflexivity.
Qed.

Lemma rewrite_O_nth_bit : forall n (a : nbits (S n)) (I : (0 < S n)%nat),
  nth_bit 0 a I = fst a.
Proof. introv. reflexivity. Qed.

Lemma rewrite_S_nth_bit : forall n m (a : nbits (S m)) (I : (S n < S m)%nat) (I' : (n < m)%nat),
  nth_bit (S n) a I = nth_bit n (snd a) I'.
Proof. introv. erewrite rewrite_nth_bit with (n := n). simpl. reflexivity. Qed.

Lemma nth_bit_eq : forall n (x y : nbits n),
  (forall m (I : (m < n)%nat), nth_bit _ x I = nth_bit _ y I) -> x = y.
Proof.
  induction n; introv E.
  - destruct x, y. reflexivity.
  - destruct x as [b1 x], y as [b2 y]. rewrite IHn with x y.
    + set (eq := E 0%nat ltac:(nbits_ok)). do 2 rewrite rewrite_O_nth_bit in eq.
      simpl in eq. substs~.
    + introv. asserts Im: (S m < S n)%nat. { nat_math. }
      set (eq := E (S m) Im). do 2 rewrite rewrite_S_nth_bit with (I' := I) in eq. apply eq.
Qed.


(** * Writing **)

Definition write_nbit (m n : nat) : (n < m)%nat -> bool -> nbits m -> nbits m.
  introv I b a. gen m. induction n as [|n]; introv I a; destruct m; try solve [ false; nat_math ].
  - exact (b, snd a).
  - refine (fst a, IHn _ _ (snd a)). nat_math.
Defined.
Arguments write_nbit [m] n.

Lemma rewrite_write_nbit : forall n m (a : nbits m) (I I' : (n < m)%nat) b,
  write_nbit n I b a = write_nbit n I' b a.
Proof. introv. fequals. Qed.

Lemma rewrite_S_write_nbit : forall n m (a : nbits (S m)) (I : (S n < S m)%nat) (I' : (n < m)%nat) b,
  write_nbit (S n) I b a = (fst a, write_nbit n I' b (snd a)).
Proof. introv. erewrite rewrite_write_nbit with (n := n). simpl. reflexivity. Qed.

Lemma write_nth_bit : forall n m (I : (n < m)%nat) b (a : nbits m),
  nth_bit n (write_nbit n I b a) I = b.
Proof.
  induction n; introv; destruct m; try solve [ false; nat_math ].
  - reflexivity.
  - asserts I': (n < m)%nat. { nat_math. }
    rewrite rewrite_S_nth_bit with (I' := I'). rewrite rewrite_S_write_nbit with (I' := I').
    simpl. rewrite~ IHn.
Qed.


(** * Creating **)

Fixpoint nbits_init (n : nat) : nbits n :=
  match n with
  | O => tt
  | S n => (false, nbits_init n)
  end.
Arguments nbits_init {n}.

Lemma nbits_init_read : forall n m (I : (n < m)%nat),
  nth_bit n nbits_init I = false.
Proof.
  induction n; introv; destruct m; try solve [ false; nat_math ].
  - reflexivity.
  - asserts I': (n < m)%nat. { nat_math. }
    rewrite rewrite_S_nth_bit with (I' := I'). rewrite~ IHn.
Qed.


(** * Conversions **)

(** ** To and From Lists **)

Definition nbits_to_list n (a : nbits n) : list bool.
  induction n.
  - exact nil.
  - exact (fst a :: IHn (snd a)).
Defined.
Arguments nbits_to_list [n].

Lemma nbits_to_list_cons : forall n (a : nbits n) b,
  nbits_to_list ((b, a) : nbits (S n)) = b :: nbits_to_list a.
Proof. reflexivity. Qed.

Lemma nbits_to_list_length : forall n (a : nbits n),
  length (nbits_to_list a) = n.
Proof.
  induction n; introv.
  - reflexivity.
  - simpl. rew_list. rewrite~ IHn.
Qed.

Lemma nbits_to_list_nth : forall n (a : nbits n) d m I,
  nth_default d m (nbits_to_list a) = nth_bit m a I.
Proof.
  induction n; introv.
  - false. nat_math.
  - destruct m as [|m].
    + reflexivity.
    + simpl. rewrite nth_default_cons. erewrite~ IHn.
Qed.

Fixpoint list_to_nbits (l : list bool) : nbits (length l) :=
  match l return nbits (length l) with
  | nil => tt
  | b :: l => (b, list_to_nbits l)
  end.

Lemma list_to_nbits_to_list : forall l,
  nbits_to_list (list_to_nbits l) = l.
Proof.
  introv. induction l as [|b l].
  - reflexivity.
  - simpl. rewrite (nbits_to_list_cons _ (list_to_nbits l) _). fequals~.
Qed.


(** ** To and From Natural Numbers **)

Definition nbits_to_nat n (a : nbits n) : nat.
  (** Important note: the first bit in this representation has the lower weight. **)
  induction n.
  - exact 0%nat.
  - exact ((if fst a then 1 else 0) + 2 * IHn (snd a))%nat.
Defined.
Arguments nbits_to_nat [n].

Lemma rewrite_nbits_to_nat : forall n (a : nbits (S n)),
  nbits_to_nat a = ((if fst a then 1 else 0) + 2 * nbits_to_nat (snd a))%nat.
Proof. reflexivity. Qed.

Definition nat_to_nbits n m : (m < 2 ^ n)%nat -> nbits n.
  introv I. gen m. induction n; introv I.
  - exact tt.
  - refine (decide (m mod 2 = 1), IHn (m / 2) _)%nat.
    apply~ Nat.div_lt_upper_bound.
Defined.
Arguments nat_to_nbits [n] m.

Lemma rewrite_nat_to_nbits : forall n m I I',
  nat_to_nbits m I = (nat_to_nbits m I' : nbits n).
Proof. introv. fequals. Qed.

Lemma rewrite_nat_to_nbits_cons : forall n m I I',
  nat_to_nbits m I = ((decide (m mod 2 = 1), nat_to_nbits (m / 2) I') : nbits (S n)).
Proof.
  introv. unfold nat_to_nbits. simpl. repeat fequals.
  apply decide_equiv. forwards E: (Nat.divmod_spec m 1 0 1); [nat_math|].
  destruct Nat.divmod. destruct E as [E I2].
  simpl. repeat rewrite Nat.add_0_r in E. rewrite E.
  asserts E': (((n0 + n0 + match n1 with 0 => 1 | S _ => 0 end)%nat : int%I)
               = (match n1 with 0 => 1 | S _ => 0 end)%nat + n0 * 2).
  { destruct n1; math. }
  rewrites (rm E'). rewrite Z_mod_plus_full. rewrite Z.mod_small; destruct n1; math.
Qed.

Lemma nat_to_nbits_to_nat : forall n m I,
  nbits_to_nat (nat_to_nbits m I : nbits n) = m.
Proof.
  introv. gen m. induction n; introv.
  - simpls. nat_math.
  - asserts I': (m / 2 < 2 ^ n)%nat. { apply~ Nat.div_lt_upper_bound. }
    rewrite rewrite_nat_to_nbits_cons with (I' := I'). rewrite rewrite_nbits_to_nat.
    unfold snd, fst. rewrite IHn. rewrite Nat.add_comm.
    asserts E: ((ifb (m mod 2)%Z = 1%Z then 1 else 0) = m mod 2)%nat.
    { asserts Z2: (nat_to_Z 2%nat = 2); [ math |].
      cases_if as D; rewrite decide_spec in D; rew_bool_eq in D.
      - asserts G: (m mod 2%nat = 1%nat); [ rewrite Z2; math |].
        rewrite <- mod_Zmod in G; math.
      - forwards (I1&I2): (Z.mod_pos_bound m 2); [ math |].
        asserts G: (m mod 2%nat = 0%nat); [ rewrite Z2; math |].
        rewrite <- mod_Zmod in G; math. }
    rewrite E. rewrite~ <- Nat.div_mod.
Qed.

Lemma nat_to_nbits_init : forall n (I : (0 < 2 ^ n)%nat),
  nbits_init = nat_to_nbits 0 I.
Proof.
  introv. apply nth_bit_eq. introv. rewrite nbits_init_read. symmetry.
  gen n. induction m; introv; (destruct n; [nat_math|]).
  - rewrite rewrite_O_nth_bit. simpl. rewrite decide_spec. rew_bool_eq*.
  - asserts I': (m < n)%nat. { nat_math. }
    rewrite rewrite_S_nth_bit with (I' := I').
    asserts I2: (0 / 2 < 2 ^ n)%nat. { simpl. forwards: (Nat.pow_nonzero 2 n); nat_math. }
    rewrite rewrite_nat_to_nbits_cons with (I' := I2). apply IHm.
Qed.

Lemma nbits_to_nat_init : forall n,
  nbits_to_nat (nbits_init : nbits n) = 0%nat.
Proof.
  induction n.
  - reflexivity.
  - rewrite rewrite_nbits_to_nat. simpl. rewrite* IHn.
Qed.

Definition nat_to_nbits_check : forall n, nat -> option (nbits n).
  introv m. destruct (decide (m < 2 ^ n)%nat) eqn: E.
  - refine (Some (nat_to_nbits m _)). rewrite decide_spec in E. rew_bool_eq~ in E.
  - exact None.
Defined.
Arguments nat_to_nbits_check [n].

Lemma rewrite_decide_if_true : forall A P `{Decidable P} f1 f2 (E : decide P = true),
  (if decide P as b return decide P = b -> A then f1 else f2) eq_refl = f1 E.
Proof. introv. destruct (decide P); tryfalse. erewrite~ (proof_irrelevance E). Qed.

Lemma rewrite_decide_if_false : forall A P `{Decidable P} f1 f2 (E : decide P = false),
  (if decide P as b return decide P = b -> A then f1 else f2) eq_refl = f2 E.
Proof. introv. destruct (decide P); tryfalse. erewrite~ (proof_irrelevance E). Qed.

Lemma nat_to_nbits_check_correct : forall n m (I : (m < 2 ^ n)%nat),
  nat_to_nbits_check m = Some (nat_to_nbits m I).
Proof.
  introv. unfolds nat_to_nbits_check.
  asserts E: (decide (m < 2 ^ n)%nat = true). { rewrite decide_spec. rew_bool_eq*. }
  rewrite rewrite_decide_if_true with (E := E). erewrite~ rewrite_nat_to_nbits.
Qed.

Lemma nat_to_nbits_check_out : forall n m,
  (m >= 2 ^ n)%nat ->
  @nat_to_nbits_check n m = None.
Proof.
  introv I. unfolds nat_to_nbits_check.
  asserts E: (decide (m < 2 ^ n)%nat = false). { rewrite decide_spec. rew_bool_eq~. nat_math. }
  rewrite rewrite_decide_if_false with (E := E). reflexivity.
Qed.

Definition int_to_nbits_check n z : option (nbits n) :=
  match z with
  | 0%Z => Some (@nat_to_nbits n 0 ltac:(forwards: (Nat.pow_nonzero 2 n); nat_math))
  | Z.pos p => nat_to_nbits_check (Pos.to_nat p)
  | Z.neg _ => None
  end.
Arguments int_to_nbits_check [n].

Lemma int_to_nbits_check_correct : forall (n : nat) (m : Z) (I : (Z.to_nat m < 2 ^ n)%nat),
  (0 <= m)%Z ->
  int_to_nbits_check m = Some (nat_to_nbits (Z.to_nat m) I).
Proof.
  introv I'. destruct m.
  - simpl. repeat fequals.
  - simpl. apply nat_to_nbits_check_correct.
  - apply Zle_not_lt in I'. false I'. apply Zlt_neg_0.
Qed.

Lemma int_to_nbits_check_out : forall n m,
  (Z.to_nat m >= 2 ^ n)%nat \/ (m < 0)%Z ->
  @int_to_nbits_check n m = None.
Proof.
  introv [I|I]; destruct m.
  - forwards: (Nat.pow_nonzero 2 n). { nat_math. }
    simpls. nat_math.
  - simpls. apply~ nat_to_nbits_check_out.
  - forwards: (Nat.pow_nonzero 2 n). { nat_math. }
    simpls. nat_math.
  - nat_math.
  - forwards: Zle_0_pos p. nat_math.
  - reflexivity.
Qed.




(** * Extracting Bits **)

(** ** First Bits **)

Definition nth_first_nbits n m (a : nbits n) (I : (m < n)%nat) : nbits m.
  gen n a. induction m; introv I a.
  - exact tt.
  - destruct n; try solve [ false; nat_math ]. refine (fst a, IHm _ _ (snd a)). nat_math.
Defined.
Arguments nth_first_nbits [n] m.

Lemma rewrite_nth_first_nbits : forall n m I I' (a : nbits n),
  nth_first_nbits m a I = nth_first_nbits m a I'.
Proof. introv. fequals. Qed.

Lemma rewrite_nth_first_nbits_cons : forall n m I I' (a : nbits (S n)),
  nth_first_nbits (S m) a I = (fst a, nth_first_nbits m (snd a) I').
Proof. introv. simpl. erewrite rewrite_nth_first_nbits. reflexivity. Qed.

Lemma nth_nth_first_nbits : forall n m (a : nbits n) Im k Ikn Ikm,
  nth_bit k a Ikn = nth_bit k (nth_first_nbits m a Im) Ikm.
Proof.
  introv. gen k n a. induction m; introv.
  - false. nat_math.
  - destruct n; try solve [ false; nat_math ]. destruct k.
    + reflexivity.
    + asserts I1: (k < m)%nat. { nat_math. }
      asserts I2: (k < n)%nat. { nat_math. }
      erewrite rewrite_S_nth_bit with (I' := I1).
      erewrite rewrite_S_nth_bit with (I' := I2).
      erewrite IHm. fequals.
Qed.

Lemma nat_from_nth_first_nbits : forall n m (a : nbits n) I,
  (nbits_to_nat a < 2 ^ m)%nat ->
  nbits_to_nat a = nbits_to_nat (nth_first_nbits m a I).
Proof.
  introv Im. gen n. induction m; introv Im.
  - simpls. nat_math.
  - destruct n; try solve [ false; nat_math ].
    asserts In: (m < n)%nat. { nat_math. }
    rewrite rewrite_nth_first_nbits_cons with (I' := In).
    do 2 rewrite rewrite_nbits_to_nat. fequals. fequals. apply IHm.
    simpls. nat_math.
Qed.


(** ** Any Bits **)

Definition sub_nbits n (start length : nat) (a : nbits n) (I : (start + length < n)%nat) : nbits length.
  gen n a. induction start; introv I a.
  - refine (nth_first_nbits length a _). nat_math.
  - destruct n; try solve [ false; nat_math ]. refine (IHstart _ _ (snd a)). nat_math.
Defined.
Arguments sub_nbits [n].

Lemma rewrite_sub_nbits : forall n start length (a : nbits n) I I',
  sub_nbits start length a I = sub_nbits start length a I'.
Proof. introv. fequals. Qed.

Lemma rewrite_sub_nbits_cons : forall n start length (a : nbits (S n)) I I',
  sub_nbits (S start) length a I = sub_nbits start length (snd a) I'.
Proof. introv. simpl. erewrite rewrite_sub_nbits. reflexivity. Qed.

Lemma rewrite_sub_nbits_zero : forall n length (a : nbits n) I I',
  sub_nbits 0 length a I = nth_first_nbits length a I'.
Proof. introv. simpl. fequals. Qed.


(** ** Writing SubSets of Bits **)

Definition write_nbits (n m : nat) start (v : nbits m) (I : (start + m < n)%nat) (a : nbits n) : nbits n.
  gen n a. induction start; introv I a.
  - gen n a v. induction m; introv I a v.
    + exact a.
    + destruct n; try solve [ false; nat_math ]. refine (fst v, IHm _ _ (snd a) (snd v)). nat_math.
  - destruct n; try solve [ false; nat_math ]. refine (fst a, IHstart _ _ (snd a)). nat_math.
Defined.
Arguments write_nbits [n m].

Lemma rewrite_write_nbits : forall n m start (v : nbits m) (a : nbits n) I I',
  write_nbits start v I a = write_nbits start v I' a.
Proof. introv. fequals. Qed.

Lemma rewrite_write_nbits_cons : forall n m start (v : nbits m) (a : nbits (S n)) I I',
  write_nbits (S start) v I a = (fst a, write_nbits start v I' (snd a)).
Proof. introv. simpl. erewrite rewrite_write_nbits. reflexivity. Qed.

Lemma rewrite_write_nbits_zero_cons : forall n m (v : nbits (S m)) (a : nbits (S n)) I I',
  write_nbits 0 v I a = (fst v, write_nbits 0 (snd v) I' (snd a)).
Proof. introv. simpl. repeat fequals. Qed.

Lemma sub_write_nbits : forall n m start (v : nbits m) (a : nbits n) I,
  sub_nbits start m (write_nbits start v I a) I = v.
Proof.
  introv. gen n m. induction start; introv.
  - asserts I': (m < n)%nat. { nat_math. }
    rewrite rewrite_sub_nbits_zero with (I' := I').
    gen n. induction m; introv.
    + destruct~ v.
    + destruct n; try solve [ false; nat_math ].
      asserts I'': (0 + m < n)%nat. { nat_math. }
      rewrite rewrite_write_nbits_zero_cons with (I' := I'').
      rewrite rewrite_nth_first_nbits_cons with (I' := I'').
      destruct v as [b v]. unfolds @snd. rewrite~ IHm.
  - destruct n; try solve [ false; nat_math ].
    asserts I': (start + m < n)%nat. { nat_math. }
    rewrite rewrite_write_nbits_cons with (I' := I').
    rewrite rewrite_sub_nbits_cons with (I' := I').
    apply* IHstart.
Qed.


(** * Instances **)

Global Instance nbits_Comparable : forall n, Comparable (nbits n).
Proof.
  introv. apply make_comparable. intros x y.
  applys Decidable_equiv (nbits_to_list x = nbits_to_list y).
  - iff E.
    + apply nth_bit_eq. introv. do 2 rewrite <- nbits_to_list_nth with (d := arbitrary). rewrite~ E.
    + substs~.
  - typeclass.
Defined.

Global Instance nbits_Inhab : forall n, Inhab (nbits n).
Proof.
  introv. apply Inhab_of_val. apply nbits_init.
Defined.


(** * Comparing Structures **)

Definition nbits_intersects n (a1 a2 : nbits n) :=
  exists n I, nth_bit n a1 I = true /\ nth_bit n a2 I = true.
Arguments nbits_intersects [n].

Instance Decidable_exists_inf : forall n P,
  (forall m (I : (m < n)%nat), Decidable (P m I)) ->
  Decidable (exists m I, P m I).
Proof.
  induction n; introv ID.
  - applys Decidable_equiv False.
    + iff I; tryfalse. lets (m&I'&H): (rm I). nat_math.
    + typeclass.
  - asserts Im: (forall m, (m < n)%nat -> (m < S n)%nat). { nat_math. }
    applys Decidable_equiv (P n ltac:(nat_math) \/ exists m I, P m (Im _ I)).
    + iff I.
      * inverts I as I; [autos*|]. lets* (m&I'&H): (rm I).
      * lets* (m&I'&H): (rm I). tests D: (m = n).
        -- left. erewrite proof_irrelevance. apply H.
        -- right. asserts I: (m < n)%nat. { nat_math. }
           exists m I. erewrite proof_irrelevance. apply H.
    + typeclass.
Defined.

Global Instance nbits_intersects_decidable : forall n (a1 a2 : nbits n),
  Decidable (nbits_intersects a1 a2).
Proof.
  introv. sets_eq f: (fun n I => decide (nth_bit n a1 I = true /\ nth_bit n a2 I = true)).
  applys Decidable_equiv (exists n I, istrue (f n I)).
  - splits; intros (m&I&H); exists m I.
    + rewrite EQf in H. rewrite decide_spec in H. rew_bool_eq in H. autos~.
    + rewrite EQf. rewrite decide_spec. rew_bool_eq~.
  - typeclass.
Defined.


(** * Operations **)

(** ** Negation **)

Definition nbits_not n (a : nbits n) : nbits n.
  induction n.
  - constructors.
  - exact (negb (fst a), IHn (snd a)).
Defined.
Arguments nbits_not [n].

Lemma nbits_not_nth_bit : forall n (a : nbits n) m I,
  nth_bit m (nbits_not a) I = negb (nth_bit m a I).
Proof.
  introv. gen n. induction m; introv; destruct n; try nat_math.
  - repeat rewrite rewrite_O_nth_bit. reflexivity.
  - asserts I': (m < n)%nat. { nat_math. }
    repeat rewrite rewrite_S_nth_bit with (I' := I'). apply IHm.
Qed.


(** ** Binary **)

Definition nbits_map2 (f : bool -> bool -> bool) n (a1 a2 : nbits n) : nbits n.
  induction n.
  - constructors.
  - exact (f (fst a1) (fst a2), IHn (snd a1) (snd a2)).
Defined.
Arguments nbits_map2 f [n].

Lemma nbits_map2_nth_bit : forall f n (a1 a2 : nbits n) m I,
  nth_bit m (nbits_map2 f a1 a2) I = f (nth_bit m a1 I) (nth_bit m a2 I).
Proof.
  introv. gen n. induction m; introv; destruct n; try nat_math.
  - repeat rewrite rewrite_O_nth_bit. reflexivity.
  - asserts I': (m < n)%nat. { nat_math. }
    repeat rewrite rewrite_S_nth_bit with (I' := I'). apply IHm.
Qed.

Definition nbits_or := nbits_map2 or.
Arguments nbits_or [n].

Lemma nbits_or_nth_bit : forall n (a1 a2 : nbits n) m I,
  nth_bit m (nbits_or a1 a2) I = nth_bit m a1 I || nth_bit m a2 I.
Proof. introv. apply nbits_map2_nth_bit. Qed.

Definition nbits_and := nbits_map2 and.
Arguments nbits_and [n].

Lemma nbits_and_nth_bit : forall n (a1 a2 : nbits n) m I,
  nth_bit m (nbits_and a1 a2) I = nth_bit m a1 I && nth_bit m a2 I.
Proof. introv. apply nbits_map2_nth_bit. Qed.

Lemma nbits_intersects_and : forall n (a1 a2 : nbits n),
  nbits_intersects a1 a2 <-> nbits_and a1 a2 <> nbits_init.
Proof.
  introv. iff I.
  - lets (m&I'&E1&E2): (rm I). intro E.
    lets E': (nbits_and_nth_bit a1 a2 I').
    rewrite E in E'. rewrite nbits_init_read with (I := I') in E'.
    rewrite E1, E2 in E'. false.
  - unfolds. apply not_not_inv. introv F. false I.
    apply nth_bit_eq. introv. rewrite nbits_and_nth_bit. rewrite nbits_init_read.
    rew_bool_eq. introv (E1&E2). false F. exists* m I0.
Qed.

