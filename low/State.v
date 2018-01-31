(** State.
  Provides a model for the C memory. **)

Set Implicit Arguments.
Require Export String.
Require Export RinternalsAux TLC.LibHeap Shared.
Require Import TLC.LibStream.

(** * A Model for the C Memory **)

(** The global state of the C memory. In particular, it maps SEXP
  pointers to their corresponding expressions. **)
Record memory := make_memory {
    state_heap_SExp :> heap nat SExpRec ;
    state_fresh_locations : stream nat ;
    state_fresh_locations_fresh : forall n,
      ~ indom state_heap_SExp (LibStream.nth n state_fresh_locations) ;
    state_fresh_locations_different : forall n1 n2,
      n1 <> n2 ->
      LibStream.nth n1 state_fresh_locations <> LibStream.nth n2 state_fresh_locations
  }.

(** Allocate a new cell and provide it an initial value **)
Definition alloc_memory_SExp_nat (S : memory) (e_ : SExpRec) : memory * nat.
  refine (let p := stream_head (state_fresh_locations S) in ({|
      state_heap_SExp := write S p e_ ;
      state_fresh_locations := stream_tail (state_fresh_locations S) |},
    p)).
  - introv I. rewrite stream_tail_nth in I. forwards~ I': @indom_write_inv I.
    + unfolds p. rewrite stream_head_nth. applys* state_fresh_locations_different.
    + applys~ state_fresh_locations_fresh I'.
  - introv D. repeat rewrite stream_tail_nth. applys* state_fresh_locations_different.
Defined.

Definition alloc_memory_SExp S e_ : memory * SExpRec_pointer :=
  let (S, p) := alloc_memory_SExp_nat S e_ in
  (S, Some p).

(** Writes a value in the state. Might return [None] if the cell is not already allocated. **)
Definition write_memory_SExp_nat (S : memory) (e : nat) (e_ : SExpRec) : option memory.
  refine (match read_option S e as r return r = _ -> _ with
          | None => fun _ => None
          | Some _ => fun Eq => Some {|
              state_heap_SExp := write S e e_ ;
              state_fresh_locations := state_fresh_locations S |}
          end eq_refl).
  - introv. apply not_indom_write.
    + introv E. applys state_fresh_locations_fresh. rewrite E.
      symmetry in Eq. applys~ read_option_indom Eq.
    + applys~ state_fresh_locations_fresh.
  - apply* state_fresh_locations_different.
Defined.

Definition write_memory_SExp (S : memory) (e : SExpRec_pointer) (e_ : SExpRec) :=
  match e with
  | None => None
  | Some e => write_memory_SExp_nat S e e_
  end.

Definition read_SExp_nat (S : memory) (e : nat) : option SExpRec :=
  read_option S e.

(** Reads a value in the state. **)
Definition read_SExp (S : memory) (e : SExpRec_pointer) :=
  match e with
  | None => None
  | Some e => read_SExp_nat S e
  end.


Lemma read_SExp_NULL : forall S,
  read_SExp S NULL = None.
Proof.
  introv. reflexivity.
Qed.

Lemma alloc_memory_SExp_nat_read_SExp : forall S S' e_ e,
  alloc_memory_SExp_nat S e_ = (S', e) ->
  read_SExp S' (Some e) = Some e_.
Proof. introv Eq. inverts Eq. do 2 unfolds. simpl. rewrite~ read_option_write_same. Qed.

Lemma alloc_memory_SExp_read_SExp : forall S S' e_ e,
  alloc_memory_SExp S e_ = (S', e) ->
  read_SExp S' e = Some e_.
Proof. introv Eq. inverts Eq. applys* alloc_memory_SExp_nat_read_SExp. Qed.

Lemma destruct_write_memory_SExp_nat_None : forall (S : memory) e e_,
  read_option S e = None ->
  write_memory_SExp_nat S e e_ = None.
Proof.
  introv E. unfolds.
  asserts R: (forall T P (x : option T) (f1 : None = x -> P None) (f2 : forall v, Some v = x -> _)
      (H : None = x),
    match x as r return r = x -> P r with
    | None => f1
    | Some v => fun E => f2 v E
    end eq_refl
    = match H in _ = r return P r with
      | eq_refl => f1 H
      end).
  + clear. introv. destruct~ H.
  + symmetry in E. lets R': (rm R) (read_option S e). erewrite (R' _ _ E). destruct~ E.
Qed.

Lemma destruct_write_memory_SExp_nat : forall (S : memory) e e_ v,
  read_option S e = Some v ->
  exists S',
    write_memory_SExp_nat S e e_ = Some S'
    /\ (S' : heap _ _) = write S e e_.
Proof.
  introv E. unfolds write_memory_SExp_nat.
  asserts R: (forall T T' (x : option T) (f1 : None = x -> T') (f2 : forall v, Some v = x -> T')
      v (H : Some v = x),
    match x as r return r = x -> T' with
    | None => f1
    | Some v => fun E => f2 v E
    end eq_refl
    = f2 v H).
  + clear. introv. destruct~ H.
  + symmetry in E. lets R': (rm R) (read_option S e). rewrite (R' _ _ _ E). clear.
    eexists. splits~.
Qed.

Lemma write_memory_SExp_nat_read_SExp_same : forall S S' e_ e,
  write_memory_SExp_nat S e e_ = Some S' ->
  read_SExp S' (Some e) = Some e_.
Proof.
  introv E. simpl. destruct (read_option S e) eqn: E'.
  + forwards (S2&E1&E2): destruct_write_memory_SExp_nat E'.
    rewrite E in E1. inverts E1. unfolds. rewrite E2. rewrite~ read_option_write_same.
  + forwards Eq: destruct_write_memory_SExp_nat_None E'. rewrite Eq in E. false*.
Qed.

Lemma write_memory_SExp_read_SExp_same : forall S S' e_ e,
  write_memory_SExp S e e_ = Some S' ->
  read_SExp S' e = Some e_.
Proof. introv E. destruct e; tryfalse. applys~ write_memory_SExp_nat_read_SExp_same E. Qed.

Lemma write_memory_SExp_nat_read_SExp : forall S S' e_ e e',
  write_memory_SExp_nat S e e_ = Some S' ->
  e <> e' ->
  read_SExp S' (Some e') = read_SExp S (Some e').
Proof.
  introv E D. simpl. destruct (read_option S e) eqn: E'.
  + forwards (S2&E1&E2): destruct_write_memory_SExp_nat E'.
    rewrite E in E1. inverts E1. unfolds. rewrite E2. rewrite~ read_option_write.
  + forwards Eq: destruct_write_memory_SExp_nat_None E'. rewrite Eq in E. false*.
Qed.

Lemma write_memory_SExp_read_SExp : forall S S' e_ e e',
  write_memory_SExp S e e_ = Some S' ->
  e <> e' ->
  read_SExp S' e' = read_SExp S e'.
Proof.
  introv E D. destruct e; tryfalse. destruct e'.
  + applys~ write_memory_SExp_nat_read_SExp E.
  + reflexivity.
Qed.

Lemma read_SExp_write_memory_SExp_nat : forall S e_ e'_ e,
  read_SExp S (Some e) = Some e_ ->
  exists S', write_memory_SExp_nat S e e'_ = Some S'.
Proof.
  introv E. simpl in E. forwards (S'&E1&E2): destruct_write_memory_SExp_nat E.
  exists S'. rewrite~ E1.
Qed.

Lemma read_SExp_write_memory_SExp : forall S e_ e'_ e,
  read_SExp S e = Some e_ ->
  exists S', write_memory_SExp S e e'_ = Some S'.
Proof. introv E. destruct e; tryfalse. applys~ read_SExp_write_memory_SExp_nat E. Qed.


(** * A Model for R’s Contexts **)

(** Contexts are defined in the file main/context.c of R source code. **)

Definition context_type := nbits 7.

Definition CTXT_TOPLEVEL := 0.
Definition CTXT_NEXT := 1.
Definition CTXT_BREAK := 2.
Definition CTXT_LOOP := 3.
Definition CTXT_FUNCTION := 4.
Definition CTXT_CCODE := 8.
Definition CTXT_RETURN := 12.
Definition CTXT_BROWSER := 16.
Definition CTXT_GENERIC := 20.
Definition CTXT_RESTART := 32.
Definition CTXT_BUILTIN := 64.

Definition Ctxt_TopLevel : context_type := @nat_to_nbits 7 CTXT_TOPLEVEL ltac:(nbits_ok).
Definition Ctxt_Next : context_type := @nat_to_nbits 7 CTXT_NEXT ltac:(nbits_ok).
Definition Ctxt_Break : context_type := @nat_to_nbits 7 CTXT_BREAK ltac:(nbits_ok).
Definition Ctxt_Loop : context_type := @nat_to_nbits 7 CTXT_LOOP ltac:(nbits_ok).
Definition Ctxt_Function : context_type := @nat_to_nbits 7 CTXT_FUNCTION ltac:(nbits_ok).
Definition Ctxt_CCode : context_type := @nat_to_nbits 7 CTXT_CCODE ltac:(nbits_ok).
Definition Ctxt_Return : context_type := @nat_to_nbits 7 CTXT_RETURN ltac:(nbits_ok).
Definition Ctxt_Browser : context_type := @nat_to_nbits 7 CTXT_BROWSER ltac:(nbits_ok).
Definition Ctxt_Generic : context_type := @nat_to_nbits 7 CTXT_GENERIC ltac:(nbits_ok).
Definition Ctxt_Restart : context_type := @nat_to_nbits 7 CTXT_RESTART ltac:(nbits_ok).
Definition Ctxt_Builtin : context_type := @nat_to_nbits 7 CTXT_BUILTIN ltac:(nbits_ok).

Definition empty_context_type := Ctxt_TopLevel.

Instance context_type_Comparable : Comparable context_type.
  typeclass.
Defined.

Instance context_type_Inhab : Inhab context_type.
  apply prove_Inhab. apply empty_context_type.
Defined.

Definition context_type_mask (t1 t2 : context_type) :=
  nbits_intersects t1 t2.

Definition context_type_merge (t1 t2 : context_type) :=
  nbits_or t1 t2.


(** Note: not all fields have been modeled. See the report or the
  original definition in the file include/Defn.h for more details. **)
(** The [cjmpbuf] field is here just a number, different for all
  context. The jumping process occurs by returning a special
  result (see Monads.v or the repport). **)
(** RCNTXT, *context **)
Inductive context := make_context {
    context_nextcontext : option context ;
    context_cjmpbuf : nat ;
    context_callflag : context_type ;
    context_promargs : SExpRec_pointer ;
    context_callfun : SExpRec_pointer ;
    context_sysparent : SExpRec_pointer ;
    context_call : SExpRec_pointer ;
    context_cloenv : SExpRec_pointer ;
    context_conexit : SExpRec_pointer ;
    context_returnValue : SExpRec_pointer ;
    context_jumptarget : option context ;
    context_jumpmask : context_type
  }.

Fixpoint context_rect' (P : context -> Type) HNoneNone HNoneSome HSomeNone HSomeSome c : P c :=
  match c with
  | make_context nextcontext cjmpbuf callflag promargs callfun sysparent call cloenv
      conexit returnValue jumptarget jumpmask =>
    match nextcontext, jumptarget with
    | None, None =>
      HNoneNone cjmpbuf callflag promargs callfun sysparent call cloenv conexit returnValue jumpmask
    | None, Some c' =>
      HNoneSome c' (context_rect' P HNoneNone HNoneSome HSomeNone HSomeSome c')
        cjmpbuf callflag promargs callfun sysparent call cloenv conexit returnValue jumpmask
    | Some c', None =>
      HSomeNone c' (context_rect' P HNoneNone HNoneSome HSomeNone HSomeSome c')
        cjmpbuf callflag promargs callfun sysparent call cloenv conexit returnValue jumpmask
    | Some c1, Some c2 =>
      HSomeSome c1 c2 (context_rect' P HNoneNone HNoneSome HSomeNone HSomeSome c1)
        (context_rect' P HNoneNone HNoneSome HSomeNone HSomeSome c2)
        cjmpbuf callflag promargs callfun sysparent call cloenv conexit returnValue jumpmask
    end
  end.

Definition context_ind' (P : context -> Prop) := context_rect' P.

Fixpoint context_rect_next_context (P : context -> Type) HNone HSome c : P c :=
  match c with
  | make_context nextcontext cjmpbuf callflag promargs callfun sysparent call cloenv
      conexit returnValue jumptarget jumpmask =>
    match nextcontext with
    | None =>
      HNone cjmpbuf callflag promargs callfun sysparent call cloenv conexit returnValue jumptarget jumpmask
    | Some c' =>
      HSome c' (context_rect_next_context P HNone HSome c')
        cjmpbuf callflag promargs callfun sysparent call cloenv conexit returnValue jumptarget jumpmask
    end
  end.

Definition context_ind_next_context (P : context -> Prop) := context_rect_next_context P.

Fixpoint context_rect_jumptarget (P : context -> Type) HNone HSome c : P c :=
  match c with
  | make_context nextcontext cjmpbuf callflag promargs callfun sysparent call cloenv
      conexit returnValue jumptarget jumpmask =>
    match jumptarget with
    | None =>
      HNone nextcontext cjmpbuf callflag promargs callfun sysparent call cloenv conexit returnValue jumpmask
    | Some c' =>
      HSome c' (context_rect_jumptarget P HNone HSome c')
       nextcontext cjmpbuf callflag promargs callfun sysparent call cloenv conexit returnValue jumpmask
    end
  end.

Definition context_ind_jumptarget (P : context -> Prop) := context_rect_jumptarget P.

Instance context_Comparable : Comparable context.
  applys make_comparable. intros c1.
  induction c1 using context_rect'; intros c2;
    induction c2 using context_rect'; prove_decidable_eq.
Defined.

Definition context_with_callflag context callflag := {|
     context_nextcontext := context_nextcontext context ;
     context_cjmpbuf := context_cjmpbuf context ;
     context_callflag := callflag ;
     context_promargs := context_promargs context ;
     context_callfun := context_callfun context ;
     context_sysparent := context_sysparent context ;
     context_call := context_call context ;
     context_cloenv := context_cloenv context ;
     context_conexit := context_conexit context ;
     context_returnValue := context_returnValue context ;
     context_jumptarget := context_jumptarget context ;
     context_jumpmask := context_jumpmask context
   |}.

Definition context_with_conexit context conexit := {|
     context_nextcontext := context_nextcontext context ;
     context_cjmpbuf := context_cjmpbuf context ;
     context_callflag := context_callflag context ;
     context_promargs := context_promargs context ;
     context_callfun := context_callfun context ;
     context_sysparent := context_sysparent context ;
     context_call := context_call context ;
     context_cloenv := context_cloenv context ;
     context_conexit := conexit ;
     context_returnValue := context_returnValue context ;
     context_jumptarget := context_jumptarget context ;
     context_jumpmask := context_jumpmask context
   |}.

Definition context_with_returnValue context returnValue := {|
     context_nextcontext := context_nextcontext context ;
     context_cjmpbuf := context_cjmpbuf context ;
     context_callflag := context_callflag context ;
     context_promargs := context_promargs context ;
     context_callfun := context_callfun context ;
     context_sysparent := context_sysparent context ;
     context_call := context_call context ;
     context_cloenv := context_cloenv context ;
     context_conexit := context_conexit context ;
     context_returnValue := returnValue ;
     context_jumptarget := context_jumptarget context ;
     context_jumpmask := context_jumpmask context
   |}.

Definition context_with_jumptarget context jumptarget := {|
     context_nextcontext := context_nextcontext context ;
     context_cjmpbuf := context_cjmpbuf context ;
     context_callflag := context_callflag context ;
     context_promargs := context_promargs context ;
     context_callfun := context_callfun context ;
     context_sysparent := context_sysparent context ;
     context_call := context_call context ;
     context_cloenv := context_cloenv context ;
     context_conexit := context_conexit context ;
     context_returnValue := context_returnValue context ;
     context_jumptarget := jumptarget ;
     context_jumpmask := context_jumpmask context
   |}.

Definition context_with_jumpmask context jumpmask := {|
     context_nextcontext := context_nextcontext context ;
     context_cjmpbuf := context_cjmpbuf context ;
     context_callflag := context_callflag context ;
     context_promargs := context_promargs context ;
     context_callfun := context_callfun context ;
     context_sysparent := context_sysparent context ;
     context_call := context_call context ;
     context_cloenv := context_cloenv context ;
     context_conexit := context_conexit context ;
     context_returnValue := context_returnValue context ;
     context_jumptarget := context_jumptarget context ;
     context_jumpmask := jumpmask
   |}.


(** * A Model for R’s Connections **)

(** Output and input can perform various side effects, as well as
  calling function that may not be marshalable.  To avoid any
  difficulties, we define indirections. **)

Inductive open_type :=
  | null_open
  .

Inductive close_type :=
  | null_close
  .

Inductive destroy_type :=
  | null_destroy
  .

Inductive print_type :=
  | null_print
  | stdout_print
  | stderr_print
  .

Inductive flush_type :=
  | null_flush
  | stdout_flush
  | stderr_flush
  .


(** The following definition corresponds to the type
  [Rconn]/[Rconnection] in the file include/R_ext/Connections.h]. **)

Inductive Rconnection := make_Rconnection {
    Rconnection_class : string ;
    Rconnection_description : string ;
    Rconnection_mode : string ;
    Rconnection_text : bool ;
    Rconnection_isopen : bool ;
    Rconnection_incomplete : bool ;
    Rconnection_canread : bool ;
    Rconnection_canwrite : bool ;
    Rconnection_canseek : bool ;
    Rconnection_blocking : bool ;
    Rconnection_isGzcon : bool ;
    Rconnection_open : open_type ;
    Rconnection_close : close_type ;
    Rconnection_destroy : destroy_type ;
    Rconnection_print : print_type (** Corresponds to [vfprintf], but simplified. **) ;
    Rconnection_fflush : flush_type ;

    (** We allows connections to store information to represent the
      external state of the connection.  For instance, for random
      values, it can be the stream of future values. **)
    Rconnection_type : Type ;
    Rconnection_state : Rconnection_type
  }.

Definition Rconnection_with_class c class := {|
    Rconnection_class := class ;
    Rconnection_description := Rconnection_description c ;
    Rconnection_mode := Rconnection_mode c ;
    Rconnection_text := Rconnection_text c ;
    Rconnection_isopen := Rconnection_isopen c ;
    Rconnection_incomplete := Rconnection_incomplete c ;
    Rconnection_canread := Rconnection_canread c ;
    Rconnection_canwrite := Rconnection_canwrite c ;
    Rconnection_canseek := Rconnection_canseek c ;
    Rconnection_blocking := Rconnection_blocking c ;
    Rconnection_isGzcon := Rconnection_isGzcon c ;
    Rconnection_open := Rconnection_open c ;
    Rconnection_close := Rconnection_close c ;
    Rconnection_destroy := Rconnection_destroy c ;
    Rconnection_print := Rconnection_print c ;
    Rconnection_fflush := Rconnection_fflush c ;
    Rconnection_state := Rconnection_state c
  |}.

Definition Rconnection_with_isopen c isopen := {|
    Rconnection_class := Rconnection_class c ;
    Rconnection_description := Rconnection_description c ;
    Rconnection_mode := Rconnection_mode c ;
    Rconnection_text := Rconnection_text c ;
    Rconnection_isopen := isopen ;
    Rconnection_incomplete := Rconnection_incomplete c ;
    Rconnection_canread := Rconnection_canread c ;
    Rconnection_canwrite := Rconnection_canwrite c ;
    Rconnection_canseek := Rconnection_canseek c ;
    Rconnection_blocking := Rconnection_blocking c ;
    Rconnection_isGzcon := Rconnection_isGzcon c ;
    Rconnection_open := Rconnection_open c ;
    Rconnection_close := Rconnection_close c ;
    Rconnection_destroy := Rconnection_destroy c ;
    Rconnection_print := Rconnection_print c ;
    Rconnection_fflush := Rconnection_fflush c ;
    Rconnection_state := Rconnection_state c
  |}.

Definition Rconnection_with_canread c canread := {|
    Rconnection_class := Rconnection_class c ;
    Rconnection_description := Rconnection_description c ;
    Rconnection_mode := Rconnection_mode c ;
    Rconnection_text := Rconnection_text c ;
    Rconnection_isopen := Rconnection_isopen c ;
    Rconnection_incomplete := Rconnection_incomplete c ;
    Rconnection_canread := canread ;
    Rconnection_canwrite := Rconnection_canwrite c ;
    Rconnection_canseek := Rconnection_canseek c ;
    Rconnection_blocking := Rconnection_blocking c ;
    Rconnection_isGzcon := Rconnection_isGzcon c ;
    Rconnection_open := Rconnection_open c ;
    Rconnection_close := Rconnection_close c ;
    Rconnection_destroy := Rconnection_destroy c ;
    Rconnection_print := Rconnection_print c ;
    Rconnection_fflush := Rconnection_fflush c ;
    Rconnection_state := Rconnection_state c
  |}.

Definition Rconnection_with_canwrite c canwrite := {|
    Rconnection_class := Rconnection_class c ;
    Rconnection_description := Rconnection_description c ;
    Rconnection_mode := Rconnection_mode c ;
    Rconnection_text := Rconnection_text c ;
    Rconnection_isopen := Rconnection_isopen c ;
    Rconnection_incomplete := Rconnection_incomplete c ;
    Rconnection_canread := Rconnection_canread c ;
    Rconnection_canwrite := canwrite ;
    Rconnection_canseek := Rconnection_canseek c ;
    Rconnection_blocking := Rconnection_blocking c ;
    Rconnection_isGzcon := Rconnection_isGzcon c ;
    Rconnection_open := Rconnection_open c ;
    Rconnection_close := Rconnection_close c ;
    Rconnection_destroy := Rconnection_destroy c ;
    Rconnection_print := Rconnection_print c ;
    Rconnection_fflush := Rconnection_fflush c ;
    Rconnection_state := Rconnection_state c
  |}.

Definition Rconnection_with_destroy c destroy := {|
    Rconnection_class := Rconnection_class c ;
    Rconnection_description := Rconnection_description c ;
    Rconnection_mode := Rconnection_mode c ;
    Rconnection_text := Rconnection_text c ;
    Rconnection_isopen := Rconnection_isopen c ;
    Rconnection_incomplete := Rconnection_incomplete c ;
    Rconnection_canread := Rconnection_canread c ;
    Rconnection_canwrite := Rconnection_canwrite c ;
    Rconnection_canseek := Rconnection_canseek c ;
    Rconnection_blocking := Rconnection_blocking c ;
    Rconnection_isGzcon := Rconnection_isGzcon c ;
    Rconnection_open := Rconnection_open c ;
    Rconnection_close := Rconnection_close c ;
    Rconnection_destroy := destroy ;
    Rconnection_print := Rconnection_print c ;
    Rconnection_fflush := Rconnection_fflush c ;
    Rconnection_state := Rconnection_state c
  |}.

Definition Rconnection_with_print c print := {|
    Rconnection_class := Rconnection_class c ;
    Rconnection_description := Rconnection_description c ;
    Rconnection_mode := Rconnection_mode c ;
    Rconnection_text := Rconnection_text c ;
    Rconnection_isopen := Rconnection_isopen c ;
    Rconnection_incomplete := Rconnection_incomplete c ;
    Rconnection_canread := Rconnection_canread c ;
    Rconnection_canwrite := Rconnection_canwrite c ;
    Rconnection_canseek := Rconnection_canseek c ;
    Rconnection_blocking := Rconnection_blocking c ;
    Rconnection_isGzcon := Rconnection_isGzcon c ;
    Rconnection_open := Rconnection_open c ;
    Rconnection_close := Rconnection_close c ;
    Rconnection_destroy := Rconnection_destroy c ;
    Rconnection_print := print ;
    Rconnection_fflush := Rconnection_fflush c ;
    Rconnection_state := Rconnection_state c
  |}.

Definition Rconnection_with_fflush c fflush := {|
    Rconnection_class := Rconnection_class c ;
    Rconnection_description := Rconnection_description c ;
    Rconnection_mode := Rconnection_mode c ;
    Rconnection_text := Rconnection_text c ;
    Rconnection_isopen := Rconnection_isopen c ;
    Rconnection_incomplete := Rconnection_incomplete c ;
    Rconnection_canread := Rconnection_canread c ;
    Rconnection_canwrite := Rconnection_canwrite c ;
    Rconnection_canseek := Rconnection_canseek c ;
    Rconnection_blocking := Rconnection_blocking c ;
    Rconnection_isGzcon := Rconnection_isGzcon c ;
    Rconnection_open := Rconnection_open c ;
    Rconnection_close := Rconnection_close c ;
    Rconnection_destroy := Rconnection_destroy c ;
    Rconnection_print := Rconnection_print c ;
    Rconnection_fflush := fflush ;
    Rconnection_state := Rconnection_state c
  |}.

Definition Rconnection_with_external_state c A (state : A) := {|
    Rconnection_class := Rconnection_class c ;
    Rconnection_description := Rconnection_description c ;
    Rconnection_mode := Rconnection_mode c ;
    Rconnection_text := Rconnection_text c ;
    Rconnection_isopen := Rconnection_isopen c ;
    Rconnection_incomplete := Rconnection_incomplete c ;
    Rconnection_canread := Rconnection_canread c ;
    Rconnection_canwrite := Rconnection_canwrite c ;
    Rconnection_canseek := Rconnection_canseek c ;
    Rconnection_blocking := Rconnection_blocking c ;
    Rconnection_isGzcon := Rconnection_isGzcon c ;
    Rconnection_open := Rconnection_open c ;
    Rconnection_close := Rconnection_close c ;
    Rconnection_destroy := Rconnection_destroy c ;
    Rconnection_print := Rconnection_print c ;
    Rconnection_fflush := Rconnection_fflush c ;
    Rconnection_state := state
  |}.


(** We now resolve the indirection. **)
Definition interpret_open t (c : Rconnection) : option (Rconnection * bool) :=
  match t with
  | null_open => None
  end.

Definition interpret_close t (c : Rconnection) : option Rconnection :=
  match t with
  | null_close => Some (Rconnection_with_isopen c false)
  end.

Definition interpret_destroy t (c : Rconnection) : option Rconnection :=
  match t with
  | null_destroy => Some c
  end.

Parameters run_stdout_print run_stderr_print : Rconnection -> string -> option Rconnection.

Definition interpret_print t (c : Rconnection) str : option Rconnection :=
  match t with
  | null_print => None
  | stdout_print => run_stdout_print c str
  | stderr_print => run_stderr_print c str
  end.

Parameters run_stdout_flush run_stderr_flush : Rconnection -> option Rconnection.

Definition interpret_flush t (c : Rconnection) : option Rconnection :=
  match t with
  | null_flush => None
  | stdout_flush => run_stdout_flush c
  | stderr_flush => run_stderr_flush c
  end.

(** The following functions are translations from functions of main/connections.c. **)

Definition init_con description mode := {|
    Rconnection_class := "" ;
    Rconnection_description := description ;
    Rconnection_mode := mode ;
    Rconnection_isopen := false ;
    Rconnection_incomplete := false ;
    Rconnection_blocking := false ;
    Rconnection_isGzcon := false ;
    Rconnection_canread := true ;
    Rconnection_canwrite := true ;
    Rconnection_canseek := false ;
    Rconnection_text := true ;
    Rconnection_open := null_open ;
    Rconnection_close := null_close ;
    Rconnection_destroy := null_destroy ;
    Rconnection_print := null_print ;
    Rconnection_fflush := null_flush ;
    Rconnection_state := tt
  |}.

Definition newterminal description mode :=
  let c := init_con description mode in
  let c := Rconnection_with_isopen c true in
  let c := Rconnection_with_canread c (decide (mode = "r"%string)) in
  let c := Rconnection_with_canwrite c (decide (mode = "w"%string)) in
  c.


(** * A Model for R’s State **)

Record state := make_state {
    state_memory :> memory ;
    state_context : context ;
    R_ExitContext : option context ;
    R_SymbolTable : SExpRec_pointer ;
    R_ReturnedValue : SExpRec_pointer ;
    R_Connections : list Rconnection (** Simply [Connections] in main/connections.c. **) ;
    R_OutputCon : nat
  }.

Definition R_GlobalContext := state_context.

Definition state_with_memory S m := {|
    state_memory := m ;
    state_context := state_context S ;
    R_ExitContext := R_ExitContext S ;
    R_SymbolTable := R_SymbolTable S ;
    R_ReturnedValue := R_ReturnedValue S ;
    R_Connections := R_Connections S ;
    R_OutputCon := R_OutputCon S
  |}.

Definition state_with_context S c := {|
    state_memory := state_memory S ;
    state_context := c ;
    R_ExitContext := R_ExitContext S ;
    R_SymbolTable := R_SymbolTable S ;
    R_ReturnedValue := R_ReturnedValue S ;
    R_Connections := R_Connections S ;
    R_OutputCon := R_OutputCon S
  |}.

Definition update_R_ExitContext S c := {|
    state_memory := state_memory S ;
    state_context := state_context S ;
    R_ExitContext := c ;
    R_SymbolTable := R_SymbolTable S ;
    R_ReturnedValue := R_ReturnedValue S ;
    R_Connections := R_Connections S ;
    R_OutputCon := R_OutputCon S
  |}.

Definition update_R_SymbolTable S p := {|
    state_memory := state_memory S ;
    state_context := state_context S ;
    R_ExitContext := R_ExitContext S ;
    R_SymbolTable := p ;
    R_ReturnedValue := R_ReturnedValue S ;
    R_Connections := R_Connections S ;
    R_OutputCon := R_OutputCon S
  |}.

Definition update_R_ReturnedValue S p := {|
    state_memory := state_memory S ;
    state_context := state_context S ;
    R_ExitContext := R_ExitContext S ;
    R_SymbolTable := R_SymbolTable S ;
    R_ReturnedValue := p ;
    R_Connections := R_Connections S ;
    R_OutputCon := R_OutputCon S
  |}.

Definition update_R_Connections S cs := {|
    state_memory := state_memory S ;
    state_context := state_context S ;
    R_ExitContext := R_ExitContext S ;
    R_SymbolTable := R_SymbolTable S ;
    R_ReturnedValue := R_ReturnedValue S ;
    R_Connections := cs ;
    R_OutputCon := R_OutputCon S
  |}.

Definition update_R_OutputCon S outputCon := {|
    state_memory := state_memory S ;
    state_context := state_context S ;
    R_ExitContext := R_ExitContext S ;
    R_SymbolTable := R_SymbolTable S ;
    R_ReturnedValue := R_ReturnedValue S ;
    R_Connections := R_Connections S ;
    R_OutputCon := outputCon
  |}.


(** Wrapping up with the functions defined in the previous section. **)

Definition alloc_SExp (S : state) e_ :=
  let (m, e) := alloc_memory_SExp S e_ in
  (state_with_memory S m, e).

Definition write_SExp (S : state) e e_ :=
  match write_memory_SExp S e e_ with
  | Some m => Some (state_with_memory S m)
  | None => None
  end.


(** * Initial Memory **)

CoFixpoint all_locations n : stream nat :=
  n ::: (all_locations (1 + n)).

Lemma all_locations_nth : forall n m,
  nth m (all_locations n) = m + n.
Proof.
  introv. gen n. induction m; introv.
  - reflexivity.
  - simpl. rewrite~ IHm.
Qed.

Definition empty_memory : memory.
  refine {|
      state_heap_SExp := empty ;
      state_fresh_locations := all_locations 0
    |}.
  - introv. apply~ @not_indom_empty. typeclass.
  - introv D. repeat rewrite all_locations_nth. math.
Defined.


(** * Instances **)

Instance memory_Inhab : Inhab memory :=
  prove_Inhab empty_memory.

Instance context_Inhab : Inhab context.
  apply prove_Inhab. constructors; typeclass || apply arbitrary.
Qed.

Instance state_Rconnection : Inhab Rconnection.
  apply prove_Inhab. apply (newterminal "dummy" "???").
Qed.

Instance state_Inhab : Inhab state.
  apply prove_Inhab. constructors; typeclass || apply arbitrary.
Qed.

