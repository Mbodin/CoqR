(** InvariantsTactics.
  Defines tactics to manipulate the invariants defined in Invariants. **)

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
Require Import InvariantsAux.

(** * Simplifying tactics **)

(** ** Simplifying lists **)

Ltac is_fully_computed l :=
  lazymatch l with
  | nil => constr:(true)
  | _ :: ?l =>
    let r := is_fully_computed l in r
  | _ => constr:(false)
  end.

(** Checks whether [x] is syntactically in the list [l]. **)
Ltac compute_is_in x l :=
  lazymatch l with
  | nil => constr:(false)
  | x :: _ => constr:(true)
  | _ :: ?l =>
    let r := compute_is_in x l in r
  end.

(** This produces a list equal to [l1 \n l2] in Ltac. **)
Ltac compute_list_inter l1 l2 :=
  lazymatch l2 with
  | nil => l2
  | ?a :: ?l =>
    let isi := compute_is_in a l1 in
    let r := compute_list_inter l1 l in
    match isi with
    | true => constr:(a :: r)
    | false => r
    end
  end.

(** The following tactic computes any occurence of [l1 \n l2] in the goal. **)
Ltac simpl_list_inter :=
  let solve_eq :=
    solve [ clear; simpl;
    repeat
      (rewrite filter_cons;
       let C := fresh "C" in
       cases_if as C; fold_bool; rew_refl in C;
       try solve [ false~ | repeat inverts C as C; false~ ];
       fequals; clear C) ] in
  repeat match goal with
  | |- context [ ?l1 \n ?l2 ] =>
    let l := compute_list_inter l1 l2 in
    asserts_rewrite (l1 \n l2 = l); [solve_eq|]
  | H : context [ ?l1 \n ?l2 ] |- _ =>
    let l := compute_list_inter l1 l2 in
    asserts_rewrite (l1 \n l2 = l) in H; [solve_eq|]
  end.

(** This produces a list equal to [l1 \u l2] in Ltac. **)
Ltac compute_list_union l1 l2 :=
  let rec inl2butnotinl1 l2 :=
    match l2 with
    | nil => l2
    | ?a :: ?l =>
      let isi := compute_is_in a l1 in
      let r := inl2butnotinl1 l in
      match isi with
      | true => r
      | false => constr:(a :: r)
      end
    end in
  let rec add_to_the_end l1 :=
    lazymatch l1 with
    | nil =>
      let r := inl2butnotinl1 l2 in
      r
    | ?a :: ?l =>
      let r := add_to_the_end l in
      constr:(a :: r)
    end in
  add_to_the_end l1.

(** The following tactic fully compute any occurence of [l1 \u l2],
  with both [l1] and [l2] already fully computed, in the goal and
  the context. **)
Ltac simpl_list_union :=
  let solve_eq :=
    solve [ clear; simpl;
    repeat rewrite app_cons; rewrite app_nil_l;
    repeat
      (rewrite filter_cons;
       let C := fresh "C" in
       cases_if as C; fold_bool; rew_refl in C; try (false C; substs; Mem_solve);
       fequals; clear C) ] in
  repeat match goal with
  | |- context [ ?l1 \u ?l2 ] =>
    let l := compute_list_union l1 l2 in
    asserts_rewrite (l1 \u l2 = l); [solve_eq|]
  | H : context [ ?l1 \u ?l2 ] |- _ =>
    let l := compute_list_union l1 l2 in
    asserts_rewrite (l1 \u l2 = l) in H; [solve_eq|]
  end.


(** ** Recognising a fully computed [SExpType] **)

Ltac SExpType_fully_computed t :=
  lazymatch t with
  | NilSxp => constr:(true)
  | SymSxp => constr:(true)
  | ListSxp => constr:(true)
  | CloSxp => constr:(true)
  | EnvSxp => constr:(true)
  | PromSxp => constr:(true)
  | LangSxp => constr:(true)
  | SpecialSxp => constr:(true)
  | BuiltinSxp => constr:(true)
  | CharSxp => constr:(true)
  | LglSxp => constr:(true)
  | IntSxp => constr:(true)
  | RealSxp => constr:(true)
  | CplxSxp => constr:(true)
  | StrSxp => constr:(true)
  | DotSxp => constr:(true)
  | AnySxp => constr:(true)
  | VecSxp => constr:(true)
  | ExprSxp => constr:(true)
  | BcodeSxp => constr:(true)
  | ExtptrSxp => constr:(true)
  | WeakrefSxp => constr:(true)
  | RawSxp => constr:(true)
  | S4Sxp => constr:(true)
  | NewSxp => constr:(true)
  | FreeSxp => constr:(true)
  | FunSxp => constr:(true)
  | _ => constr:(false)
  end.


(** ** Simplifying the context **)

(** Fails if [x] and [y] are not syntactically the same. **)
Ltac syntactically_the_same x y :=
  lazymatch x with
  | y => idtac
  end.

(** Fails if [x] and [y] are syntactically the same. **)
Ltac syntactically_different x y :=
  lazymatch x with
  | y => fail
  | _ => idtac
  end.

(** Simplifies the contact. In particular:
  - it merges different instances of [may_have_types] and [list_type] abo9ut the same pointer
    into the same predicate;
  - it folds some definitions that may have been unfolded by other tactics;
  - it unfolds some definitions that are more useful unfolded;
  - it simplifies lists such as [l1 \u l2] and [l1 \n l2], fully computing them.
  Note that a more powerful version [simplify_context] of this tactic is defined in a section below. **)
Ltac simplify_context_base :=
  repeat match goal with
  | T : may_have_types ?S nil ?p |- _ =>
    false; applys~ may_have_types_nil T
  | T1 : may_have_types ?S ?l1 ?p,
    T2 : may_have_types ?S ?l2 ?p |- _ =>
    let T3 := fresh2 T1 T2 in
    forwards T3: may_have_types_merge (rm T1) (rm T2);
    rename T3 into T1
  | T1 : list_type ?S ?l1_t ?l1_car ?l1_tag ?p,
    T2 : list_type ?S ?l2_t ?l2_car ?l2_tag ?p |- _ =>
    let T3 := fresh2 T1 T2 in
    forwards T3: list_type_merge (rm T1) (rm T2);
    rename T3 into T1
  | T1 : list_type_such_that ?Pheader ?Pcar ?Ptag ?S ?l1_t ?l1_car ?l1_tag ?p,
    T2 : list_type_such_that ?Pheader ?Pcar ?Ptag ?S ?l2_t ?l2_car ?l2_tag ?p |- _ =>
    let T3 := fresh2 T1 T2 in
    forwards T3: list_type_merge (rm T1) (rm T2);
    rename T3 into T1
  | E : ?p1 = ?p2 |- _ =>
    lazymatch p1 with
    | _ _ => fail
    | _ =>
      lazymatch p2 with
      | _ _ => fail
      | _ => inverts E
      end
    end
  end;
  try fold (list_head_such_that (fun _ => True) (fun _ => True)) in *;
  try fold list_head_such_that in *;
  try fold list_head in *;
  try fold list_type in *;
  try unfolds all_storable_SExpTypes;
  try unfolds all_SExpTypes;
  repeat match goal with
  | |- context [ list_type_such_that (safe_header safe_pointer ?S) (safe_pointer ?S) (safe_pointer ?S) ?S ] =>
    fold (list_type_safe S)
  | H : context [ list_type_such_that (safe_header safe_pointer ?S) (safe_pointer ?S) (safe_pointer ?S) ?S ] |- _ =>
    fold (list_type_safe S) in H
  | |- context [ list_head_such_that (safe_header safe_pointer ?S) (safe_pointer ?S) (safe_pointer ?S) ?S ] =>
    fold (list_head_safe S)
  | H : context [ list_head_such_that (safe_header safe_pointer ?S) (safe_pointer ?S) (safe_pointer ?S) ?S ] |- _ =>
    fold (list_head_safe S) in H
  end;
  simpl_list_inter;
  simpl_list_union.


(** ** Automatic rewriting **)

(** As this file defines a lot of tactics defining new names, it is
  best to avoid explicitely having to use these new hypotheses by
  their names.  The following tactics try to automatically rewrite
  what they can. **)

(** Apply any rewriting it can. **)
Ltac self_rewrite :=
  repeat match goal with
  | H : _ = _ |- _ => rewrite~ H
  end.

(** Apply any rewriting to a given hypothesis it can. **)
Ltac self_rewrite_in P :=
  repeat match goal with
  | H : _ = _ |- _ =>
    syntactically_different H P;
    rewrite~ H in P
  end.

(** Only rewrite using hypothesis referencing a given [x]. **)
Ltac self_rewrite_about x :=
  repeat match goal with
  | H : context [ x ] |- _ => rewrite~ H
  end.

(** Same than above, but in a given hypothesis. **)
Ltac self_rewrite_about_in x P :=
  repeat match goal with
  | H : context [ x ] |- _ =>
    syntactically_different H P;
    rewrite~ H in P
  end.

Tactic Notation "self_rewrite" :=
  self_rewrite.

Tactic Notation "self_rewrite" "in" hyp(P) :=
  self_rewrite_in P.

Tactic Notation "self_rewrite" "about" constr(x) :=
  self_rewrite_about x.

Tactic Notation "self_rewrite" "about" constr(x) "in" hyp(P) :=
  self_rewrite_about_in x P.


(** ** Prevent infinite recursion **)

(** The prevent useless inifite loops in tactics, we mark their
  arguments are already seen using the following definition. **)
Definition already_seen A (a : A) := True.

(** The following tactic marks its argument as already seen in the
  context. It fails if already present. **)
Ltac mark_as_seen a :=
  lazymatch goal with
  | A : already_seen a |- _ => fail
  | _ =>
    let a' := fresh1 a in
    let A := fresh "AS" a' in
    asserts A: (already_seen a); [ constructors* |]
  end.

(** Remove the mark for a given argument. **)
Ltac remove_already_seen a :=
  try lazymatch goal with
  | A : already_seen a |- _ => clear A
  end.

(** Remove all marks. **)
Ltac remove_all_already_seen :=
  repeat lazymatch goal with
  | A : already_seen _ |- _ => clear A
  end.


(** ** Case analysis on lists **)

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
  | ?x \in [?y] =>
    let T' := fresh1 T in
    asserts T': (x = y); [ eapply BagInSingle_list; apply T |];
    clear T; rename T' into T
  | ?x \in (?y :: ?l) =>
    apply BagIn_cons in T;
    let T' := fresh1 T in
    lets [T'|T']: (rm T);
    [ try rename T' into T
    | (rename T' into T ; explode_list T) || explode_list T' ]
  | may_have_types ?S nil ?x =>
    false~ may_have_types_nil T
  | may_have_types ?S (?t :: ?l) ?x =>
    apply may_have_types_cons in T;
    let T' := fresh1 T in
    lets [T'|T']: (rm T);
    [ try rename T' into T
    | (rename T' into T ; explode_list T) || explode_list T' ]
  | Mem ?x nil =>
    rewrite Mem_nil_eq in T; false~ T
  | Mem ?x (?y :: ?l) =>
    rewrite Mem_cons_eq in T;
    let T' := fresh1 T in
    lets [T'|T']: (rm T);
    [ try rename T' into T
    | (rename T' into T ; explode_list T) || explode_list T' ]
  | mem ?x nil =>
    rewrite mem_nil in T; false~ T
  | mem ?x (?y :: ?l) =>
    rewrite mem_cons in T;
    rew_refl in T;
    let T' := fresh1 T in
    lets [T'|T']: (rm T);
    [ try rename T' into T
    | (rename T' into T ; explode_list T) || explode_list T' ]
  | In ?x nil =>
    false~ in_nil T
  | In ?x (?y :: ?l) =>
    let T' := fresh1 T in
    lets [T'|T']: in_inv (rm T);
    [ try rename T' into T
    | (rename T' into T ; explode_list T) || explode_list T' ]
  end.


(** ** Clearing trivial hypotheses **)

(** This tactic removes useless hypotheses. **)
Ltac clear_trivial :=
  repeat lazymatch goal with
  | T : True |- _ => clear T
  | E : ?x = ?x |- _ => clear E
  | H1 : ?P, H2 : ?P |- _ => clear H2
  | I : ?x \in [?y] |- _ => explode_list I
  end;
  repeat match goal with
  | u : unit |- _ => clear u
  end.


(** ** Miscellaneous **)

(** [look_for_equality] takes a pointer [p], a tactic [recognize] returning
  either [true] or [false], and a continuation.  If called, the continuation
  is assured to be called on a [p'] such that [recognize p'] and on an
  hypothesis of the form [p = p']. **)
Ltac look_for_equality p recognize cont :=
  let r := recognize p in
  lazymatch r with
  | true => cont p (eq_refl p)
  | _ =>
    match goal with
    | E : p = ?p' |- _ =>
      let r := recognize p' in
      match r with
      | true => cont p' E
      end
    | E : ?p' = p |- _ =>
      let r := recognize p' in
      match r with
      | true => cont p' (eq_sym E)
      end
    | _ =>
      let p_e := eval simpl in p in
      let r := recognize p_e in
      match r with
      | true =>
        let p' := fresh1 p in
        let E := fresh "E" p' in
        asserts E: (p = p_e); [ reflexivity | cont p_e E ]
      end
    end
  end.

(** Similar than [look_for_equality], but instead of providing a tactic
  stating whether this term is acceptable, we provide directly a term.
  This tactic will look for equalities between [p] and [term].  The
  continuation only expects the equality [p = term]. **)
Ltac look_for_equality_term p term cont :=
  lazymatch p with
  | term => cont (eq_refl p)
  | _ =>
    lazymatch goal with
    | E : p = term |- _ => cont E
    | E : term = p |- _ => cont (eq_sym E)
    | _ =>
      (** We check whether by chance, [term] and [p] are convertible. **)
      let p' := fresh1 p in
      let E := fresh "E" p' in
      asserts E: (p = term); [ reflexivity | cont E ]
    end
  end.

(** Checks whether, in the current context, the given term [term] is indeed of
  the form [Some term'].  It then calls the continuation [cont] with arguments
  [term'], as well as an equiality of the form [term = Some term']. **)
Ltac should_be_some term cont :=
  look_for_equality term ltac:(fun o =>
    lazymatch o with
    | Some _ => constr:(true)
    | _ => constr:(false)
    end) ltac:(fun someterm' E =>
      lazymatch someterm' with
      | Some ?term' => cont term' E
      end).


(** * Getting some properties **)

(** Each of the following [get_property arguments continuation] tactic will try to build
  a property of the form [property arguments], then call the continuation with it.
  These tactics will try not to rebuilt it if already built. **)

(** ** [safe_globals] **)

Ltac get_safe_globals S globals cont :=
  lazymatch goal with
  | H : safe_globals S globals |- _ => cont H
  end.

Ltac get_safe_globals_no_S globals cont :=
  lazymatch goal with
  | H : safe_globals _ globals |- _ => cont H
  end.


(** ** [safe_state] **)

Ltac get_safe_state S cont :=
  lazymatch goal with
  | H : safe_state S |- _ => cont H
  | H : result_prop ?P_success _ _ (result_success S _) |- _ =>
    let S' := fresh1 S in
    let R := fresh "OK" S' in
    asserts R: (safe_state S);
    [ let I := fresh "Impl" in
      asserts I: (forall S r, P_success S r -> safe_state S);
      [ solve [ autos* ] | solve [ applys* I H ] ]
    | cont R ]
  | H : result_prop _ ?P_error _ (result_error S _) |- _ =>
    let S' := fresh1 S in
    let R := fresh "OK" S' in
    asserts R: (safe_state S);
    [ let I := fresh "Impl" in
      asserts I: (forall S, P_error S -> safe_state S);
      [ solve [ autos* ] | solve [ applys* I H ] ]
    | cont R ]
  | H : result_prop _ _ ?P_longjump (result_longjump S _ _) |- _ =>
    let S' := fresh1 S in
    let R := fresh "OK" S' in
    asserts R: (safe_state S);
    [ let I := fresh "Impl" in
      asserts I: (forall S n c, P_longjump S n c -> safe_state S);
      [ solve [ autos* ] | solve [ applys* I H ] ]
    | cont R ]
  end.


(** ** [bound] **)

Ltac get_bound S p cont :=
  lazymatch goal with
  | B : bound S p |- _ => cont B
  | B : bound_such_that S _ p |- _ =>
    let B' := fresh B in
    forwards B': bound_such_that_bound B;
    cont B'
  | OKp : safe_pointer_gen _ S p |- _ =>
    let p' := fresh1 p in
    let B := fresh "B" p' in
    forwards B: pointer_bound OKp;
    cont B
  | OKp : safe_pointer S p |- _ =>
    rewrite safe_pointer_rewrite in OKp;
    let p' := fresh1 p in
    let B := fresh "B" p' in
    forwards B: pointer_bound OKp;
    cont B
  | R : read_SExp (state_memory S) p = Some _ |- _ =>
    let p' := fresh1 p in
    let B := fresh "B" p' in
    forwards B: read_bound R;
    cont B
  | A : alloc_SExp _ p = (S, _) |- _ =>
    let p' := fresh1 p in
    let B := fresh "B" p' in
    forwards B: alloc_SExp_bound A;
    cont B
  end.

Ltac get_bound_no_S p cont :=
  lazymatch goal with
  | B : bound _ p |- _ => cont B
  | B : bound_such_that _ _ p |- _ =>
    let B' := fresh B in
    forwards B': bound_such_that_bound B;
    cont B'
  | OKp : safe_pointer_gen _ _ p |- _ =>
    let p' := fresh1 p in
    let B := fresh "B" p' in
    forwards B: pointer_bound OKp;
    cont B
  | OKp : safe_pointer _ p |- _ =>
    rewrite safe_pointer_rewrite in OKp;
    let p' := fresh1 p in
    let B := fresh "B" p' in
    forwards B: pointer_bound OKp;
    cont B
  | R : read_SExp _ p = Some _ |- _ =>
    let p' := fresh1 p in
    let B := fresh "B" p' in
    forwards B: read_bound R;
    cont B
  | A : alloc_SExp _ p = (_, _) |- _ =>
    let p' := fresh1 p in
    let B := fresh "B" p' in
    forwards B: alloc_SExp_bound A;
    cont B
  end.


(** ** [list_type] **)

(** There are several variants of [list_type] defined in this file.
  These tactics will look for one of them. **)

Ltac get_list_type S p cont :=
  lazymatch goal with
  | L : list_type_safe S _ _ _ p |- _ => cont L
  | L : list_type_such_that _ _ _ S _ _ _ p |- _ => cont L
  | L : list_type S _ _ _ p |- _ => cont L
  | _ =>
    match p with
    | R_SymbolTable S =>
      get_safe_state S ltac:(fun OKS =>
        cont (safe_SymbolTable OKS))
    end
  end.

Ltac get_list_type_no_S p cont :=
  lazymatch goal with
  | L : list_type_safe _ _ _ _ p |- _ => cont L
  | L : list_type_such_that _ _ _ _ _ _ _ p |- _ => cont L
  | L : list_type _ _ _ _ p |- _ => cont L
  | _ =>
    match p with
    | R_SymbolTable ?S =>
      get_safe_state S ltac:(fun OKS =>
        cont (safe_SymbolTable OKS))
    end
  end.

Ltac get_list_head S p_ cont :=
  lazymatch goal with
  | L : list_head_safe S _ _ _ p_ |- _ => cont L
  | L : list_head_such_that _ _ _ S _ _ _ p_ |- _ => cont L
  | L : list_head S _ _ _ p_ |- _ => cont L
  end.

Ltac get_list_head_no_S p_ cont :=
  lazymatch goal with
  | L : list_head_safe _ _ _ _ p_ |- _ => cont L
  | L : list_head_such_that _ _ _ _ _ _ _ p_ |- _ => cont L
  | L : list_head _ _ _ _ p_ |- _ => cont L
  end.


(** ** [may_have_types] **)

(** These tactics will try to build a property of the form [may_have_types S l p]
  for a given [p].
  The list [l] will either already have been computed by a previously called tactic,
  or will be inferred from what the goal can offer. **)

Ltac get_may_have_types S p cont :=
  lazymatch goal with
  | M : may_have_types S _ p |- _ => cont M
  | _ =>
    first [
        (** We try looking for lists. **)
        get_list_type S p ltac:(fun L =>
          let p' := fresh1 p in
          let M := fresh "M" p' in
          forwards M: list_type_may_have_types L;
          simpl_list_union;
          cont M)
      | (** Otherwise, we look for less specific hints. **)
        lazymatch goal with
        | E : read_SExp (state_memory S) p = Some ?p_,
          T : type (get_SxpInfo ?p_) = ?t |- _ =>
          let p' := fresh1 p in
          let M := fresh "M" p' in
          forwards M: read_SExp_may_have_types_read_exact E T;
          cont M
        | E : read_SExp (state_memory S) p = Some ?p_,
          T : type (get_SxpInfo ?p_) \in ?l |- _ =>
          let p' := fresh1 p in
          let M := fresh "M" p' in
          forwards M: read_SExp_may_have_types_read E T;
          cont M
        | E : read_SExp (state_memory S) p = Some ?p_ |- _ =>
          get_list_head S p_ ltac:(fun L =>
            let p' := fresh1 p in
            let T := fresh "T" p' in
            forwards T: list_head_may_have_types L;
            let M := fresh "M" p' in
            forwards M: read_SExp_may_have_types_read E T;
            cont M)
        | E : read_SExp (state_memory S) p = Some ?p_ |- _ =>
          let t := fresh "t" in
          evar (t : SExpType);
          let T := fresh "E" t in
          asserts T: (type p_ = t);
          [ substs; simpl; unfolds t; reflexivity
          | unfolds t; clear t;
            match type of T with
            | _ = ?t =>
              let tf := SExpType_fully_computed t in
              match tf with
              | true =>
                let p' := fresh1 p in
                let M := fresh "M" p' in
                forwards M: read_SExp_may_have_types_read_exact E T;
                cont M
              end
            end ]
        | |- _ =>
          first [
              lazymatch p with
              | read_globals ?globals R_NilValue =>
                get_safe_globals S globals ltac:(fun OKg =>
                  let T := fresh "Tnil" in
                  forwards T: R_NilValue_may_have_types OKg;
                  cont T)
              end
            | (** This case uses [bound_may_have_types], which produces an imprecise result.
                It thus important for it to always be the last resort case. **)
              lazymatch goal with
              | B : bound_such_that S _ p |- _ =>
                let p' := fresh1 p in
                let M := fresh "M" p' in
                forwards M: bound_may_have_types (rm B);
                [ applys~ bound_such_that_weaken B | cont M ]
              | |- _ =>
                get_bound S p ltac:(fun B =>
                  let p' := fresh1 p in
                  let M := fresh "M" p' in
                  forwards M: bound_may_have_types (rm B);
                  cont M)
              end ]
        end ]
  end.

Ltac get_may_have_types_no_S p cont :=
  lazymatch goal with
  | M : may_have_types _ _ p |- _ => cont M
  | _ =>
    first [
        (** We try looking for lists. **)
        get_list_type_no_S p ltac:(fun L =>
          let p' := fresh1 p in
          let M := fresh "M" p' in
          forwards M: list_type_may_have_types L;
          simpl_list_union;
          cont M)
      | (** Otherwise, we look for less specific hints. **)
        lazymatch goal with
        | E : read_SExp _ p = Some ?p_,
          T : type (get_SxpInfo ?p_) = ?t |- _ =>
          let p' := fresh1 p in
          let M := fresh "M" p' in
          forwards M: read_SExp_may_have_types_read_exact E T;
          cont M
        | E : read_SExp _ p = Some ?p_,
          T : type (get_SxpInfo ?p_) \in ?l |- _ =>
          let p' := fresh1 p in
          let M := fresh "M" p' in
          forwards M: read_SExp_may_have_types_read E T;
          cont M
        | E : read_SExp _ p = Some ?p_ |- _ =>
          get_list_head_no_S p_ ltac:(fun L =>
            let p' := fresh1 p in
            let T := fresh "T" p' in
            forwards T: list_head_may_have_types L;
            let M := fresh "M" p' in
            forwards M: read_SExp_may_have_types_read E T;
            cont M)
        | E : read_SExp _ p = Some ?p_ |- _ =>
          let t := fresh "t" in
          evar (t : SExpType);
          let T := fresh "E" t in
          asserts T: (type p_ = t);
          [ substs; simpl; unfolds t; reflexivity
          | unfolds t; clear t;
            match type of T with
            | _ = ?t =>
              let tf := SExpType_fully_computed t in
              match tf with
              | true =>
                let p' := fresh1 p in
                let M := fresh "M" p' in
                forwards M: read_SExp_may_have_types_read_exact E T;
                cont M
              end
            end ]
        | |- _ =>
          first [
              lazymatch p with
              | read_globals ?globals R_NilValue =>
                get_safe_globals_no_S globals ltac:(fun OKg =>
                  let T := fresh "Tnil" in
                  forwards T: R_NilValue_may_have_types OKg;
                  cont T)
              end
            | (** This case uses [bound_may_have_types], which produces an imprecise result.
                It thus important for it to always be the last resort case. **)
              lazymatch goal with
              | B : bound_such_that _ _ p |- _ =>
                let p' := fresh1 p in
                let M := fresh "M" p' in
                forwards M: bound_may_have_types (rm B);
                [ applys~ bound_such_that_weaken B | cont M ]
              | |- _ =>
                get_bound_no_S p ltac:(fun B =>
                  let p' := fresh1 p in
                  let M := fresh "M" p' in
                  forwards M: bound_may_have_types (rm B);
                  cont M)
              end ]
        end ]
  end.


(** ** Basic tactics to disprove some simple null pointer exceptions **)

(** Note that a more general tactic [prove_no_null_pointer_exceptions]
  is defined in a section below. **)

Ltac prove_no_null_pointer_exceptions_globals A :=
  solve [ inverts~ A ].

Ltac prove_no_null_pointer_exceptions_entry_point A :=
  solve [ inverts~ A ].

Ltac prove_no_null_pointer_exceptions_path_simple A :=
  solve [ inverts A as A; inverts~ A ].

Ltac prove_no_null_pointer_exceptions_path_suffix_simple A :=
  solve [ inverts A; substs; false* ].


(** ** A basic tactic to prove [safe_pointer] **)

(** This tactic tries to prove [safe_pointer], without attempting anything
  that may loop if not handled properly.
  Note that a more general tactic [get_safe_pointer] is defined in a section
  below. **)

Ltac get_safe_pointer_base S p cont :=
  let move_along_entry_point_case M :=
    get_safe_state S ltac:(fun OKS =>
      let p' := fresh1 p in
      let R := fresh "OK" p' in
      asserts R: (safe_pointer S p);
      [ applys* safe_entry_points OKS M;
        solve [
          applys~ no_null_pointer_entry_point OKS M;
          let A := fresh "A" in
          introv A;
          prove_no_null_pointer_exceptions_entry_point A ]
      | cont R ]) in
  lazymatch goal with
  | H : safe_pointer S p |- _ => cont H
  | H : safe_pointer_gen safe_pointer S p |- _ =>
    rewrite <- safe_pointer_rewrite in H; cont H
  | M : move_along_entry_point _ S = Some p |- _ =>
    move_along_entry_point_case M
  | _ =>
    first [
        let p' := fresh1 p in
        let OKp := fresh "OK" p' in
        match p with
        | read_globals ?globals ?g =>
          get_safe_globals S globals ltac:(fun OKg =>
            asserts OKp: (safe_pointer S p);
            [ applys~ globals_not_NULL_safe OKg;
              applys~ globals_not_NULL OKg;
              let A := fresh "A" in
              introv A;
              prove_no_null_pointer_exceptions_globals A
            | cont OKp ])
        | attrib ?p' =>
          asserts OKp: (safe_pointer S p);
          [ get_safe_pointer_base S p' ltac:(fun OKp' =>
              applys~ safe_attrib OKp')
          | cont OKp ]
        | R_SymbolTable S =>
          try (
            let L := fresh "L" in
            get_safe_state S ltac:(fun OKS =>
              forwards L: safe_SymbolTable OKS));
          let M := fresh "M" in
          asserts M: (move_along_entry_point ESymbolTable S = Some p);
          [ reflexivity |];
          move_along_entry_point_case M
        | R_ReturnedValue S =>
          let M := fresh "M" in
          asserts M: (move_along_entry_point EReturnedValue S = Some p);
          [ reflexivity |];
          move_along_entry_point_case M
        end
     | get_may_have_types S p ltac:(fun M =>
         match type of M with
         | may_have_types S ([NilSxp]) p =>
           let p' := fresh1 p in
           let OKp := fresh "OK" p' in
           asserts OKp: (safe_pointer S p);
           [ get_safe_state S ltac:(fun OKS =>
               applys* may_have_types_NilSxp_safe_pointer OKS M)
           | cont OKp ]
         end)
     | lazymatch goal with
       | L : list_type_safe S ([ListSxp]) ?l_car ?l_tag p |- _ =>
         let p' := fresh1 p in
         let OKp := fresh "OK" p' in
         asserts OKp: (safe_pointer S p);
         [ get_safe_state S ltac:(fun OKS =>
                                    applys* list_type_safe_safe_pointer OKS L;
                                    solve_incl)
         | cont OKp ]
       | H : safe_pointer_gen _ S p |- _ => cont H
       end ]
  end.

(** Tactics to simplify [safe_pointer]. **)
Ltac rewrite_safe_pointer :=
  repeat first [
      rewrite safe_pointer_rewrite_paco2
    | rewrite safe_pointer_rewrite_upaco2
    | rewrite <- safe_pointer_rewrite ].

Ltac rewrite_safe_pointer_in H :=
  repeat first [
      rewrite safe_pointer_rewrite_paco2 in H
    | rewrite safe_pointer_rewrite_upaco2 in H
    | rewrite <- safe_pointer_rewrite in H ].


(** ** [safe_header] **)

Ltac get_safe_header S h cont :=
  lazymatch goal with
  | OKh : safe_header S h |- _ => cont OKh
  | _ =>
    first [
        let h' := fresh1 h in
        let OK := fresh "OK" h' in
        let ah := eval simpl in (attrib h) in
        asserts OK: (safe_header S h);
        [ constructors;
          [ (** safe_attrib **)
            get_safe_pointer_base S ah ltac:(fun OKh => apply OKh)
          | (** attrib_list **)
            (get_list_type S ah ltac:(fun L =>
              applys~ list_type_weaken L; try intros; solve_incl))
            || (get_may_have_types S ah ltac:(fun M =>
                  apply~ list_type_nil; applys~ may_have_types_weaken M; solve_incl))
          ]
        | cont OK ]
      | lazymatch goal with
        | OKh : safe_header_gen _ S h |- _ => cont OKh
        end ]
  end.


(** ** [safe_SExpRec] **)

Ltac get_safe_SExpRec S e_ cont :=
  lazymatch goal with
  | H : safe_SExpRec S e_ |- _ => cont H
  | H : safe_SExpRec_gen safe_pointer S e_ |- _ => cont H
  | H : safe_SExpRec_gen (upaco2 safe_pointer_gen bot2) S e_ |- _ =>
    try rewrite safe_pointer_rewrite_upaco2 in H;
    cont H
  | P : read_SExp (state_memory S) ?e = Some e_ |- _ =>
    get_safe_pointer_base S e ltac:(fun H =>
      let e_' := fresh1 e_ in
      let R := fresh "OK" e_' in
      asserts R: (safe_SExpRec_gen safe_pointer S e_);
      [ solve [
            applys* safe_SExpRec_read H P; pfold; autos~
          | let H' := fresh1 H in
            lets H': H;
            rewrite safe_pointer_rewrite in H';
            forwards* R: safe_SExpRec_read H' P; pfold; autos~ ]
      | cont R ])
  | _ =>
    first [
        let e_' := fresh1 e_ in
        let R := fresh "OK" e_' in
        asserts R: (safe_SExpRec S e_);
        [ substs; simpl; constructors~;
          [ (** SExpType_corresponds_to_datatype **)
            simpl; constructors~;
            lazymatch goal with
            | |- may_have_types ?S ?l ?p =>
              get_may_have_types S p ltac:(fun M =>
                applys~ may_have_types_weaken M; solve_incl)
            | |- list_type S _ _ _ ?p =>
              get_list_type S p ltac:(fun L =>
                applys~ list_type_weaken L; (solve_incl || (repeat rewrite safe_pointer_rewrite; autos*)))
            | |- forall a, Mem a _ -> may_have_types S ?l a =>
              let M := fresh "M" in
              substs; simpl; introv M; repeat inverts M as M;
              lazymatch goal with
              | |- may_have_types ?S ?l ?a =>
                get_may_have_types S a ltac:(fun M =>
                  applys~ may_have_types_weaken M; solve_incl)
              end
            | |- safe_pointer S ?p =>
              get_safe_pointer_base S p ltac:(fun OKp => apply p)
            | |- _ => solve [ constructors* ]
            end
          | (** SExpRec_header **)
            get_safe_header S (get_SExpRecHeader e_) ltac:(fun OKh => apply OKh) ]
        | cont R ]
      | lazymatch goal with
        | H : safe_SExpRec_gen _ S e_ |- _ => cont H
        end ]
  end.

(** Ensures that there exists an hypothesis of the form
  [safe_SExpRec S p_] or [safe_pointer_gen _ S p_] in the goal. **)
Ltac generate_safe_SExpRec S p_ :=
  lazymatch goal with
  | OKp_ : safe_SExpRec S p_ |- _ => idtac
  | OKp_ : safe_SExpRec_gen _ S p_ |- _ => idtac
  | _ =>
    get_safe_SExpRec S p_ ltac:(fun OKp_ =>
      let p_' := fresh1 p_ in
      let OKp_' := fresh "OK" p_' in
      lets OKp_': (rm OKp_))
  end.

(** The following tactic is similar to [get_safe_SExpRec], but ensures
  that the given proposition will be of the form [safe_SExpRec_gen _ S _]
  and not [safe_SExpRec]. **)
Ltac get_safe_SExpRec_unfolded S e_ cont :=
  get_safe_SExpRec S e_ ltac:(fun OKe_ =>
    lazymatch type of OKe_ with
    | safe_SExpRec _ _ =>
      let OKe_' := fresh1 OKe_ in
      forwards OKe_': paco2_unfold safe_pointer_gen_mon OKe_;
      cont OKe_'
    | safe_SExpRec_gen _ _ _ => cont OKe_
    end).
  

(** ** [move_along_path_step] **)

(** The continuation expects a pointer [p0] and an equality of the
  form [move_along_path_step step S p0 = Some p].  This tactic thus
  looks for a pointer in the backward direction. **)
Ltac get_move_along_path_step S p cont :=
  lazymatch goal with
  | M : move_along_path_step _ S ?p0 = Some p |- _ => cont p0 M
  | R : read_SExp (state_memory S) ?p0 = Some ?p0_ |- _ =>
    (** We consider an allocated potential pointer [p0].  We now inspect whether
      the object [p0_] contains [p] in one of its projections. **)
    let look_for_projection step term L :=
      look_for_equality_term p term ltac:(fun E =>
        let p' := fresh1 p in
        let E' := fresh "M" p' in
        asserts E': (move_along_path_step step S p0 = Some p);
        [ unfold move_along_path_step;
          rewrite R; try reflexivity;
          repeat rewrite_first L; try reflexivity;
          (rewrite E || (simpl; try simpl in E; rewrite E)); try reflexivity;
          repeat rewrite_first L;
          reflexivity
        | cont p0 E' ]) in
    first [
        look_for_projection Sattrib (attrib (get_SExpRecHeader p0_)) >>
      | should_be_some (get_NonVector p0_) ltac:(fun p0_' Ep0_ =>
          first [
              should_be_some (get_symSxp (NonVector_SExpRec_data p0_')) ltac:(fun p0_sym Ep0_sym =>
                first [
                    look_for_projection (SNonVectorSym Ssym_pname) (sym_pname p0_sym) >> Ep0_ Ep0_sym
                  | look_for_projection (SNonVectorSym Ssym_value) (sym_value p0_sym) >> Ep0_ Ep0_sym
                  | look_for_projection (SNonVectorSym Ssym_internal) (sym_internal p0_sym) >> Ep0_ Ep0_sym
                  ])
            | should_be_some (get_listSxp (NonVector_SExpRec_data p0_')) ltac:(fun p0_list Ep0_list =>
                first [
                    look_for_projection (SNonVectorList Slist_carval) (list_carval p0_list) >> Ep0_ Ep0_list
                  | look_for_projection (SNonVectorList Slist_cdrval) (list_cdrval p0_list) >> Ep0_ Ep0_list
                  | look_for_projection (SNonVectorList Slist_tagval) (list_tagval p0_list) >> Ep0_ Ep0_list
                  ])
            | should_be_some (get_envSxp (NonVector_SExpRec_data p0_')) ltac:(fun p0_env Ep0_env =>
                first [
                    look_for_projection (SNonVectorEnv Senv_frame) (env_frame p0_env) >> Ep0_ Ep0_env
                  | look_for_projection (SNonVectorEnv Senv_enclos) (env_enclos p0_env) >> Ep0_ Ep0_env
                  ])
            | should_be_some (get_cloSxp (NonVector_SExpRec_data p0_')) ltac:(fun p0_clo Ep0_clo =>
                first [
                    look_for_projection (SNonVectorClo Sclo_formals) (clo_formals p0_clo) >> Ep0_ Ep0_clo
                  | look_for_projection (SNonVectorClo Sclo_body) (clo_body p0_clo) >> Ep0_ Ep0_clo
                  | look_for_projection (SNonVectorClo Sclo_env) (clo_env p0_clo) >> Ep0_ Ep0_clo
                  ])
            | should_be_some (get_promSxp (NonVector_SExpRec_data p0_')) ltac:(fun p0_prom Ep0_prom =>
                first [
                    look_for_projection (SNonVectorProm Sprom_value) (prom_value p0_prom) >> Ep0_ Ep0_prom
                  | look_for_projection (SNonVectorProm Sprom_expr) (prom_expr p0_prom) >> Ep0_ Ep0_prom
                  | look_for_projection (SNonVectorProm Sprom_env) (prom_env p0_prom) >> Ep0_ Ep0_prom
                  ])
            ])
      | should_be_some (get_VectorPointer p0_) ltac:(fun p0_' Ep0_ =>
          let v0 :=
            eval simpl in (ArrayList.to_list (VecSxp_data (Vector_SExpRec_vecsxp p0_'))) in
          let rec t n l :=
            match l with
            | ?p' :: ?l' =>
              (look_for_projection (SVectorPointer n) p' >> Ep0_ nth_option_zero nth_option_cons)
              || t (1 + n) l'
            end in
          t 0 v0)
      ]
  end.


(** ** [move_along_path] **)

(** The continuation expects an equality of the form
  [move_along_path path S = Some p]. **)
Ltac get_move_along_path S p cont :=
  lazymatch goal with
  | M : move_along_path _ S = Some p |- _ => cont M
  | MP : move_along_path_from _ S ?e = Some p,
    ME : move_along_entry_point _ S = Some ?e |- _ =>
    let p' := fresh1 p in
    let M := fresh "M" p' in
    forwards M: make_move_along_path ME MP;
    cont M
  end.


(** ** [safe_pointer] **)

(** In addition to [get_safe_pointer_base], this tactic tries to look for
  other pointers whose pointed object possesses fields that point to the
  current object: thanks to the fact that pointer safety also applies to
  the pointed pointers, we can get the safety of the new pointer using
  such a link.
  This tactic avoids looping. **)
Ltac get_safe_pointer S p cont :=
  match goal with
  | _ => get_safe_pointer_base S p cont
  | _ =>
    get_safe_state S ltac:(fun OKS =>
      get_move_along_path S p ltac:(fun M =>
        let p' := fresh1 p in
        let OKp := fresh "OK" p' in
        asserts OKp: (safe_pointer S p);
        [ applys* safe_pointer_along_path OKS M;
          solve [
              pfold; autos~
            | applys~ no_null_pointer_along_path OKS M;
              try solve [ pfold; autos~ ];
              let A := fresh "A" in
              introv A;
              prove_no_null_pointer_exceptions_path_simple A ]
        | cont OKp ]))
  | _ =>
    get_move_along_path_step S p ltac:(fun p0 M =>
      mark_as_seen p0;
      get_safe_pointer S p0 ltac:(fun OKp0 =>
        let next OKp0 :=
          let p' := fresh1 p in
          let OKp := fresh "OK" p' in
          asserts OKp: (safe_pointer S p);
          [ applys* safe_pointer_along_path_step OKp0 M;
            solve [
                pfold; autos~
              | applys~ no_null_pointer_along_path_step OKp0 M;
                try solve [ pfold; autos~ ];
                let A := fresh "A" in
                introv A;
                prove_no_null_pointer_exceptions_path_suffix_simple A ]
          | remove_already_seen p0;
            cont OKp ] in
        next OKp0
        || (let OKp0' := fresh1 OKp0 in
            lets OKp0': OKp0;
            rewrite safe_pointer_rewrite in OKp0';
            next OKp0')))
  | OKp0 : safe_pointer S ?p0,
    M : move_along_path_from _ S ?p0 = Some p |- _ =>
    let p' := fresh1 p in
    let OKp := fresh "OK" p' in
    asserts OKp: (safe_pointer S p);
    [ applys* safe_pointer_along_path_from OKp0 M;
      solve [
          pfold; autos~
        | applys~ no_null_pointer_along_path_from OKp0 M;
          try solve [ pfold; autos~ ];
          let I := fresh "I" in
          let A := fresh "A" in
          introv I A; repeat inverts I as I;
          prove_no_null_pointer_exceptions_path_suffix_simple A ]
    | cont OKp ]
  end.

(** Ensures that there exists an hypothesis of the form
  [safe_pointer S p] or [safe_pointer_gen _ S p] in the goal. **)
Ltac generate_safe_pointer S p :=
  lazymatch goal with
  | OKp : safe_pointer S p |- _ => idtac
  | OKp : safe_pointer_gen _ S p |- _ => idtac
  | _ =>
    get_safe_pointer S p ltac:(fun OKp =>
      let p' := fresh1 p in
      let OKp' := fresh "OK" p' in
      lets OKp': (rm OKp))
  end.

(** The following tactic is similar to [get_safe_pointer], but ensures
  that the given proposition will be of the form [safe_pointer_gen _ S _]
  and not [safe_pointer]. **)
Ltac get_safe_pointer_unfolded S p cont :=
  get_safe_pointer S p ltac:(fun OKp =>
    lazymatch type of OKp with
    | safe_pointer _ _ =>
      let OKp' := fresh1 OKp in
      forwards OKp': paco2_unfold safe_pointer_gen_mon OKp;
      cont OKp'
    | safe_pointer_gen _ _ _ => cont OKp
    end).

Ltac get_safe_pointer_no_S p cont :=
  match goal with
  | S : state |- _ =>
    get_safe_pointer S p cont
  end.


(** * Unfolding tactics **)

(** ** Getting object shapes **)

(** Removes useless hypotheses of the form [type p_ = _] or [type p_ \in _].
  This tactic may solve the goal if some of these hypotheses are inconsistant. **)
Ltac clear_useless_type_eq :=
  repeat match goal with
  | T : type (get_SxpInfo ?p_) \in [?t] |- _ => explode_list T
  | T1 : type (get_SxpInfo ?p_) = ?t,
    T2 : type (get_SxpInfo ?p_) = ?t |- _ => clear T2
  | T1 : type (get_SxpInfo ?p_) = ?t1,
    T2 : type (get_SxpInfo ?p_) = ?t2 |- _ =>
    solve [ rewrite T2 in T1; inverts T1 ]
  | T1 : type (get_SxpInfo ?p_) = ?t,
    T2 : type (get_SxpInfo ?p_) \in ?l |- _ =>
    rewrite T1 in T2;
    let isi := compute_is_in t l in
    lazymatch isi with
    | true => clear T2
    | false =>
      try solve [ false; repeat inverts T2 as T2 ]
    end
  end.

(** Generates an hypothesis of the form [type p_ = t] or [type p_ \in l]
  in the goal when possible. **)
Ltac put_type_in_context p_ :=
  match goal with
  | T : type (get_SxpInfo p_) = ?t |- _ => idtac
  | T : type (get_SxpInfo p_) \in _ |- _ => idtac
  | R : read_SExp (state_memory ?S) ?p = Some p_ |- _ =>
    get_may_have_types S p ltac:(fun M =>
      let p_' := fresh1 p_ in
      let T := fresh "T" p_' in
      forwards~ T: may_have_types_read_SExp M R)
  end; clear_useless_type_eq; simplify_context_base.

(** Extracts relevant information for [p_] from an hypothesis
  of the form [safe_SExpRec]. The [explode] arguments tells the
  tactics whether exploding the type into all its possibilities
  is wanted. **)
Ltac force_unfold_shape explode S p_ :=
  let invert_type OKp_ :=
    put_type_in_context p_;
    let inverts_explode t :=
      lazymatch explode with
      | true => inverts~ OKp_; t
      | false =>
         ((inverts~ OKp_; t; [idtac]) || solve [ inverts~ OKp_; t ])
      end in
    let solve_T T := solve [ simpls; rewrite T in *; false~ | inverts~ T ] in
    lazymatch goal with
    | T : type (get_SxpInfo p_) = ?t |- _ =>
      inverts_explode ltac:(try solve_T T)
    | T : type (get_SxpInfo p_) \in ?l |- _ =>
      let solve_in := applys BagInIncl T; solve_incl in
      first [
          (** Direct approach **)
          inverts_explode ltac:(try solve [
            lazymatch l with
            | _ _ => idtac
            | _ => unfold l in T
            end;
            explode_list T;
            solve_T T ])
        (** Lemmae-based approach **)
        | let header := fresh "header" in
          let car := fresh "car" in
          let cdr := fresh "cdr" in
          let tag := fresh "tag" in
          let p_' := fresh1 p_ in
          let E := fresh "E" p_' in
          let Tcar := fresh "T" car in
          let Tcdr := fresh "T" cdr in
          let Ttag := fresh "T" tag in
          forwards (header&car&cdr&tag&E&Tcar&Tcdr&Ttag): safe_SExpRec_type_ListSxp_struct OKp_;
          [ solve_in | inverts E ]
        | let header := fresh "header" in
          let offset := fresh "offset" in
          let p_' := fresh1 p_ in
          let E := fresh "E" p_' in
          let OKoffset := fresh "OK" offset in
          forwards (header&offset&E&OKoffset): safe_SExpRec_type_PrimSxp_struct OKp_;
          [ solve_in | inverts E ]
        | let header := fresh "header" in
          let array := fresh "array" in
          let p_' := fresh1 p_ in
          let E := fresh "E" p_' in
          let F := fresh "F" array in
          forwards (header&array&E&F): safe_SExpRec_type_VectorPointer OKp_;
          [ solve_in | inverts E ]
        ]
    end in
  lazymatch goal with
  | OKp_ : safe_SExpRec_type _ S (type (get_SxpInfo p_)) p_ |- _ =>
    invert_type OKp_
  | _ =>
    get_safe_SExpRec_unfolded S p_ ltac:(fun OKp_ =>
      let OKp_' := fresh1 OKp_ in
      forwards~ OKp_': SExpType_corresponds_to_datatype OKp_;
      invert_type OKp_')
  end.

(** [unfold_shape true S p_] generates an equality of the form [p_ = SExpRec_* _],
  generating as many subgoal as being needed. [unfold_shape false S p_] generates
  such an equality only if it only generates one subgoal or less. **)
Ltac unfold_shape explode S p_ :=
  lazymatch goal with
  | H : p_ = SExpRec_NonVector _ |- _ => idtac
  | H : p_ = SExpRec_VectorChar _ |- _ => idtac
  | H : p_ = SExpRec_VectorInteger _ |- _ => idtac
  | H : p_ = SExpRec_VectorComplex _ |- _ => idtac
  | H : p_ = SExpRec_VectorReal _ |- _ => idtac
  | H : p_ = SExpRec_VectorPointer _ |- _ => idtac
  | _ => force_unfold_shape explode S p_
  end.

(** This tactic tries to make [read_SExp] expressions appear in the context. **)
Ltac unfold_may_hide_read_SExp :=
  repeat match goal with
  | E : move_along_path_from ?l _ _ = _ |- _ =>
    let OKl := is_fully_computed l in
    match OKl with
    | true => unfold move_along_path_from in E; rew_list in E; simpl in E
    end
  | E : move_along_path_step _ _ _ = _ |- _ =>
    unfold move_along_path_step in E
  end.

(** This tactic is very similar to [unfold_shape], but it takes a pointer [p]
  instead of an object [p_]. **)
Ltac unfold_shape_pointer explode S p :=
  let aftermath R :=
    try lazymatch type of R with
    | read_SExp _ _ = Some ?p_ =>
      repeat lazymatch goal with
      | T : may_have_types S (_ :: _ :: _) p |- _ => clear T
      | T : type (get_SxpInfo p_) \in (_ :: _ :: _) |- _ => clear T
      end;
      try lazymatch goal with
      | T : may_have_types S _ p |- _ => idtac
      | T : type (get_SxpInfo p_) = ?t |- _ =>
        let p' := fresh1 p in
        let T' := fresh "T" p' in
        forwards T': read_SExp_may_have_types_read_exact R T
      | T : ?t = type (get_SxpInfo p_) |- _ =>
        let p' := fresh1 p in
        let T' := fresh "T" p' in
        forwards T': read_SExp_may_have_types_read_exact R (eq_sym T)
      end
    end in
  lazymatch goal with
  | R : read_SExp (state_memory S) p = Some ?p_ |- _ =>
    unfold_shape explode S p_;
    aftermath R
  | |- _ =>
    let p' := fresh1 p in
    let p_ := fresh p' "_" in
    let R := fresh "E" p_ in
    unfold_may_hide_read_SExp;
    destruct (read_SExp (state_memory S) p) as [p_|] eqn: R;
    [ unfold_shape explode S p_;
      aftermath R
    | false~;
      try get_safe_pointer_unfolded S p ltac:(fun OKp =>
        let E := fresh R in
        forwards (p_&E): bound_read OKp;
        rewrite E in R; inverts~ R);
      lazymatch explode with
      | true => idtac
      end ]
  end.

Ltac unfold_shape_pointer_explode := unfold_shape_pointer true.
Ltac unfold_shape_pointer_one := unfold_shape_pointer false.


(** ** Dealing with [read_SExp] **)

(** This tactic tries to rewrite [read_SExp] expressions into an object using the context.
  It can be called after [unfold_may_hide_read_SExp] to potentially rewrite more expressions. **)
Ltac rewrite_read_SExp :=
  repeat match goal with
  | |- context [ read_SExp (state_memory ?S) ?e ] =>
    let infer_from_eq E e_ :=
      try get_safe_pointer_unfolded S e ltac:(fun OKp =>
        let e_' := fresh1 e_ in
        let OKe_ := fresh "OK" e_' in
        forwards OKe_: safe_SExpRec_read OKp E) in
    let bound_such_that_prop T :=
      let e' := fresh1 e in
      let e_ := fresh e' "_" in
      let Ee_ := fresh "E" e_ in
      let T' := fresh1 T in
      let Pe_ := fresh T' e_ in
      lets (e_&Ee_&Pe_): (rm T);
      try rewrite Ee_ in *;
      infer_from_eq Ee_ e_ in
    lazymatch goal with
    | E : read_SExp (state_memory S) e = _ |- _ => rewrite E
    | T : may_have_types S ?l e |- _ => bound_such_that_prop T
    | B : bound_such_that S ?P e |- _ => bound_such_that_prop B
    | B : bound S e |- _ => bound_such_that_prop B
    | _ =>
      rewrite read_SExp_NULL
      || (get_may_have_types S e ltac:(bound_such_that_prop))
      || (get_safe_pointer_unfolded S e ltac:(fun OKe =>
            bound_such_that_prop (pointer_bound OKe)))
    end;
    try unfold_shape_pointer_one S e
  end; clear_trivial.

(** Tries to rewrite the expression [write_SExp S p p_] into something of the form
  [Some ?S'] everywhere in the context. **)
Ltac define_write_SExp S p p_ :=
  lazymatch goal with
  | E : write_SExp S p p_ = Some ?S' |- _ =>
    try rewrite E;
    try rewrite E in *
  | E : read_SExp (state_memory S) p = Some _ |- _ =>
    let S' := fresh1 S in
    let ES' := fresh "E" S' in
    lets (S'&ES'): read_write_SExp_Some p_ E;
    try rewrite E; (* This forces the instantiation of [E] in the goal first. *)
    try rewrite E in *
  | _ =>
    let S' := fresh1 S in
    let ES' := fresh "E" S' in
    destruct (write_SExp S p p_) as [S'|] eqn:ES';
    [ solve [
          false;
          match goal with
          | A : alloc_SExp _ _ = (S, p) |- _ =>
            applys alloc_write_SExp_not_None A ES';
            solve [ false~ ]
          | E : read_SExp (state_memory S) p = Some _ |- _ =>
            let R := fresh "R" in
            rewrites >> write_read_SExp_None (rm ES') in E;
            inverts E; solve [ false~ ]
          end
        | autos~; simpls* ]
    | try rewrite ES';
      try rewrite ES' in *;
      try assumption ]
  end.


(** * Dealing with pointer exceptions **)

(** Deals with goals of the form [~ no_null_pointer_exceptions_*]. **)
Ltac prove_no_null_pointer_exceptions :=
  lazymatch goal with
  | |- ~ _ =>
    let A := fresh "A" in
    introv A; inverts~ A; prove_no_null_pointer_exceptions
  | |- forall_ s \in ?path, ~ _ =>
    let I := fresh "I" in
    introv I;
    repeat inverts I as I;
    prove_no_null_pointer_exceptions
  | |- False =>
    repeat match goal with
    | A : null_pointer_exceptions_path ?p |- _ =>
      inverts A
    end;
    match goal with
    | A : null_pointer_exceptions_entry_point ?e |- _ =>
      prove_no_null_pointer_exceptions_entry_point A
    | A : null_pointer_exceptions_suffix ?path |- _ =>
      solve [
        inverts~ A;
        match goal with
        | N : ~ null_pointer_exceptions_suffix ?l |- _ =>
          apply N; constructors~
        | E : move_along_path_from path ?S ?p_ = _ |- _ =>
          unfold_shape_pointer_explode S p_;
          solve [ inverts E; false~ ]
        end ]
    | A : null_pointer_exceptions_globals ?g |- _ =>
      prove_no_null_pointer_exceptions_globals A
    end
  end.


(** * Some tactics about locations **)

(** ** Proving that locations are not [NULL] **)

Lemma noteq_sym : forall A (x y : A), x <> y -> y <> x.
Proof. autos*. Qed.

(** Deals with goals of the form [p <> NULL]. **)
Ltac prove_not_NULL :=
  let aux p :=
    match goal with
    | R : read_SExp _ p = Some ?p' |- _ =>
      intro_subst;
      rewrite read_SExp_NULL in R; solve [ inverts~ R ]
    | B : bound ?S p |- _ =>
      let p' := fresh1 p in
      let p_ := fresh p' "_" in
      let R := fresh "R" in
      lets (p_&R&_): B;
      intro_subst;
      rewrite read_SExp_NULL in R; solve [ inverts~ R ]
    | B : bound_such_that ?S _ p |- _ =>
      let p' := fresh1 p in
      let p_ := fresh p' "_" in
      let R := fresh "R" in
      lets (p_&R&_): B;
      intro_subst;
      rewrite read_SExp_NULL in R; solve [ inverts~ R ]
    | T : may_have_types ?S _ p |- _ =>
      let p' := fresh1 p in
      let p_ := fresh p' "_" in
      let R := fresh "R" in
      lets (p_&R&_): T;
      intro_subst;
      rewrite read_SExp_NULL in R; solve [ inverts~ R ]
    | M : move_along_path_step _ ?S ?p0 = Some p |- _ =>
      get_safe_pointer S p0 ltac:(fun OKp0 =>
        let OKp0' := fresh1 OKp0 in
        lets OKp0': OKp0;
        rewrite safe_pointer_rewrite in OKp0';
        applys~ no_null_pointer_along_path_step OKp0' M;
        try solve [ pfold; autos~ ];
        clear OKp0';
        prove_no_null_pointer_exceptions)
    | M : move_along_path _ ?S = Some p |- _ =>
      get_safe_state S ltac:(fun OKS =>
        applys~ no_null_pointer_along_path OKS M;
        try solve [ pfold; autos~ ];
        prove_no_null_pointer_exceptions)
    | M : move_along_entry_point _ ?S = Some p |- _ =>
      get_safe_state S ltac:(fun OKS =>
        applys~ no_null_pointer_entry_point OKS M;
        prove_no_null_pointer_exceptions)
    | M : move_along_path_from _ ?S ?p0 = Some p |- _ =>
      get_safe_pointer S p0 ltac:(fun OKp0 =>
        applys~ no_null_pointer_along_path_from OKp0 M;
        try solve [ pfold; autos~ ];
        prove_no_null_pointer_exceptions)
    | _ =>
      solve [
          apply* globals_not_NULL; prove_no_null_pointer_exceptions
        | get_safe_pointer_no_S p ltac:(fun OKp =>
            applys~ safe_pointer_not_NULL OKp)
        | let E := fresh "E" in introv E; substs;
          match goal with
          | E : move_along_path_step _ _ NULL = Some _ |- _ =>
            rewrite move_along_path_step_NULL in E; inverts~ E
          | E : move_along_path_from _ _ NULL = Some _ |- _ =>
            rewrite move_along_path_from_NULL in E;
            [ substs~; discriminate
            | inverts~ E ]
          | E : read_SExp _ NULL = Some _ |- _ =>
            rewrite read_SExp_NULL in E; inverts~ E
          end ]
    end in
  lazymatch goal with
  | |- ?p <> NULL => aux p
  | |- ?p = NULL -> False => aux p
  | |- NULL <> ?p => apply noteq_sym; aux p
  | |- NULL = ?p -> False => apply noteq_sym; aux p
  end.


(** ** Proving locations different **)

(** Generates a proof of [Nth n p l] if possible. **)
Ltac prove_Nth p l :=
  lazymatch l with
  | p :: ?l' => constr:(Nth_here l' p)
  | ?x :: ?l' =>
    let N := prove_Nth p l' in
    constr:(Nth_next x N)
  end.

(** Deals with goals of the form [p1 <> p2], with [p1] and [p2] two [SEXP] pointers. **)
Ltac prove_locations_different :=
  let aux p1 p2 :=
    match goal with
    | _ => prove_not_NULL
    | D : No_duplicates ?l |- _ =>
      abstract (
        let N1 := prove_Nth p1 l in
        let N2 := prove_Nth p2 l in
        let E := fresh "E" in
        forwards E: No_duplicates_Nth D N1 N2;
        false~ E )
    | A : alloc_SExp ?S _ = (?S', p1),
      R : read_SExp (state_memory ?S) p2 = Some _ |- _ =>
      applys~ alloc_read_SExp_diff A R
    | A : alloc_SExp ?S _ = (?S', p2),
      R : read_SExp (state_memory ?S) p1 = Some _ |- _ =>
      apply~ noteq_sym;
      applys~ alloc_read_SExp_diff A R
    | A : alloc_SExp ?S _ = (?S', p1),
      B : bound ?S p2 |- _ =>
      let E := fresh B in
      let p2' := fresh1 p2 in
      let p2_ := fresh p2' "_" in
      lets (p2_&E): bound_read B;
      applys~ alloc_read_SExp_diff A (rm E)
    | A : alloc_SExp ?S _ = (?S', p2),
      B : bound ?S p1 |- _ =>
      let E := fresh B in
      let p2' := fresh1 p2 in
      let p2_ := fresh p2' "_" in
      lets (p2_&E): bound_read B;
      apply~ noteq_sym;
      applys~ alloc_read_SExp_diff A (rm E)
    | A : alloc_SExp ?S _ = (?S', p1),
      B : bound_such_that ?S _ p2 |- _ =>
      let E := fresh B in
      let p2' := fresh1 p2 in
      let p2_ := fresh p2' "_" in
      lets (p2_&E&_): B;
      applys~ alloc_read_SExp_diff A (rm E)
    | A : alloc_SExp ?S _ = (?S', p2),
      B : bound_such_that ?S _ p1 |- _ =>
      let E := fresh B in
      let p2' := fresh1 p2 in
      let p2_ := fresh p2' "_" in
      lets (p2_&E&_): B;
      apply~ noteq_sym;
      applys~ alloc_read_SExp_diff A (rm E)
    | A : alloc_SExp ?S _ = (?S', p1) |- _ =>
      get_may_have_types_no_S p2 ltac:(fun M =>
        let E := fresh1 M in
        let p2' := fresh1 p2 in
        let p2_ := fresh p2' "_" in
        lets (p2_&E&_): M;
        applys~ alloc_read_SExp_diff A (rm E))
    | A : alloc_SExp ?S _ = (?S', p2) |- _ =>
      get_may_have_types_no_S p2 ltac:(fun M =>
        let E := fresh1 M in
        let p2' := fresh1 p2 in
        let p2_ := fresh p2' "_" in
        lets (p2_&E&_): M;
        apply~ noteq_sym;
        applys~ alloc_read_SExp_diff A (rm E))
    | _ => discriminate
    | R1 : read_SExp (state_memory ?S) p1 = _,
      R2 : read_SExp (state_memory ?S) p2 = _ |- _ =>
      solve [
        let E := fresh "E" in
        introv E; rewrite E in R2; rewrite R2 in R1; inverts~ R1 ]
    | _ =>
      solve [
          autos~
        | let E := fresh "E" in
          introv E; substs; simplify_context_base; false~ ]
    end in
  lazymatch goal with
  | |- ?p1 <> ?p2 => aux p1 p2
  | |- ?p1 = ?p2 -> False => aux p1 p2
  end.


(** In order to differentiate as many pointers [SEXP] as possible,
  the following tactics generate hypotheses of the form
  [No_duplicates [p1; …; pn]]. **)

(** Given an hypothesis [D] of the form [No_duplicates l], this tactic
  tries to replace it by an hypothesis of the form [No_duplicates (p :: l). **)
Ltac add_in_No_duplicates_hypothesis D p :=
  lazymatch type of D with
  | No_duplicates ?l =>
    let already_in := compute_is_in p l in
    lazymatch already_in with
    | false =>
      let D' := fresh D in
      forwards D': No_duplicates_cons p D;
      [ abstract (
          let M := fresh "M" in
          introv M;
          explode_list M;
          gen M;
          prove_locations_different)
      | clear D; rename D' into D ]
    end
  end.

(** This tactic tries to add [p] in as many [No_duplicates l] hypotheses as possible. **)
Ltac add_in_No_duplicates p :=
  (** First step: we add it in any hypothesis we can. **)
  repeat match goal with
  | D : No_duplicates _ |- _ =>
    add_in_No_duplicates_hypothesis D p
  end;
  (** Second step: we check that at least one hypothesis contains the pointer. **)
  match goal with
  | D : No_duplicates ?l |- _ =>
    let already_in := compute_is_in p l in
    lazymatch already_in with
    | true =>
      (** There is at least one hypothesis about this location. **)
      idtac
    end
  | _ =>
    (** There are no hypothesis about this location: we create a new one, and tries to
      add as many locations as possible to it. **)
    let D := fresh "D" in
    forwards D: (No_duplicates_single p);
    repeat match goal with
    | p' : SEXP |- _ =>
      add_in_No_duplicates D p'
    end
  end.

(** This tactic tries to add hyptheses of the form [No_duplicates l] for all interesting
  pointers in the context. **)
Ltac prepare_No_duplicates_hypothesis :=
  let already_has p :=
    match goal with
    | D : No_duplicates ?l |- _ =>
      let already_in := compute_is_in p l in
      match already_in with
      | true => constr:(true)
      end
    | _ => constr:(false)
    end in
  let must_be_new p :=
    let a := already_has p in
    lazymatch a with
    | false => idtac
    end in
  repeat match goal with
  | B : bound _ ?p |- _ =>
    must_be_new p;
    add_in_No_duplicates p
  | B : bound_such_that _ _ ?p |- _ =>
    must_be_new p;
    add_in_No_duplicates p
  | R : read_SExp _ ?p = Some _ |- _ =>
    must_be_new p;
    add_in_No_duplicates p
  | T : may_have_types _ _ ?p |- _ =>
    must_be_new p;
    add_in_No_duplicates p
  | L : list_type _ _ _ _ ?p |- _ =>
    must_be_new p;
    add_in_No_duplicates p
  | L : list_type_such_that _ _ _ _ _ _ _ ?p |- _ =>
    must_be_new p;
    add_in_No_duplicates p
  | L : list_type_safe _ _ _ _ ?p |- _ =>
    must_be_new p;
    add_in_No_duplicates p
  | A : alloc_SExp _ _ = (_, ?p) |- _ =>
    must_be_new p;
    add_in_No_duplicates p
  | _ =>
    let r :=
      lazymatch goal with
      | D : @No_duplicates SEXP _ |- _ => constr:(true)
      | _ => constr:(false)
      end in
    lazymatch r with
    | false =>
      let D := fresh "D" in
      forwards D: (No_duplicates_nil SEXP)
    end
  end.

(** This tactic must be call before the [read_SExp] expressions are
  updated to the new state. **)
Ltac prepare_proofs_that_locations_are_different :=
  prepare_No_duplicates_hypothesis;
  repeat match goal with
  | A : alloc_SExp ?S ?p_ = (?S', ?p) |- _ =>
    add_in_No_duplicates p
  end.


(** * Applying the right lemma **)

(** This tactic wraps up most of the tactic defined above in a single tactic.
  Note that a more powerful version [solve_premises_smart] of this tactic is
  defined in a section below. **)
Ltac solve_premises_lemmae :=
  autos~;
  let deal_with_list_type S p :=
    let try_hypothesis L :=
      solve [ applys~ list_type_weaken L; try intros; solve_incl ] in
    get_list_type S p ltac:(fun L => try_hypothesis L)
    || solve [
           get_may_have_types S p ltac:(fun M =>
             match type of M with
             | may_have_types S ?l p =>
               let rec allNil l :=
                 lazymatch l with
                 | nil => constr:(true)
                 | NilSxp :: ?l' => let r := allNil l' in r
                 | _ => constr:(false)
                 end in
               let an := allNil l in
               lazymatch an with
               | true =>
                 apply~ list_type_nil; applys~ may_have_types_weaken M; solve_incl
               end
             end)
         | apply list_type_cons; eexists; splits*;
           do 4 eexists; splits*; simplify_context_base;
           (solve_premises_lemmae || (constructors; solve_premises_lemmae)) ] in
  lazymatch goal with
  | |- bound ?S ?p =>
    match goal with
    | E : read_SExp (state_memory S) p = Some _ |- _ =>
      solve [ applys~ read_bound E; solve_premises ]
    | |- _ =>
      solve [
          get_bound S p ltac:(fun M =>
            applys* bound_such_that_weaken M)
        | get_may_have_types S p ltac:(fun M =>
            applys~ may_have_types_bound M; solve_premises)
        | get_safe_pointer_unfolded S p ltac:(fun OKp =>
            applys~ pointer_bound OKp; solve_premises)
        | apply* bound_such_that_weaken; solve_premises ]
    end
  | |- bound_such_that ?S _ ?p =>
    match goal with
    | B : bound_such_that S _ p |- _ =>
      applys~ bound_such_that_weaken B; (solve_incl || solve_premises)
    | B : bound S p |- _ =>
      applys~ bound_such_that_weaken B; (solve_incl || solve_premises)
    | E : read_SExp (state_memory S) p = Some ?p_ |- _ =>
      exists p_; splits~; (solve_incl || solve_premises)
    end
  | |- may_have_types ?S ?l ?p =>
    solve [
        get_may_have_types S p ltac:(fun M =>
          applys~ may_have_types_weaken M;
          solve_incl)
      | eexists; splits*; simpl; Mem_solve ]
  | |- list_type ?S ?l_t ?l_car ?l_tag ?p =>
    deal_with_list_type S p
  | |- list_type_such_that ?Pheader ?Pcar ?Ptag ?S ?l_t ?l_car ?l_tag ?p =>
    deal_with_list_type S p
  | |- list_type_safe ?S ?l_t ?l_car ?l_tag ?p =>
    deal_with_list_type S p
  | |- _ <> _ => prove_locations_different
  | |- _ \c _ => substs; solve_incl
  | |- _ \in _ => substs; Mem_solve
  | |- Mem _ _ => substs; Mem_solve
  | |- _ = _ => substs~; apply* BagInSingle_list
  | |- _ => solve_premises
  end.


(** * Tactics taking advantage of the invariants **)

(** ** Simplifying the context **)

(** Simplifies the context. In addition to [simplify_context_base], it also uses invariants
  such as [safe_state S] to merge [NilSxp]-typed pointers. **)
Ltac simplify_context :=
  repeat match goal with
  | OKg : safe_globals ?S ?globals,
    T : may_have_types ?S ([NilSxp]) ?p |- _ =>
    lazymatch p with
    | read_globals _ R_NilValue => fail
    | _ =>
      get_safe_state S ltac:(fun Safe =>
        let Tnil := fresh "Tnil" in
        forwards~ Tnil: R_NilValue_may_have_types OKg;
        let E := fresh "E" in
        forwards~ E: only_one_nil Safe T (rm Tnil);
        try rewrite E in *; clear_trivial)
    end
  | T1 : may_have_types ?S ([NilSxp]) ?p1,
    T2 : may_have_types ?S ([NilSxp]) ?p2 |- _ =>
    get_safe_state S ltac:(fun Safe =>
      let E := fresh "E" in
      forwards~ E: only_one_nil Safe T1 (rm T2);
      try rewrite E in *; clear_trivial)
  | R1 : read_SExp (state_memory ?S) ?p1 = Some ?p1_,
    R2 : read_SExp (state_memory ?S) ?p2 = Some ?p2_,
    T1 : type (get_SxpInfo ?p1_) = NilSxp,
    T2 : type (get_SxpInfo ?p2_) = NilSxp |- _ =>
    get_safe_state S ltac:(fun Safe =>
      let E := fresh "E" in
      forwards~ E: only_one_nil_SExpRec Safe R1 R2 T1 T2;
      try rewrite E in *;
      let E_ := fresh "E_" in
      asserts E_: (p1_ = p2_); [rewrite R1 in R2; inverts~ R2|];
      try rewrite E_ in *;
      clear_trivial)
  | T1 : may_have_types ?S ([NilSxp]) ?p1,
    R2 : read_SExp (state_memory ?S) ?p2 = Some ?p2_,
    T2 : type (get_SxpInfo ?p2_) = NilSxp |- _ =>
    get_safe_state S ltac:(fun Safe =>
      let E := fresh "E" in
      forwards~ E: only_one_nil Safe (rm T1);
      try solve [ exists p2_; splits*; Mem_solve ];
      try rewrite <- E in *; clear_trivial)
  | OKg : safe_globals ?S ?globals,
    R : read_SExp (state_memory ?S) ?p = Some ?p_,
    T : type (get_SxpInfo ?p_) = NilSxp |- _ =>
    lazymatch p with
    | read_globals _ R_NilValue => fail
    | _ =>
      get_safe_state S ltac:(fun Safe =>
        let Tnil := fresh "Tnil" in
        forwards~ Tnil: R_NilValue_may_have_types OKg;
        let E := fresh "E" in
        forwards~ E: only_one_nil Safe (rm Tnil);
        try solve [ exists p_; splits*; Mem_solve ];
        try rewrite E in *; clear_trivial)
    end
  | _ => simplify_context_base
  end.


(** * Proving expression types different **)

(** Tries to solve a goal of the form [t1 <> t2] where [t1] and [t2] are of type [SExpType]. **)
Ltac prove_types_different :=
  simplify_context;
  let aux t1 t2 :=
    let rec rewrite_type t :=
      match t with
      | _ =>
        lazymatch goal with
        | E : t = _ |- _ => rewrite E
        | E : t \in _ |- _ => explode_list E; rewrite E
        end
      | type (get_SxpInfo ?p_) =>
        match goal with
        | E : read_SExp (state_memory ?S) ?p = Some p_ |- _ =>
          get_may_have_types S p ltac:(fun T =>
            let L := fresh "L" in
            forwards L: may_have_types_read_SExp T E;
            explode_list L; rewrite L)
        end
      end in
    solve [
        try rewrite_type t1; try rewrite_type t2; (discriminate || (substs~; discriminate))
      | let E := fresh "E" in
        introv E; substs; false~ ] in
  lazymatch goal with
  | |- ?t1 <> ?t2 => aux t1 t2
  | |- ?t1 = ?t2 -> False => aux t1 t2
  end.


(** * Transitions between states **)

(** Tries to find a term of the form [conserve_old_bindings S S']
  in the goal, typically from an allocation. **)
Ltac find_conserve_old_bindings S S' cont :=
  lazymatch goal with
  | C : conserve_old_bindings S S' |- _ => cont C
  | E : alloc_SExp S ?p_ = (S', ?p) |- _ =>
    let C := fresh "C" in
    forwards~ C: alloc_SExp_conserve_old_bindings E;
    cont C
  | W : write_SExp S ?e _ = Some S',
    R : read_SExp (state_memory) S ?e = None |- _ =>
    let C := fresh "C" in
    forwards~ C: write_SExp_conserve_old_bindings_when_read_None R W;
    cont C
  | E : state_equiv S S' |- _ =>
    let C := fresh "C" in
    forwards~ C: state_equiv_conserve_old_bindings E;
    cont C
  | E : state_equiv S' S |- _ =>
    let E' := fresh E in
    forwards~ E': state_equiv_sym E;
    let C := fresh "C" in
    forwards~ C: state_equiv_conserve_old_bindings E';
    cont C
  | _ =>
    match S' with
    | S =>
      let C := fresh "C" in
      forwards C: conserve_old_bindings_refl S;
      cont C
    end
  end.


(** * Solving frequent patterns. **)

(** This tactic wraps up most of the tactic defined in this file in a single tactic:
  if you are looking for important tactic in this file, you should not miss this one.
  It should do a decent job in most of the cases.
  It either solves the goal, or fail. **)
Ltac solve_premises_smart :=
  let apply_or_rewrite OK :=
    solve [
        apply OK
      | rewrite_safe_pointer;
        first [
            apply OK
          | let OK' := fresh1 OK in
            lets OK': OK;
            rewrite_safe_pointer_in OK';
            apply OK' ] ] in
  lazymatch goal with
  | |- safe_state ?S =>
    get_safe_state S ltac:(fun OKS => apply OKS)
  | |- safe_globals ?S ?globals =>
    get_safe_globals S globals ltac:(fun OKg => apply OKg)
  | |- safe_pointer ?S ?e =>
    get_safe_pointer S e ltac:(fun OKe => apply OKe)
  | |- safe_pointer_gen _ ?S ?e =>
    get_safe_pointer S e ltac:(fun OKe =>
      apply_or_rewrite OKe)
  | |- safe_SExpRec ?S ?e_ =>
    get_safe_SExpRec S e_ ltac:(fun OKe_ => apply OKe_)
  | |- safe_SExpRec_gen _ ?S ?e_ =>
    get_safe_SExpRec S e_ ltac:(fun OKe_ =>
      apply_or_rewrite OKe_)
  | |- safe_header ?S ?h =>
    get_safe_header S h ltac:(fun OKh => apply OKh)
  | |- safe_header_gen _ ?S ?h =>
    get_safe_header S h ltac:(fun OKh =>
      apply_or_rewrite OKh)
  | |- conserve_old_bindings ?S ?S' =>
    find_conserve_old_bindings S S' ltac:(fun C => apply C)
  | |- _ <> _ => prove_locations_different || prove_types_different
  | _ => prove_no_null_pointer_exceptions || solve_premises_lemmae
  end.


(** Given two states whose property [conserve_old_bindings S S'] is
  producable by the above tactic, this tactic tries to update the
  predicates of the goal about [S] to predicates about [S']. **)
Ltac transition_conserve S S' :=
  prepare_proofs_that_locations_are_different;
  let update_safe_props_from_alloc A S S' p_ :=
    lazymatch goal with
    | OKS : safe_state S |- _ =>
      get_safe_SExpRec S p_ ltac:(fun OKp_ =>
        let S'' := fresh1 S' in
        let OKS' := fresh "OK" S'' in
        let OKp_' := fresh1 OKp_ in
        asserts OKS': (safe_state S');
        [ applys* alloc_SExp_safe_state OKS OKp_ A;
          solve [ prove_types_different ] |];
        asserts OKp_': (safe_SExpRec S' p_);
        [ applys* conserve_old_bindings_safe_SExpRec OKp_;
          solve [ applys* alloc_SExp_conserve_old_bindings A ] |])
    | OKS_cond : ?cond -> safe_state S |- _ =>
      let S'' := fresh1 S' in
      let OKS' := fresh "OK" S'' in
      try (
        asserts OKS': (safe_state S' \/ cond -> safe_state S');
        [ let H := fresh in
          intros [H|H];
          [ exact H
          | let OKS := fresh OKS_cond in
            forwards OKS: OKS_cond H;
            get_safe_SExpRec S p_ ltac:(fun OKp_ =>
              let OKp_' := fresh1 OKp_ in
              applys* alloc_SExp_safe_state OKS OKp_ A;
              solve [ prove_types_different ]) ] |];
        asserts OKp_': (safe_SExpRec S' p_ \/ cond -> safe_SExpRec S' p_);
        [ let H := fresh in
          intros [H|H];
          [ exact H
          | let OKS := fresh OKS_cond in
            forwards OKS: OKS_cond H;
            get_safe_SExpRec S p_ ltac:(fun OKp_ =>
              applys* conserve_old_bindings_safe_SExpRec OKp_;
              solve [ applys* alloc_SExp_conserve_old_bindings A ]) ] |])
    end in
  find_conserve_old_bindings S S' ltac:(fun C =>
    first [
        syntactically_the_same S S'
      | repeat lazymatch goal with
        | A : alloc_SExp ?S0 ?p_ = (S, ?p) |- _ =>
          try update_safe_props_from_alloc A S0 S p_;
          try first [ generate_safe_pointer S p | generate_safe_SExpRec S p_ ];
          (** Saving a copy that won’t match, to avoid looping without loosing information. **)
          let A' := fresh A in
          asserts A': (alloc_SExp S0 p_ = id (S, p)); [ apply* A |];
          let F := fresh "F" in
          forwards F: alloc_read_SExp_fresh A;
          let E := fresh "E" in
          forwards E: alloc_read_SExp_eq (rm A)
        | A : alloc_SExp ?S ?p_ = (S', ?p) |- _ =>
          try update_safe_props_from_alloc A S S' p_;
          try first [ generate_safe_pointer S' p | generate_safe_SExpRec S' p_ ];
          (** Saving a copy that won’t match, to avoid looping without loosing information. **)
          let A' := fresh A in
          asserts A': (alloc_SExp S p_ = id (S', p)); [ apply* A |];
          let F := fresh "F" in
          forwards F: alloc_read_SExp_fresh A;
          let E := fresh "E" in
          forwards E: alloc_read_SExp_eq (rm A)
        | E : read_SExp (state_memory S) ?p = Some ?p_ |- _ =>
          let E' := fresh E in
          forwards E': conserve_old_bindings_read C (rm E);
          rename E' into E
        | B : bound S ?p |- _ =>
          let B' := fresh B in
          forwards B': conserve_old_bindings_bound C (rm B);
          rename B' into B
        | E : may_have_types S ?l ?p |- _ =>
          let E' := fresh E in
          forwards E': conserve_old_bindings_may_have_types C (rm E);
          rename E' into E
        | E : list_type S ?l_t ?l_car ?l_tag ?p |- _ =>
          let E' := fresh E in
          forwards E': conserve_old_bindings_list_type C (rm E);
          rename E' into E
        | E : list_head S ?l_t ?l_car ?l_tag ?p_ |- _ =>
          let E' := fresh E in
          forwards E': conserve_old_bindings_list_head C (rm E);
          rename E' into E
        | E : list_type_such_that ?Pheader ?Pcar ?Ptag S ?l_t ?l_car ?l_tag ?p |- _ =>
          let E' := fresh E in
          forwards E': conserve_old_bindings_list_type C (rm E);
          rename E' into E
        | E : list_head_such_that ?Pcar ?Ptag S ?l_t ?l_car ?l_tag ?p_ |- _ =>
          let E' := fresh E in
          forwards E': conserve_old_bindings_list_head C (rm E);
          rename E' into E
        | E : list_type_safe S ?l_t ?l_car ?l_tag ?p |- _ =>
          let E' := fresh E in
          forwards E': conserve_old_bindings_list_type_safe C (rm E);
          rename E' into E
        | E : list_head_safe S ?l_t ?l_car ?l_tag ?p_ |- _ =>
          let E' := fresh E in
          forwards E': conserve_old_bindings_list_head_safe C (rm E);
          rename E' into E
        | OKp : safe_pointer S ?p |- _ =>
          (** Saving a copy that won’t match, to avoid looping without loosing information. **)
          let OKpold := fresh OKp "_old" in
          asserts OKpold: (id safe_pointer S p); [ apply* OKp |];
          let OKp' := fresh OKp in
          forwards OKp': conserve_old_bindings_safe_pointer C (rm OKp);
          rename OKp' into OKp
        | OKp : safe_pointer_gen ?sp S ?p |- _ =>
          let OKp' := fresh OKp in
          ((forwards* OKp': conserve_old_bindings_safe_pointer_aux C (rm OKp); [idtac])
           || solve [ forwards* OKp': conserve_old_bindings_safe_pointer_aux C OKp ]);
          rename OKp' into OKp
        | OKp_ : safe_SExpRec S ?p_ |- _ =>
          (** Saving a copy that won’t match, to avoid looping without loosing information. **)
          let OKp_old := fresh OKp_ "_old" in
          asserts OKp_old: (id safe_SExpRec S p_); [ apply* OKp_ |];
          let OKp_' := fresh OKp_ in
          forwards OKp_': conserve_old_bindings_safe_SExpRec C (rm OKp_);
          rename OKp_' into OKp_
        | OKp_ : safe_SExpRec_gen _ S ?p_ |- _ =>
          let OKp_' := fresh OKp_ in
          ((forwards* OKp_': conserve_old_bindings_safe_pointer_aux C (rm OKp_); [idtac])
           || solve [ forwards* OKp_': conserve_old_bindings_safe_pointer_aux C OKp_ ]);
          rename OKp_' into OKp_
        | G : safe_globals S ?globals |- _ =>
          let G' := fresh G in
          forwards G': conserve_old_bindings_safe_globals C (rm G);
          rename G' into G
        end; simplify_context ]).

(** If the state [S'] has been produced from [S] by the
  [write_SExp] function, this tactic tries to update the
  predicates of the goal about [S] to predicates about [S']. **)
Ltac transition_write_SExp S S' :=
  prepare_proofs_that_locations_are_different;
  let find_write cont :=
    lazymatch goal with
    | W : write_SExp S ?p ?p_ = Some S' |- _ => cont W p p_
    | E : Some S' = write_SExp S ?p ?p_ |- _ =>
      let W := fresh E in
      lets W: E; symmetry in W; try clear E;
      cont W p p_
    end in
  find_write ltac:(fun W p p_ =>
    try first [ generate_safe_pointer S' p | generate_safe_SExpRec S' p_ ];
    let R := fresh "E" in
    forwards~ R: read_write_SExp_eq W;
    repeat match goal with
    | E : read_SExp (state_memory S) ?p = Some ?p_ |- _ =>
      lazymatch type of R with
      | read_SExp (state_memory S') p = _ => clear E
      | _ =>
        let E' := fresh E in
        forwards E': read_write_SExp_neq W E;
        [ prove_locations_different | rewrite E' in E; clear E' ]
      end
    | A : alloc_SExp _ ?p_ = (S, ?p) |- _ =>
      apply alloc_read_SExp_Some in A;
      let E := fresh A in
      forwards E: read_write_SExp_neq R A;
      [ prove_locations_different | rewrite E in A; clear E ]
    | B : bound S ?p |- _ =>
      let B' := fresh B in
      forwards~ B': bound_write W (rm B);
      rename B' into B
    | E : may_have_types S ?l ?p |- _ =>
      match type of W with
      | write_SExp S p ?p_ =>
        clear E;
        try match goal with
        | T : type (get_SxpInfo p_) = ?t |- _ =>
          forwards E: may_have_types_write_SExp_eq_exact W T
        | T : type (get_SxpInfo p_) \in ?t |- _ =>
          forwards E: may_have_types_write_SExp_eq W T
        end
      | _ =>
        let E' := fresh E in
        forwards E': may_have_types_write_SExp W E;
        [ prove_locations_different | rewrite E' in E; clear E' ]
      end
    (*| E : list_type S ?l_t ?l_car ?l_tag ?p |- _ =>
      Unfortunately the lemma for list types is quite complex:
      we have to prove that we did not rewrite any pointer of the list.
      For this, we probably need a stronger logics, like separation logic.
      Although we might still be able to prove it in the case of alloc_SExp
      (which is the most common). TODO *)
    end; simplify_context).


(** * Correctness lemmae of some R functions **)

(** ** [TYPEOF] **)

Lemma TYPEOF_pass : forall S x t,
  may_have_types S ([t]) x ->
  TYPEOF S x = result_success S t.
Proof. introv T. unfolds. rewrite_read_SExp. simplifyR. self_rewrite. Qed.

Lemma TYPEOF_result : forall S x t,
  may_have_types S ([t]) x ->
  result_prop (fun S' r => r = t /\ S' = S) (fun _ => False) (fun _ _ _ => False)
    (TYPEOF S x).
Proof. introv T. unfolds TYPEOF. rewrite_read_SExp. simplifyR. splits~. Qed.


(** ** [CONS] **)

Lemma CONS_safe : forall globals S S' l_car l_tag car cdr l,
  safe_state S ->
  safe_globals S globals ->
  safe_pointer S car ->
  list_type_safe S ([ListSxp]) l_car l_tag cdr ->
  may_have_types S l_car car ->
  l_car \c all_storable_SExpTypes ->
  l_tag \c [NilSxp; CharSxp] ->
  CONS globals S car cdr = (S', l) ->
  safe_state S' /\ safe_globals S' globals /\ safe_pointer S' l
  /\ list_type_safe S' ([ListSxp]) l_car ([NilSxp] \u l_tag) l
  /\ conserve_old_bindings S S'.
Proof.
  introv OKS OKG OKcar Lcdr Tcar Icar Itag E. unfolds in E.
  transition_conserve S S'.
  splits; try solve_premises_smart.
  - rewrite safe_pointer_rewrite. constructors.
    + (** pointer_bound **)
      applys* read_bound.
    + (** no_null_pointer_along_path_step **)
      introv N Em. unfolds in Em. self_rewrite in Em. simpl in Em.
      destruct s as [|?|[| |]|?|?|?|?]; inverts~ Em; solve_premises_smart.
    + (** safe_pointer_along_path_step **)
      introv Em NN. unfolds in Em. rewrite E1 in Em. simpl in Em.
      destruct s as [|?|[| |]|?|?|?|?]; inverts~ Em; solve_premises_smart.
    + (** safe_SExpRec_read **)
      self_rewrite. introv E2. inverts E2. solve_premises_smart.
  - applys list_type_cons. eexists. splits*. do 4 eexists. splits*; solve_premises_smart.
Qed.


(** ** [allocList] **)

Lemma allocList_aux_safe : forall globals S S' n l l0,
  safe_state S ->
  safe_globals S globals ->
  safe_pointer S l0 ->
  list_type_safe S ([ListSxp]) ([NilSxp]) ([NilSxp]) l0 ->
  allocList_aux globals S n l0 = (S', l) ->
  safe_state S' /\ safe_globals S' globals /\ safe_pointer S' l
  /\ list_type_safe S' ([ListSxp]) ([NilSxp]) ([NilSxp]) l
  /\ conserve_old_bindings S S'.
Proof.
  introv OKS OKG OKl0 L E. gen S S' l. induction n; introv OKS OKG OKl0 L E.
  - inverts E. splits~. apply~ conserve_old_bindings_refl.
  - simpl in E. destruct allocList_aux as [S2 p] eqn: Ep.
    forwards~ (OKS2&OKG2&OKp&Lp&C): IHn Ep.
    forwards~ (OKS'&OKG'&OKl&Ll&C'): CONS_safe Lp E; try solve_premises_smart.
    simplify_context. splits*. applys conserve_old_bindings_trans C C'.
Qed.

Lemma allocList_safe : forall globals S S' n l,
  safe_state S ->
  safe_globals S globals ->
  allocList globals S n = (S', l) ->
  safe_state S' /\ safe_globals S' globals /\ safe_pointer S' l
  /\ list_type_safe S' ([ListSxp]) ([NilSxp]) ([NilSxp]) l
  /\ conserve_old_bindings S S'.
Proof.
  introv OKS OKG E. unfolds in E. applys~ allocList_aux_safe E.
  - applys~ globals_not_NULL_safe OKG. applys~ globals_not_NULL OKG.
    introv A. inverts A.
  - apply list_type_nil. applys~ R_NilValue_may_have_types OKG.
Qed.


(** * Specific tactics **)

(** The tactics defined below applies the specific lemmae proven in the previous section
  to prove the [computeR] tactic, similar to [simplifyR] but making use invariants, and
  propagating them. **)

Ltac get_result_lemma t :=
  lazymatch get_head t with
  | TYPEOF => constr:(>> TYPEOF_pass TYPEOF_result)
  end.

Ltac apply_result_lemma t :=
  let R := get_result_lemma t in
  let L := list_boxer_of R in
  let rec try_all_lemmae L :=
    lazymatch L with
    | boxer ?R :: ?L' =>
      first [
          rewrite R
        | eapply R
        | let P := fresh "P" in
          eapply if_success_result; [ introv P | solve [ apply* R] ]
        | try_all_lemmae L' ]
    end in
  try_all_lemmae L;
  simplify_context;
  try solve_premises_smart.

Ltac computeR_step :=
  simplifyR;
  rewrite_read_SExp;
  match goal with
  | |- context [ read_SExp (state_memory ?S) ?x ] =>
    rewrite_read_SExp
  | |- context [ write_SExp ?S ?p ?p_ ] =>
    define_write_SExp S p p_;
    match goal with
    | E : write_SExp S p p_ = Some ?S' |- _ =>
      first [
          find_conserve_old_bindings S S' ltac:(fun _ =>
            transition_conserve S S')
        | repeat rewrite E;
          transition_write_SExp S S' ]
    end
  | |- context [ alloc_SExp ?S ?p_ ] =>
    let p := fresh "p" in
    let S' := fresh1 S in
    let E := fresh "E" S' in
    destruct (alloc_SExp S p_) as [S' p] eqn: E;
    transition_conserve S S'
  | |- context [ TYPEOF ?S ?e ] =>
    apply_result_lemma (TYPEOF S e)
  | |- context [ CONS ?globals ?S ?car ?cdr ] =>
    let S' := fresh1 S in
    let l := fresh "l" in
    let E := fresh "E" l in
    destruct (CONS globals S car cdr) as [S' l] eqn: E;
    let OKS' := fresh "OK" S' in
    let OKG' := fresh "OKG" in
    let OKl' := fresh "OK" l in
    let L := fresh "L" in
    forwards (OKS'&OKG'&OKl'&L): CONS_safe E; try solve_premises_smart;
    [idtac];
    simplify_context
  | |- context [ allocList ?globals ?S ?n ] =>
    let S' := fresh1 S in
    let l := fresh "l" in
    let E := fresh "E" l in
    destruct (allocList globals S n) as [S' l] eqn: E;
    let OKS' := fresh "OK" S' in
    let OKG' := fresh "OKG" in
    let OKl' := fresh "OK" l in
    let L := fresh "L" in
    forwards (OKS'&OKG'&OKl'&L): allocList_safe E; try solve_premises_smart;
    [idtac]
  | _ => idtac
  end;
  clear_trivial.

Ltac computeR :=
  repeat computeR_step.

