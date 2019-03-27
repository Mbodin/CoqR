(** Features.FSubassign.
  The function names of this file correspond to the function names
  in the file main/subassign.c. **)

(* Copyright © 2018 Martin Bodin, Tomás Díaz

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
Require Import Rcore.
Require Import FUtil.



Section Parameters.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Definition R_DispatchOrEvalSP call op generic args rho :=
  add%stack "R_DispatchOrEvalSP" in
  read%list args_car, args_cdr, _ := args in
  let%exit (prom, args) :=
    ifb args <> R_NilValue /\ args_car <> R_DotsSymbol then
      let%success x := eval globals runs args_car rho in
      run%success INCREMENT_LINKS x in
      let%success x_obj := OBJECT x in
      if negb x_obj then
        let%success elkm :=
          evalListKeepMissing globals runs args_cdr rho in
        let (S, ans) := CONS_NR globals x elkm in
        run%success DECREMENT_LINKS x in
        result_rreturn (false, ans)
      else unimplemented_function "R_mkEVPROMISE_NR"
    else result_rsuccess (NULL, args) in
  let%success (disp, ans) :=
    DispatchOrEval globals runs call op generic args rho false false in
  run%success
    ifb prom <> NULL then
      let%success prom_value := PRVALUE prom in
      DECREMENT_LINKS prom_value
    else result_skip in
    result_success (disp, ans).

Definition do_subassign_dflt (call op args rho : SEXP) : result SEXP :=
  add%stack "do_subassign_dflt" in
    let%success (nsubs, x, subs, y) := SubAssignArgs globals runs args in
    fold%success
    along subs as _, _, subs_list do
        let idx := list_carval subs_list in
        
        ifb x = idx then
           MARK_NOT_MUTABLE x
        else
            result_skip
    using runs, globals in

    read%list args_car, _, _ := args in
    let%success args_car_maybeShared := MAYBE_SHARED args_car in
    let%success x :=
    if args_car_maybeShared then
        let%success args_car_duplic := shallow_duplicate globals runs args_car in
        set%car args := args_car_duplic in
        result_success args_car_duplic
    else
        result_success x
    in
    let%success S4 := IS_S4_OBJECT x in

    let oldtype := 0 in
    let%success x_type := TYPEOF x in

    let%exit (x, oldtype) :=
    ifb x_type = ListSxp \/ x_type = LangSxp then
        let%success x := PairToVectorList x in
        result_rsuccess (x, SExpType_to_nat x_type)
    else
        let%success x_xlength := xlength globals runs x in
        ifb x_xlength = 0 then
            let%success y_xlength := xlength globals runs y in
            let%success y_type := TYPEOF y in
            let%success x_isNull := isNull x in
            ifb y_xlength = 0 /\ (x_isNull \/ x_type = y_type \/ y_type = VecSxp \/ y_type = ExprSxp) then
                result_rreturn x
            else
                if x_isNull then
                    let%success x := coerceVector globals runs x y_type in
                    result_rsuccess (x, oldtype)
                else
                     result_rsuccess (x, oldtype)
        else
            result_rsuccess (x, oldtype)
    in    

    let%success x_type := TYPEOF x in
    let%success x :=
    match x_type with
    | LglSxp
    | IntSxp
    | RealSxp
    | CplxSxp
    | StrSxp
    | ExprSxp
    | VecSxp
    | RawSxp =>
      match nsubs with
      | 0 => VectorAssign globals runs call rho x R_MissingArg y 
      | 1 => read%list subs_car, _, _ := subs in
            VectorAssign globals runs call rho x subs_car y
      | 2 => MatrixAssign call rho x subs y
      | _ => ArrayAssign call rho x subs y
      end
    | _ => result_error "Bad type for argument"
    end
    in

    let%success x :=
    ifb oldtype = LangSxp then
        let%success x_length := R_length globals runs x in
        ifb x_length <> 0 then
            let%success x := VectorToPairList globals runs x in
            set%type x := LangSxp in
            result_success x
        else
            result_error "result is zero-length and so cannot be a language object"
    else
        result_success x
    in

    run%success
    SETTER_CLEAR_NAMED x in
    run%success
    if S4 then
        SET_S4_OBJECT x
    else
        result_skip
    in
    result_success x.

Definition do_subassign (call op args rho : SEXP) : result SEXP :=
  add%stack "do_subassign" in
    let%success (disp, ans) := R_DispatchOrEvalSP call op "[<-" args rho in
    if disp then
      result_success ans
    else
      do_subassign_dflt call op ans rho.

End Parameters.