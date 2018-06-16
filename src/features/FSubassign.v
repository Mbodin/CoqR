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

Definition R_DispatchOrEvalSP S call op generic args rho :=
  add%stack "R_DispatchOrEvalSP" in
  read%list args_car, args_cdr, _ := args using S in
  let%exit (prom, args) :=
    ifb args <> R_NilValue /\ args_car <> R_DotsSymbol then
      let%success x := eval globals runs S args_car rho using S in
      run%success INCREMENT_LINKS S x using S in
      let%success x_obj := OBJECT S x using S in
      if negb x_obj then
        let%success elkm :=
          evalListKeepMissing globals runs S args_cdr rho using S in
        let (S, ans) := CONS_NR globals S x elkm in
        run%success DECREMENT_LINKS S x using S in
        result_rreturn S (false, ans)
      else unimplemented_function "R_mkEVPROMISE_NR"
    else result_rsuccess S (NULL, args) using S in
  let%success (disp, ans) :=
    DispatchOrEval globals runs S call op generic args rho false false using S in
  run%success
    ifb prom <> NULL then
      let%success prom_value := PRVALUE S prom using S in
      DECREMENT_LINKS S prom_value
    else result_skip S using S in
    result_success S (disp, ans).

Definition do_subassign_dflt S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_subassign_dflt" in
    let%success (nsubs, x, subs, y) := SubAssignArgs S args using S in
    fold%success s := subs
    along subs as _, _, s_list do
        let idx := list_carval s_list in
        
        ifb x = idx then
           MARK_NOT_MUTABLE S x
        else
            result_skip S
    using S, runs, globals in

    read%list args_car, _, _ := args using S in
    let%success args_car_maybeShared := MAYBE_SHARED S args_car using S in
    let%success x :=
    if args_car_maybeShared then
        let%success args_car_duplic := shallow_duplicate globals runs S args_car using S in
        set%car args := args_car_duplic using S in
        result_success S args_car_duplic
    else
        result_success S x
    using S in
    let%success S4 := IS_S4_OBJECT S x using S in

    let oldtype := 0 in
    let%success x_type := TYPEOF S x using S in

    let%exit (x, oldtype) :=
    ifb x_type = ListSxp \/ x_type = LangSxp then
        let%success x := PairToVectorList S x using S in
        result_rsuccess S (x, x_type)
    else
        let%success x_xlength := xlength globals runs S x using S in
        ifb x_xlength = 0 then
            let%success y_xlength := xlength globals runs S y using S in
            let%success y_type := TYPEOF S y using S in
            let%success x_isNull := isNull S x using S in
            ifb y_xlength = 0 /\ (x_isNull \/ x_type = y_type \/ y_type = VecSxp \/ y_type = ExprSxp) then
                result_rreturn S x
            else
                if x_isNull then
                    let%success x := coerceVector globals runs S x y_type using S in
                    result_rsuccess S (x, oldtype)
                else
                     result_rsuccess S (x, oldtype)
        else
            result_rsuccess S (x, oldtype)
    using S in    

    let%success x_type := TYPEOF S x using S in
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
      | 0 => VectorAssign S call rho x R_MissingArg y 
      | 1 => read%list subs_car, _, _ := subs using S in
            VectorAssign S call rho x subs_car y
      | 2 => MatrixAssign S call rho x subs y
      | _ => ArrayAssign S call rho x subs y
      end
    | _ => result_error S "Bad type for argument"
    end
    using S in

    let%success x :=
    ifb oldtype = LangSxp then
        let%success x_length := R_length globals runs S x using S in
        ifb x_length <> 0 then
            let%success x := VectorToPairList gobals runs S x using S in
            set%type x := LangSxp using S in
            result_success S x
        else
            result_error S "result is zero-length and so cannot be a language object"
    else
        result_success S x
    using S in

    run%success
    SETTER_CLEAR_NAMED S x using S in
    run%success
    if S4 then
        SET_S4_OBJECT S x
    else
        result_skip S
    using S in
    result_success S x.

Definition do_subassign S (call op args rho) : result SEXP :=
  add%stack "do_subassign" in
    let%success (disp, ans) := R_DispatchOrEvalSP S call op "[<-" args rho using S in
    if disp then
      result_success S ans
    else
      do_subassign_dflt S call op ans rho.

End Parameters.