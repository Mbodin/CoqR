(** Extraction.
  Extract R interpreter into OCaml. **)

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

Require Export Rinit Rparsing.

Extraction Language Ocaml.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

Set Extraction AccessOpaque.

(* TODO: Clean. *)
(* As classical logic statements are now unused, they should not be extracted
   (otherwise, useless errors will be launched). *)
Extraction Inline (*epsilon epsilon_def*) classicT arbitrary indefinite_description (*Inhab_witness*) Fix isTrue.

Extract Constant run_stdout_print => "Hooks.stdout_print".
Extract Constant run_stderr_print => "Hooks.stderr_print".
Extract Constant run_stdout_flush => "Hooks.stdout_flush".
Extract Constant run_stderr_flush => "Hooks.stderr_flush".

Extract Constant add_stack_entering => "Hooks.add_stack_entering".
Extract Constant add_stack_leaving => "Hooks.add_stack_leaving".

Extract Inductive positive => "int"
[ "(fun p -> 1 + (2 * p))"
  "(fun p -> 2 * p)"
  "1" ]
"(fun f2p1 f2p f1 p ->
  if p <= 1 then f1 () else if p mod 2 = 0 then f2p (p / 2) else f2p1 (p / 2))".

Extract Inductive Z => "int" [ "0" "" "(~-)" ]
"(fun f0 fp fn z -> if z = 0 then f0 () else if z > 0 then fp z else fn (~- z))".

Extract Inductive N => "int" [ "0" "" ]
"(fun f0 fp n -> if n = 0 then f0 () else fp n)".

Extract Constant Z.add => "(+)".
Extract Constant Z.succ => "(+) 1".
Extract Constant Z.pred => "(fun x -> x - 1)".
Extract Constant Z.sub => "(-)".
Extract Constant Z.mul => "( * )".
Extract Constant Z.opp => "(~-)".
Extract Constant Z.abs => "abs".
Extract Constant Z.min => "min".
Extract Constant Z.max => "max".
Extract Constant Z.compare =>
 "fun x y -> if x = y then Eq else if x < y then Lt else Gt".

Extract Constant Pos.add => "(+)".
Extract Constant Pos.succ => "(+) 1".
Extract Constant Pos.pred => "(fun x -> x - 1)".
Extract Constant Pos.sub => "(-)".
Extract Constant Pos.mul => "( * )".
Extract Constant Pos.min => "min".
Extract Constant Pos.max => "max".
Extract Constant Pos.compare =>
 "fun x y -> if x = y then Eq else if x < y then Lt else Gt".
Extract Constant Pos.compare_cont =>
 "fun c x y -> if x = y then c else if x < y then Lt else Gt".

Extract Constant N.add => "(+)".
Extract Constant N.succ => "(+) 1".
Extract Constant N.pred => "(fun x -> x - 1)".
Extract Constant N.sub => "(-)".
Extract Constant N.mul => "( * )".
Extract Constant N.min => "min".
Extract Constant N.max => "max".
Extract Constant N.div => "(fun x y -> if x = 0 then 0 else (x / y)".
Extract Constant N.modulo => "mod".
Extract Constant N.compare =>
 "fun x y -> if x = y then Eq else if x < y then Lt else Gt".

(* FIXME: The additional information carried by the NaN value has to be remembered because of the
  difference between R_NaReal_ and R_NaN. *)
Extract Inductive Fappli_IEEE.full_float => "float" [
  "(fun s -> if s then (-0.) else (0.))"
  "(fun s -> if s then neg_infinity else infinity)"
  "let f = fun (b, p) -> nan in f"
  "(fun (s, m, e) -> failwith ""FIXME: No extraction from binary float allowed yet."")"
].
Extract Constant Double.NaN => "nan".
Extract Constant Double.NaN1954 =>
  "(let (a, b) = (Obj.magic nan : int * int) in
    let r = (Obj.magic (a, 1954) : float) in
    assert (classify_float r = FP_nan) ; r)".
Extract Constant Double.isNaN => "(fun x -> classify_float x = FP_nan)".
Extract Constant Double.getNaNData =>
  "(let f x =
      if classify_float x = FP_nan then
        let (_, b) = (Obj.magic x : int * int) in
        Some b
      else None in
    assert (f naN1954 = Some 1954) ;
    f)".
Extract Constant Double.double_comparable =>
  "(fun x y ->
     match classify_float x, classify_float y with
     | FP_nan, FP_nan ->
       (Obj.magic x : int * int) = (Obj.magic y : int * int)
     | FP_zero, FP_zero ->
       let sign x = copysign 1. x < 0. in
       sign x = sign y
     | _, _ -> compare x y = 0)".

Extract Constant Double.opp => "(~-.)".
Extract Constant Double.fabs => "abs_float".
Extract Constant Double.add => "(+.)".
Extract Constant Double.sub => "(-.)".
Extract Constant Double.mult => "( *. )".
Extract Constant Double.div => "(/.)".

Extract Constant Double.floor => "floor".
Extract Constant Double.ceil => "ceil".
Extract Constant Double.sqrt => "sqrt".
Extract Constant Double.exp => "exp".
Extract Constant Double.expm1 => "expm1".
Extract Constant Double.log => "log".
Extract Constant Double.logm1 => "logm1".
Extract Constant Double.log1p => "log1p".
Extract Constant Double.cos => "cos".
Extract Constant Double.sin => "sin".
Extract Constant Double.tan => "tan".
Extract Constant Double.acos => "acos".
Extract Constant Double.asin => "asin".
Extract Constant Double.atan => "atan".
Extract Constant Double.cosh => "cosh".
Extract Constant Double.sinh => "sinh".
Extract Constant Double.tanh => "tanh".

Extract Constant Double.FLT_EPSILON => "epsilon_float".

Extract Constant Double.ge => "(>=)".
Extract Constant Double.le => "(<=)".
Extract Constant Double.gt => "(>)".
Extract Constant Double.lt => "(<)".

Extract Constant Double.int_to_double => "float_of_int".
Extract Constant Double.double_to_int_zero => "int_of_float".

Extract Constant HeapList.heap "'a" "'b" =>
  "int ref * int (* The following time reference at this timestamp. *)".
Extract Constant HeapList.empty => "(ref 0, 0)".
Extract Constant HeapList.write =>
  "fun (hr, h) k v -> assert (h = !hr) ; k := v ; incr hr ; (hr, !hr)".
Extract Constant HeapList.to_list => "fun (hr, h) -> assert (h = !hr) ; assert false".
Extract Constant HeapList.read => "fun _(*comparable*) (hr, h) k -> assert (h = !hr) ; !k".
Extract Constant HeapList.read_option =>
  "fun _(*comparable*) (hr, h) k -> assert (h = !hr) ; Some !k".
Extract Constant HeapList.rem => "fun _(*comparable*) (hr, h) k -> assert (h = !hr) ; assert false".
Extract Constant HeapList.indom_decidable =>
  "fun _(*comparable*) (hr, h) k -> assert (h = !hr) ; true".

Extract Constant alloc_memory_SExp_nat =>
  "fun e_ s -> let k = ref e_ in let (hr, h) = state_heap_SExp s in assert (h = !hr) ; incr hr ; ({ s with state_fresh_locations = stream_tail (state_fresh_locations s) ; state_heap_SExp = (hr, !hr) }, k)"

Extract Constant ArrayList.array "'a" => "(int * (int, 'a) PMap.t)".
Extract Constant ArrayList.length => "fst".
Extract Constant ArrayList.read => "fun (_, a) i -> PMap.find i a".
Extract Constant ArrayList.read_option => "fun (_, a) i -> try Some (PMap.find i a) with Not_found -> None".
Extract Constant ArrayList.write => "fun (n, a) i v -> ((n, PMap.add i v a) : _ array)".
Extract Constant ArrayList.from_list =>
  "fun l -> (List.fold_left (fun (i, m) v -> (i + 1, PMap.add i v m)) (0, PMap.create compare) l : _ array)".
Extract Constant ArrayList.to_list =>
  "fun (n, a) -> let rec aux i = if i = n then [] else PMap.find i a :: aux (i + 1) in aux 0".
Extract Constant ArrayListExtra.map =>
  "fun f (n, a) -> (n, PMap.map f a)".
Extract Constant ArrayList.empty =>
  "Obj.magic (from_list [])".

Extract Constant nat_comparable => "(=)".

Extraction "extract.ml"
  Parsing mkNA R_NaN mkString all_GlobalVariables
  setup_Rmainloop empty_state eval_global.

