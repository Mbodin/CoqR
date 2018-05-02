(** Hooks
  Contains some impure functions used by the Coq extracted code (mainly input and output). **)

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

let log = ref false
let log_only_at_newlines = ref true

let trace = ref false


let char_list_to_string str =
  String.concat "" (List.map (String.make 1) str)

let string_to_char_list str =
  let rec aux i acc =
    if i < 0 then acc
    else aux (i - 1) (str.[i] :: acc) in
  aux (String.length str - 1) []


let stdout_buffer = ref ""
let stderr_buffer = ref ""

let print_log print loc str =
  let str =
    if !log then
      "Printed message (to " ^ loc ^ "): " ^ str
    else str in
  print str

let generic_print print loc buffer st str =
  let str = char_list_to_string str in
  if !log_only_at_newlines then (
    let l = String.split_on_char '\n' str in
    let l_rev = List.rev l in
    let to_be_printed, staged =
      match List.rev (List.tl l_rev) with
      | [] -> [], !buffer ^ List.hd l_rev
      | l_0 :: l_tl -> (!buffer ^ l_0) :: l_tl, List.hd l_rev in
    List.iter (fun str -> print_log print loc (str ^ "\n")) to_be_printed ;
    buffer := staged
  ) else (
    print_log print loc (!buffer ^ str) ;
    buffer := ""
  ) ;
  Some st

let stdout_print st str = generic_print print_string "stdout" stdout_buffer st str
let stderr_print st str = generic_print prerr_string "stderr" stderr_buffer st str

let generic_flush channel loc print buffer st =
  if !buffer <> "" then (print_log print (loc ^ ", forced by flush, with no newline at the end of the line") !buffer ; buffer := "") ;
  if !log then output_string channel ("Flush (of " ^ loc ^ ").\n") ;
  flush channel ;
  Some st

let stdout_flush st = generic_flush stdout "stdout" print_string stdout_buffer st
let stderr_flush st = generic_flush stderr "stderr" prerr_string stderr_buffer st


let stack_depth = ref 0

let add_stack_entering name cont =
  if !trace then (
    print_endline (String.make !stack_depth ' ' ^ "{ " ^ char_list_to_string name) ;
    incr stack_depth
  ) ;
  cont ()

let add_stack_leaving name cont =
  if !trace then (
    decr stack_depth ;
    print_endline (String.make !stack_depth ' ' ^ "} " ^ char_list_to_string name)
  ) ;
  cont ()

