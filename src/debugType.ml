(** Debug Type **)

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

open Extract

type funtype =
  | Result_unit of (globals -> runs_type -> unit result)
  | Result_bool of (globals -> runs_type -> bool result)
  | Result_int of (globals -> runs_type -> int result)
  | Result_int_list of (globals -> runs_type -> int list result)
  | Result_float of (globals -> runs_type -> float result)
  | Result_string of (globals -> runs_type -> char list result)
  | Result_pointer of (globals -> runs_type -> sEXP result)

  | Argument_unit of (unit -> funtype)
  | Argument_bool of (bool -> funtype)
  | Argument_int of (int -> funtype)
  | Argument_float of (float -> funtype)
  | Argument_pointer of (sEXP -> funtype)

