{

(* A lexer for simple grammar files.
   Copyright © 2018 Martin Bodin

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

  open Parser

  exception SyntaxError of string
}

let reg_string = ([^ '\\' '"'] | '\\' ('\\' | '"' | 'n'))*

let space = ' ' | '\t' | '\n'

rule lex = parse

  | ';'                         { SEMICOLON }
  | "-often>"                   { ARROW Structures.Often }
  | "->"                        { ARROW Structures.Normal }
  | "-rare>"                    { ARROW Structures.Rare }
  | '"' (reg_string as str) '"' { STRING (Scanf.unescaped str) }
  | ['a'-'z' 'A'-'Z']+ as str   { IDENTIFIER str }

  | '#' [^ '\n']* '\n'          { lex lexbuf }
  | space+                      { lex lexbuf }
  | _                           { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | eof                         { EOF }

