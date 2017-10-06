{
    open Parser

    (** This file mainly translates Function [yylex] from File gram.y. **)
}

(** * Definitions **)

(** ** Constants **)

(** *** Special Constants **)
let reg_null = "NULL"
let reg_na = "NA"
let reg_inf = "Inf"
let reg_nan = "NaN"

(** *** Logical Constants **)
let reg_true = "TRUE"
let reg_false = "FALSE"

(** *** Numerical Constants **)
let digit = ['0'-'9']
let sign = ['+' '-']
let floating_point =
  ((digit+ '.'? digit*) | (digit* '.'? digit+))
  (['e' 'E'] sign? digit+)?
let hexadecimal_digit = ['0'-'9' 'a'-'f' 'A'-'F']
let hexadecimal =
  ("0x" | "0X") hexadecimal_digit*
  (('.' hexadecimal_digit*)? ['p' 'P'] sign? digit+)?
let reg_numeric = (floating_point | hexadecimal)
let reg_integer = reg_numeric 'L'
let reg_imaginary = reg_numeric 'i'

(** *** String Constants **)
let escape_sequence =
  '\\'
  (['\'' '"' 'n' 'r' 't' 'b' 'a' 'f' 'v' '\\']
  |['0'-'7'] (['0'-'7'] ['0'-'7']?)?
  |'x' hexadecimal_digit hexadecimal_digit?
  (** We ignore multibyte locales for now. **))
let normal_character = [^ '\\' '\'' '"'] (* This may be ameliorable. *)
let character = normal_character | escape_sequence
let reg_string =
  '\'' (character | '"')* '\'' | '"' (character | '\'')* '"'


(** ** Language Features **)

(** *** Identifiers **)
let reg_identifier =
  (** For simplicity, we do not deal with locales. **)
  ('.' ['_' '.' 'a'-'z' 'A'-'Z'] | ['a'-'z' 'A'-'Z'])
  ['_' '.' 'a'-'z' 'A'-'Z' '0'-'9']*

let reserved_keywords =
  "if" | "else" | "repeat" | "while" | "function" | "for" | "in" | "next" | "break"
  | "TRUE" | "FALSE" | "NULL" | "Inf" | "NaN"
  | "NA" | "NA_integer_" | "NA_real_" | "NA_complex_" | "NA_character_"
  | "..." | ".." ['0'-'9']+

(** *** Special Operators **)
let reg_special_operator =
  '%' [^ '%']* '%'

let operator_arithmetic =
  "+" | "-" | "*" | '/' | "%%" | "^"
let operator_relational =
  ">" | ">=" | "<" | "<=" | "==" | "!="
let operator_logical =
  "!" | "&" | "|"
let operator_model_formulae =
  "~"
let operator_assignment =
  "->" | "<-"
let operator_list_indexing =
  "$"
let operator_sequence =
  ":"


(** * Rules **)

rule yylex_start = parse
  | '\n'
    { yylex_newline lexbuf }
  | ['+' '-' '*' '/' '^'] (* What about LT, LE, GE, etc. that come afterwards? *)
    { yylex_eatline lexbuf }

(* TODO: Read 10.1 “The parsing process” of R-lang.pdf *)
