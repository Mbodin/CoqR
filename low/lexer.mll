{
    (** This file mainly translates Function [yylex] from File gram.y. **)

    open Low
    open Parser

    exception SyntaxError of string
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
  '%' ([^ '%']* as name) '%'

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

rule lex = parse

  (** ** Special Symbols **)
  | "NULL"              { NULL_CONST }
  | "NA"                { NUM_CONST mkNA }
  | "TRUE"              { NUM_CONST mkTrue }
  | "FALSE"             { NUM_CONST mkFalse }
  | "Inf"               { NUM_CONST (fun s -> alloc_vector_real s [r_PosInf]) }
  | "NaN"               { NUM_CONST (fun s -> alloc_vector_real s [r_NaN]) }
  | "NA_integer_"       { NUM_CONST (fun s -> alloc_vector_int s [nA_INTEGER]) }
  | "NA_real_"          { NUM_CONST (fun s -> alloc_vector_real s [nA_REAL]) }
  | "NA_character_"     { NUM_CONST (fun s -> alloc_vector_str s [nA_STRING]) }
  | "NA_complex_"       { NUM_CONST (fun s -> alloc_vector_cplx s [make_Rcomplex nA_REAL nA_REAL]) }
  | "function"          { FUNCTION }
  | "while"             { WHILE }
  | "repeat"            { REPEAT }
  | "for"               { FOR }
  | "if"                { IF }
  | "in"                { IN }
  | "else"              { ELSE }
  | "next"              { NEXT }
  | "break"             { BREAK }
  | "..."               { SYMBOL }

  (** ** Operators **)
  | "?"     { QUESTION_MARK }
  | "<-"    { LEFT_ASSIGN }
  | "="     { EQ_ASSIGN }
  | "->"    { RIGHT_ASSIGN }
  | ":="    { COLON_ASSIGN }
  | "~"     { TILDE }
  | "+"     { PLUS }
  | "-"     { MINUS }
  | "*"     { TIMES }
  | "/"     { DIV }
  | "^"     { EXP }
  | "<"     { LT }
  | "<="    { LE }
  | ">"     { GT }
  | ">="    { GE }
  | "=="    { EQ }
  | "!="    { NEQ }
  | "!"     { NOT }
  | "&"     { AND }
  | "|"     { OR }
  | "$"     { DOLLAR }
  | "@"     { AT }
  | ":"     { COLON }

  (** ** Special Values **)
  | reg_special_operator    { SPECIAL name }
  | reg_string              { STR_CONST }
  | reg_numeric             { NUM_CONST }
  | reg_integer             { NUM_CONST }
  | reg_imaginary           { NUM_CONST }

  (** ** Miscellaneous **)
  | '('                     { LPAR }
  | ')'                     { RPAR }
  | '['                     { LSQBRACKET }
  | ']'                     { RSQBRACKET }
  | ('#' [^ '\n']*)? '\n'   { NEW_LINE }
  | _                       { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | eof                     { EOF }

