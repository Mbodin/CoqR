{
    (** This file mainly translates the functions [token] and [yylex] from File gram.y. **)

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
let normal_character = [^ '\\' '\'' '"' '\x00'] (* This may be ameliorable. *)
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

(** ** Miscellaneous **)

(** *** Spaces **)
let space = ' ' | '\t' | '\x0c' (** Form feed **) | '\xa0' (** Replacement character **)


(** * Rules **)

rule lex = parse

  (** ** Special Symbols **)
  | "NULL"              { NULL_CONST }
  | "NA"                { NUM_CONST (wrap_no_runs mkNA) }
  | "TRUE"              { NUM_CONST (wrap_no_runs mkTrue) }
  | "FALSE"             { NUM_CONST (wrap_no_runs mkFalse) }
  | "Inf"               { NUM_CONST (wrap_only_state (fun s -> alloc_vector_real s [r_PosInf])) }
  | "NaN"               { NUM_CONST (wrap_only_state (fun s -> alloc_vector_real s [r_NaN])) }
  | "NA_integer_"       { NUM_CONST (wrap_only_state (fun s -> alloc_vector_int s [nA_INTEGER])) }
  | "NA_real_"          { NUM_CONST (wrap_only_state (fun s -> alloc_vector_real s [nA_REAL])) }
  | "NA_character_"     { NUM_CONST (wrap_only_state (fun s -> alloc_vector_str s [nA_STRING])) }
  | "NA_complex_"       { NUM_CONST (wrap_only_state (fun s -> alloc_vector_cplx s [make_Rcomplex nA_REAL nA_REAL])) }
  | "function"          { FUNCTION (install_and_save "function") }
  | "while"             { WHILE (install_and_save "while") }
  | "repeat"            { REPEAT (install_and_save "repeat") }
  | "for"               { FOR (install_and_save "for") }
  | "if"                { IF (install_and_save "if") }
  | "in"                { IN }
  | "else"              { ELSE }
  | "next"              { NEXT (install_and_save "next") }
  | "break"             { BREAK (install_and_save "break") }
  | "..."               { SYMBOL (install_and_save "...") }

  (** ** Operators **)
  | "?"         { QUESTION_MARK (install_and_save "?") }
  | "<-"        { LEFT_ASSIGN (install_and_save "<-") }
  | "="         { EQ_ASSIGN (install_and_save "=") }
  | "->"        { RIGHT_ASSIGN (install_and_save "->") }
  | ":="        { COLON_ASSIGN (install_and_save ":=") }
  | "~"         { TILDE (install_and_save "~") }
  | "+"         { PLUS (install_and_save "+") }
  | "-"         { MINUS (install_and_save "-") }
  | "*"         { TIMES (install_and_save "*") }
  | "/"         { DIV (install_and_save "/") }
  | "^" | "**"  { EXP (install_and_save "^") }
  | "<"         { LT (install_and_save "<") }
  | "<="        { LE (install_and_save "<=") }
  | ">"         { GT (install_and_save ">") }
  | ">="        { GE (install_and_save ">=") }
  | "=="        { EQ (install_and_save "==") }
  | "!="        { NEQ (install_and_save "!=") }
  | "!"         { NOT (install_and_save "!") }
  | "&&"        { AND2 (install_and_save "&&") }
  | "&"         { AND (install_and_save "&") }
  | "||"        { OR2 (install_and_save "||") }
  | "|"         { OR (install_and_save "|") }
  | "$"         { DOLLAR (install_and_save "$") }
  | "@"         { AT (install_and_save "@") }
  | ":::"       { NS_GET_INT (install_and_save ":::") }
  | "::"        { NS_GET (install_and_save "::") }
  | ":"         { COLON (install_and_save ":") }

  (** ** Special Values **)
  | reg_special_operator    { SPECIAL name }
  | reg_string              { STR_CONST }
  | reg_numeric             { NUM_CONST }
  | reg_integer             { NUM_CONST }
  | reg_imaginary           { NUM_CONST }

  (** ** Parentheses **)
  | '('     { LPAR (install_and_save "(") }
  | ')'     { RPAR }
  | '{'     { LBRACE (install_and_save "{") }
  | '}'     { RBRACE }
  | "[["    { LBB (install_and_save "[[") }
  | '['     { LSQBRACKET (install_and_save "[") }
  | ']'     { RSQBRACKET }

  (** ** Miscellaneous **)
  | ('#' [^ '\n']*)? '\n'   { NEW_LINE }
  | space+                  { lex lexbuf }
  | _                       { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | eof                     { END_OF_INPUT }

