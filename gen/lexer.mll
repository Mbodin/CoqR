{

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

