{
    open Parser

    (** This file mainly translates Function [yylex] from File gram.y. **)
}

rule yylex_start = parse
  | '\n'
    { yylex_newline lexbuf }
  | ['+' '-' '*' '/' '^'] (* What about LT, LE, GE, etc. that come afterwards? *)
    { yylex_eatline lexbuf }


(* TODO: Read 10.1 “The parsing process” of R-lang.pdf *)

