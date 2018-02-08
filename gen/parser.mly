
%token                      EOF
%token<Structures.arrow>    ARROW
%token<string>              STRING IDENTIFIER
%token                      SEMICOLON

%start<Structures.rule list> main

%%

llist (st):
  | s = st ; l = llist (st) { s :: l }
  |                         { [] }

main:
  | l = llist (rule) ; EOF  { l }

rule:
  | i = IDENTIFIER ; a = ARROW ; l = llist (token) ; SEMICOLON  { (i, a, l) }

token:
  | s = STRING      { Structures.Str s }
  | i = IDENTIFIER  { Structures.Id i }

