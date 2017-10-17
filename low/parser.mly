%{
    (** This file translates the Bison parser of R in Menhir’s syntax. **)

    open ParserUtils
%}

%token-table

(** * Token Declaration **)

(** Some tokens have been commented out, as they only help report errors. **)

%token                              END_OF_INPUT (*ERROR*)
%token<ParserUtils.token_type>      STR_CONST NUM_CONST NULL_CONST SYMBOL FUNCTION
(*%token                            INCOMPLETE_STRING*)
%token<ParserUtils.token_type>      LEFT_ASSIGN EQ_ASSIGN RIGHT_ASSIGN LBB
%token<ParserUtils.token_type>      FOR IF WHILE NEXT BREAK REPEAT
%token                              IN ELSE
%token<ParserUtils.token_type>      GT GE LT LE EQ NE AND OR AND2 OR2
%token<ParserUtils.token_type>      NS_GET NS_GET_INT
(** The following commented lines are tokens never produced by the lexer,
 * but changed in the parser when in a special position. We do not update
 * lexemes depending in their context here. **)
(*%token                            COMMENT LINE_DIRECTIVE*)
(*%token                            SYMBOL_FORMALS*)
(*%token                            EQ_FORMALS*)
(*%token                            EQ_SUB SYMBOL_SUB*)
(*%token                            SYMBOL_FUNCTION_CALL*)
(*%token                            SYMBOL_PACKAGE*)
(*%token                            SLOT*)
(*%token                            COLON_ASSIGN*)

(** These are additional tokens, directly used as characters in gran.y. **)

%token<ParserUtils.token_type>      LBRACE LPAR LSQBRACKET
%token                              RBRACE RPAR RSQBRACKET
%token<ParserUtils.token_type>      QUESTION_MARK TILDE PLUS MINUS TIMES DIV COLON EXP DOLLAR AT
%token<char list>                   SPECIAL
%token                              COMMA SEMICOLON NEW_LINE

(* * Precedence Table *)

%left       QUESTION_MARK
%left       LOW WHILE FOR REPEAT
%right      IF
%left       ELSE
%right      LEFT_ASSIGN
%right      EQ_ASSIGN
%left       RIGHT_ASSIGN
%left       TILDE
%left       OR OR2
%left       AND AND2
%left       UNOT NOT
%nonassoc   GT GE LT LE EQ NE
%left       PLUS MINUS
%left       TIMES DIV
%left       SPECIAL
%left       COLON
%left       UMINUS UPLUS
%right      EXP
%left       DOLLAR AT
%left       NS_GET NS_GET_INT
%nonassoc   LPAR LSQBRACKET LBB

%start<ParserUtils.token_type>  prog

%%

(* * Grammar *)

prog:
  | END_OF_INPUT                   { null }
  | NEW_LINE                       { null }
  | e = expr_or_assign; NEW_LINE   { e }
  | e = expr_or_assign; SEMICOLON  { e }
  | error                          { prerr_endline "Syntax error"; null }

expr_or_assign:
  | e = expr         { e }
  | e = equal_assign { e }

equal_assign:
  | e = expr; eq = EQ_ASSIGN; a = expr_or_assign { lift3 xxbinary eq e a }

expr:
  | c = NUM_CONST                                { c }
  | c = STR_CONST                                { c }
  | c = NULL_CONST                               { c }
  | c = SYMBOL                                   { c }

  | b = LBRACE; e = exprlist; RBRACE             { lift2 xxexprlist b e }
  | p = LPAR; e = expr_or_assign; RPAR           { lift2 xxparen p e }

  | s = MINUS; e = expr %prec UMINUS             { lift2 xxunary s e }
  | s = PLUS; e = expr %prec UMINUS              { lift2 xxunary s e }
  | s = NOT; e = expr %prec UNOT                 { lift2 xxunary s e }
  | s = TILDE; e = expr %prec TILDE              { lift2 xxunary s e }
  | s = QUESTION_MARK; e = expr                  { lift2 xxunary s e }

  | e1 = expr; op = COLON; e2 = expr             { lift3 xxbinary op e1 e2 }
  | e1 = expr; op = PLUS; e2 = expr              { lift3 xxbinary op e1 e2 }
  | e1 = expr; op = MINUS; e2 = expr             { lift3 xxbinary op e1 e2 }
  | e1 = expr; op = TIMES; e2 = expr             { lift3 xxbinary op e1 e2 }
  | e1 = expr; op = DIV; e2 = expr               { lift3 xxbinary op e1 e2 }
  | e1 = expr; op = EXP; e2 = expr               { lift3 xxbinary op e1 e2 }
  | e1 = expr; op = SPECIAL; e2 = expr           { lift3 xxbinary op e1 e2 }
  (** The lexeme '%' seems not to be produced by R’s tokenizer: the following
   * (commented out) line seems to be dead code. **)
  (*| e1 = expr; op = '%'; e2 = expr             { lift3 xxbinary op e1 e2 }*)
  | e1 = expr; op = TILDE; e2 = expr             { lift3 xxbinary op e1 e2 }
  | e1 = expr; op = QUESTION_MARK; e2 = expr     { lift3 xxbinary op e1 e2 }
  | e1 = expr; op = LT; e2 = expr                { lift3 xxbinary op e1 e2 }
  | e1 = expr; op = LE; e2 = expr                { lift3 xxbinary op e1 e2 }
  | e1 = expr; op = EQ; e2 = expr                { lift3 xxbinary op e1 e2 }
  | e1 = expr; op = NE; e2 = expr                { lift3 xxbinary op e1 e2 }
  | e1 = expr; op = GE; e2 = expr                { lift3 xxbinary op e1 e2 }
  | e1 = expr; op = GT; e2 = expr                { lift3 xxbinary op e1 e2 }
  | e1 = expr; op = AND; e2 = expr               { lift3 xxbinary op e1 e2 }
  | e1 = expr; op = OR; e2 = expr                { lift3 xxbinary op e1 e2 }
  | e1 = expr; op = AND2; e2 = expr              { lift3 xxbinary op e1 e2 }
  | e1 = expr; op = OR2; e2 = expr               { lift3 xxbinary op e1 e2 }

  | e1 = expr; op = LEFT_ASSIGN; e2 = expr       { lift3 xxbinary op e1 e2 }
  | e1 = expr; op = RIGHT_ASSIGN; e2 = expr      { lift3 xxbinary op e2 e1 }
  | fname = FUNCTION; LPAR; formals = formlist; RPAR; cr; body = expr_or_assign %prec LOW
                                                 { lift3 xxdefun fname formals body }
  | e = expr; LPAR; l = sublist; RPAR            { lift2 xxfuncall e l }
  | i = IF; c = ifcond; e = expr_or_assign       { lift3 xxif i c e }
  | i = IF; c = ifcond; e1 = expr_or_assign; ELSE; e2 = expr_or_assign
                                                 { lift4 xxifelse i c e1 e2 }
  | f = FOR; c = forcond; e = expr_or_assign %prec FOR
                                                 { lift3 xxfor f x e }
  | w = WHILE; c = cond; e = expr_or_assign      { lift3 xxwhile w c e }
  | r = REPEAT; e = expr_or_assign               { lift2 xxrepeat r e }
  | e = expr; s = LBB; l = sublist; RSQBRACKET; RSQBRACKET
                                                 { lift3 xxsubscript e s l }
  | e = expr; s = LSQBRACKET; l = sublist; RSQBRACKET
                                                 { lift3 xxsubscript e s l }
  | s1 = SYMBOL; op = NS_GET; s2 = SYMBOL        { lift3 xxbinary op s1 s2 }
  | s1 = SYMBOL; op = NS_GET; s2 = STR_CONST     { lift3 xxbinary op s1 s2 }
  | s1 = STR_CONST; op = NS_GET; s2 = SYMBOL     { lift3 xxbinary op s1 s2 }
  | s1 = STR_CONST; op = NS_GET; s2 = STR_CONST  { lift3 xxbinary op s1 s2 }
  | s1 = SYMBOL; op = NS_GET_INT; s2 = SYMBOL    { lift3 xxbinary op s1 s2 }
  | s1 = SYMBOL; op = NS_GET_INT; s2 = STR_CONST { lift3 xxbinary op s1 s2 }
  | s1 = STR_CONST; op = NS_GET_INT; s2 = SYMBOL { lift3 xxbinary op s1 s2 }
  | s1 = STR_CONST; op = NS_GET_INT; s2 = STR_CONST
                                                 { lift3 xxbinary op s1 s2 }
  | s1 = expr; op = DOLLAR; s2 = SYMBOL          { lift3 xxbinary op s1 s2 }
  | s1 = expr; op = DOLLAR; s2 = STR_CONST       { lift3 xxbinary op s1 s2 }
  | s1 = expr; op = AT; s2 = SYMBOL              { lift3 xxbinary op s1 s2 }
  | s1 = expr; op = AT; s2 = STR_CONST           { lift3 xxbinary op s1 s2 }
  | k = NEXT                                     { lift1 xxnxtbrk k }
  | k = BREAK                                    { lift1 xxnxtbrk k }

cond:
  | LPAR; e = expr; RPAR    { lift1 xxcond e }

ifcond:
  | LPAR; e = expr; RPAR    { lift1 xxcond e }

forcond:
  | LPAR; s = SYMBOL; IN; e = expr; RPAR   { lift2 xxforcond s e }

exprlist:
  |                                   { $$ = xxexprlist0(); setId( $$, @$); }
  | expr_or_assign                    { $$ = xxexprlist1($1, &@1); }
  | exprlist SEMICOLON expr_or_assign { $$ = xxexprlist2($1, $3, &@3); }
  | exprlist SEMICOLON                { $$ = $1; setId( $$, @$); }
  | exprlist NEW_LINE expr_or_assign  { $$ = xxexprlist2($1, $3, &@3); }
  | exprlist NEW_LINE                 { $$ = $1;}

sublist:
  | sub                    { $$ = xxsublist1($1); }
  | sublist cr COMMA sub   { $$ = xxsublist2($1,$4); }

sub:
  |                            { $$ = xxsub0(); }
  | expr                       { $$ = xxsub1($1, &@1); }
  | SYMBOL EQ_ASSIGN           { $$ = xxsymsub0($1, &@1); modif_token( &@2, EQ_SUB ) ; modif_token( &@1, SYMBOL_SUB ) ; }
  | SYMBOL EQ_ASSIGN expr      { $$ = xxsymsub1($1,$3, &@1); modif_token( &@2, EQ_SUB ) ; modif_token( &@1, SYMBOL_SUB ) ; }
  | STR_CONST EQ_ASSIGN        { $$ = xxsymsub0($1, &@1); modif_token( &@2, EQ_SUB ) ; }
  | STR_CONST EQ_ASSIGN expr   { $$ = xxsymsub1($1,$3, &@1); modif_token( &@2, EQ_SUB ) ; }
  | NULL_CONST EQ_ASSIGN       { $$ = xxnullsub0(&@1); modif_token( &@2, EQ_SUB ) ; }
  | NULL_CONST EQ_ASSIGN expr  { $$ = xxnullsub1($3, &@1); modif_token( &@2, EQ_SUB ) ; }

formlist:
  |                           { $$ = xxnullformal(); }
  | SYMBOL                    { $$ = xxfirstformal0($1); modif_token( &@1, SYMBOL_FORMALS ) ; }
  | SYMBOL EQ_ASSIGN expr     { $$ = xxfirstformal1($1,$3); modif_token( &@1, SYMBOL_FORMALS ) ; modif_token( &@2, EQ_FORMALS ) ; }
  | formlist COMMA SYMBOL     { $$ = xxaddformal0($1,$3, &@3); modif_token( &@3, SYMBOL_FORMALS ) ; }
  | formlist COMMA SYMBOL EQ_ASSIGN expr
                              { $$ = xxaddformal1($1,$3,$5,&@3); modif_token( &@3, SYMBOL_FORMALS ) ; modif_token( &@4, EQ_FORMALS ) ;}

cr:
  |     { EatLines = 1; }

%%

