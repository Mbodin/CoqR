%{
    (** This file translates the Bison parser (main/gram.y) of R in Menhir’s syntax. **)

    open ParserUtils
    open Low.Parsing
%}

(** * Token Declaration **)

(** Some tokens have been commented out, as they only help reporting errors. **)

%token                              END_OF_INPUT (*ERROR*)
%token<ParserUtils.token_type>      STR_CONST NUM_CONST NULL_CONST SYMBOL FUNCTION
(*%token                            INCOMPLETE_STRING*)
%token<ParserUtils.token_type>      LEFT_ASSIGN EQ_ASSIGN RIGHT_ASSIGN LBB
%token<ParserUtils.token_type>      FOR IF WHILE NEXT BREAK REPEAT
%token                              IN ELSE
%token<ParserUtils.token_type>      GT GE LT LE EQ NE AND OR AND2 OR2
%token<ParserUtils.token_type>      NS_GET NS_GET_INT
(** The following commented lines are tokens never produced by the lexer,
  but changed in the parser when in a special position. We do not update
  lexemes depending in their context here. **)
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
%token<ParserUtils.token_type>      QUESTION_MARK TILDE PLUS MINUS TIMES DIV COLON EXP NOT DOLLAR AT
%token<ParserUtils.token_type>      SPECIAL
%token                              COMMA SEMICOLON
%token<string>                      NEW_LINE

(* * Precedence Table *)

(** As we explicitely manage new lines, and because they are associated with no result,
  we have to help Menhir parse it with the following arbitrary choice. **)
%left EMPTY
%left NEW_LINE

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
%left       UMINUS (*UPLUS*)
%right      EXP
%left       DOLLAR AT
%left       NS_GET NS_GET_INT
%nonassoc   LPAR LSQBRACKET LBB

%start<ParserUtils.parser_result>  main

%%

(* * Grammar *)

(** ** Some Interface **)

main:
  | cmd = NEW_LINE      { Command cmd }
  | p = prog            { Success p }
  | END_OF_INPUT        { Command "#quit" }

(** ** R Grammar **)

prog:
  (*| END_OF_INPUT                          { null }*)
  (*| NEW_LINE                              { null }*)
  | e = expr_or_assign (empty); NEW_LINE    { e }
  | e = expr_or_assign (empty); SEMICOLON   { e }
  (*| error                                 { prerr_endline "Syntax error"; null }*)

expr_or_assign (el):
  (* FIXME: If I uncomment these (*el;*) then the laws of operator priorities no longer helps Menhir. *)
  | (*el;*) e = expr (el)           { e }
  | (*el;*) e = equal_assign (el)   { e }

(* FIXME: Actually inlining the following definition makes Menhir complain. This is strange. *)
%inline expr_or_assign_cr:
  | e = expr_or_assign (cr) { e }

equal_assign (el):
  | e = expr (el); el; eq = EQ_ASSIGN; cr; a = expr_or_assign (el)  { lift3 (no_runs xxbinary) eq e a }

expr (el):
  | c = NUM_CONST                                           { c }
  | c = STR_CONST                                           { c }
  | c = NULL_CONST                                          { c }
  | c = SYMBOL                                              { c }

  | b = LBRACE; e = exprlist; RBRACE                        { lift2 (only_state xxexprlist) b e }
  | p = LPAR; e = expr_or_assign_cr; cr; RPAR               { lift2 (no_runs xxparen) p e }

  | s = MINUS; cr; e = expr (el) %prec UMINUS               { lift2 (no_runs xxunary) s e }
  | s = PLUS; cr; e = expr (el) %prec UMINUS                { lift2 (no_runs xxunary) s e }
  | s = NOT; cr; e = expr (el) %prec UNOT                   { lift2 (no_runs xxunary) s e }
  | s = TILDE; cr; e = expr (el) %prec TILDE                { lift2 (no_runs xxunary) s e }
  | s = QUESTION_MARK; cr; e = expr (el)                    { lift2 (no_runs xxunary) s e }

  | e1 = expr (el); el; op = COLON; cr; e2 = expr (el)      { lift3 (no_runs xxbinary) op e1 e2 }
  | e1 = expr (el); el; op = PLUS; cr; e2 = expr (el)       { lift3 (no_runs xxbinary) op e1 e2 }
  | e1 = expr (el); el; op = MINUS; cr; e2 = expr (el)      { lift3 (no_runs xxbinary) op e1 e2 }
  | e1 = expr (el); el; op = TIMES; cr; e2 = expr (el)      { lift3 (no_runs xxbinary) op e1 e2 }
  | e1 = expr (el); el; op = DIV; cr; e2 = expr (el)        { lift3 (no_runs xxbinary) op e1 e2 }
  | e1 = expr (el); el; op = EXP; cr; e2 = expr (el)        { lift3 (no_runs xxbinary) op e1 e2 }
  | e1 = expr (el); el; op = SPECIAL; cr; e2 = expr (el)    { lift3 (no_runs xxbinary) op e1 e2 }
  (** The lexeme '%' seems not to be produced by R’s tokenizer: the following
    (commented out) line seems to be dead code. **)
  (*| e1 = expr (el); el; op = '%'; cr; e2 = expr (el)      { lift3 (no_runs xxbinary) op e1 e2 }*)
  | e1 = expr (el); el; op = TILDE; cr; e2 = expr (el)      { lift3 (no_runs xxbinary) op e1 e2 }
  | e1 = expr (el); el; op = QUESTION_MARK; cr; e2 = expr (el)
                                                            { lift3 (no_runs xxbinary) op e1 e2 }
  | e1 = expr (el); el; op = LT; cr; e2 = expr (el)         { lift3 (no_runs xxbinary) op e1 e2 }
  | e1 = expr (el); el; op = LE; cr; e2 = expr (el)         { lift3 (no_runs xxbinary) op e1 e2 }
  | e1 = expr (el); el; op = EQ; cr; e2 = expr (el)         { lift3 (no_runs xxbinary) op e1 e2 }
  | e1 = expr (el); el; op = NE; cr; e2 = expr (el)         { lift3 (no_runs xxbinary) op e1 e2 }
  | e1 = expr (el); el; op = GE; cr; e2 = expr (el)         { lift3 (no_runs xxbinary) op e1 e2 }
  | e1 = expr (el); el; op = GT; cr; e2 = expr (el)         { lift3 (no_runs xxbinary) op e1 e2 }
  | e1 = expr (el); el; op = AND; cr; e2 = expr (el)        { lift3 (no_runs xxbinary) op e1 e2 }
  | e1 = expr (el); el; op = OR; cr; e2 = expr (el)         { lift3 (no_runs xxbinary) op e1 e2 }
  | e1 = expr (el); el; op = AND2; cr; e2 = expr (el)       { lift3 (no_runs xxbinary) op e1 e2 }
  | e1 = expr (el); el; op = OR2; cr; e2 = expr (el)        { lift3 (no_runs xxbinary) op e1 e2 }

  | e1 = expr (el); el; op = LEFT_ASSIGN; cr; e2 = expr (el)
                                                            { lift3 (no_runs xxbinary) op e1 e2 }
  | e1 = expr (el); el; op = RIGHT_ASSIGN; cr; e2 = expr (el)
                                                            { lift3 (no_runs xxbinary) op e2 e1 }
  | fname = FUNCTION; cr; LPAR; formals = formlist; RPAR; cr; body = expr_or_assign (el) %prec LOW
                                                            { lift3 (no_runs xxdefun) fname formals body }
  | e = expr (el); el; LPAR; cr; l = sublist; RPAR          { lift2 xxfuncall e l }
  | i = IF; cr; c = ifcond; cr; e = expr_or_assign (el)     { lift3 (no_runs xxif) i c e }
  | i = IF; cr; c = ifcond; cr; e1 = expr_or_assign (el); ELSE; cr; e2 = expr_or_assign (el)
                                                            { lift4 (no_runs xxifelse) i c e1 e2 }
  | f = FOR; cr; c = forcond; cr; e = expr_or_assign (el) %prec FOR
                                                            { lift3 (no_runs xxfor) f c e }
  | w = WHILE; cr; c = cond; cr; e = expr_or_assign (el)    { lift3 (no_runs xxwhile) w c e }
  | r = REPEAT; cr; e = expr_or_assign (el)                 { lift2 (no_runs xxrepeat) r e }
  | e = expr (el); el; s = LBB; cr; l = sublist; RSQBRACKET; cr; RSQBRACKET
                                                            { lift3 (no_runs xxsubscript) e s l }
  | e = expr (el); s = LSQBRACKET; cr; l = sublist; RSQBRACKET
                                                            { lift3 (no_runs xxsubscript) e s l }
  | s1 = SYMBOL; el; op = NS_GET; el; s2 = SYMBOL           { lift3 (no_runs xxbinary) op s1 s2 }
  | s1 = SYMBOL; el; op = NS_GET; el; s2 = STR_CONST        { lift3 (no_runs xxbinary) op s1 s2 }
  | s1 = STR_CONST; el; op = NS_GET; el; s2 = SYMBOL        { lift3 (no_runs xxbinary) op s1 s2 }
  | s1 = STR_CONST; el; op = NS_GET; el; s2 = STR_CONST     { lift3 (no_runs xxbinary) op s1 s2 }
  | s1 = SYMBOL; el; op = NS_GET_INT; el; s2 = SYMBOL       { lift3 (no_runs xxbinary) op s1 s2 }
  | s1 = SYMBOL; el; op = NS_GET_INT; el; s2 = STR_CONST    { lift3 (no_runs xxbinary) op s1 s2 }
  | s1 = STR_CONST; el; op = NS_GET_INT; el; s2 = SYMBOL    { lift3 (no_runs xxbinary) op s1 s2 }
  | s1 = STR_CONST; el; op = NS_GET_INT; el; s2 = STR_CONST { lift3 (no_runs xxbinary) op s1 s2 }
  | s1 = expr (el); el; op = DOLLAR; cr; s2 = SYMBOL        { lift3 (no_runs xxbinary) op s1 s2 }
  | s1 = expr (el); el; op = DOLLAR; cr; s2 = STR_CONST     { lift3 (no_runs xxbinary) op s1 s2 }
  | s1 = expr (el); el; op = AT; cr; s2 = SYMBOL            { lift3 (no_runs xxbinary) op s1 s2 }
  | s1 = expr (el); el; op = AT; cr; s2 = STR_CONST         { lift3 (no_runs xxbinary) op s1 s2 }
  | k = NEXT                                                { lift1 (no_runs xxnxtbrk) k }
  | k = BREAK                                               { lift1 (no_runs xxnxtbrk) k }

cond:
  | LPAR; e = expr (cr); cr; RPAR; cr   { lift1 (only_state xxcond) e }

ifcond:
  | LPAR; e = expr (cr); cr; RPAR; cr   { lift1 (only_state xxifcond) e }

forcond:
  | LPAR; cr; s = SYMBOL; cr; IN; e = expr (cr); cr; RPAR; cr   { lift2 (no_runs xxforcond) s e }

exprlist:
  |                                                         { no_runs xxexprlist0 }
  | e = expr_or_assign (cr)                                 { lift1 (no_runs xxexprlist1) e }
  | l = exprlist; SEMICOLON; e = expr_or_assign (cr)        { lift2 (no_runs xxexprlist2) l e }
  | l = exprlist; SEMICOLON                                 { l }
  | l = exprlist; NEW_LINE; e = expr_or_assign (cr)         { lift2 (no_runs xxexprlist2) l e }
  | l = exprlist; NEW_LINE                                  { l }

sublist:
  | s = sub                         { lift1 (no_runs xxsublist1) s }
  | sl = sublist; COMMA; s = sub    { lift2 (no_runs xxsublist2) sl s }

sub:
  | cr                                                      { no_runs xxsub0 }
  | e = expr (cr); cr                                       { lift1 xxsub1 e }
  | s = SYMBOL; cr; EQ_ASSIGN; cr                           { lift1 xxsymsub0 s }
  | s = SYMBOL; cr; EQ_ASSIGN; cr; e = expr (cr); cr        { lift2 xxsymsub1 s e }
  | str = STR_CONST; cr; EQ_ASSIGN; cr                      { lift1 xxsymsub0 str }
  | str = STR_CONST; cr; EQ_ASSIGN; cr; e = expr (cr); cr   { lift2 xxsymsub1 str e }
  | NULL_CONST; cr; EQ_ASSIGN; cr                           { xxnullsub0 }
  | NULL_CONST; cr; EQ_ASSIGN; cr; e = expr (cr); cr        { lift1 xxnullsub1 e }

formlist:
  | cr                                                      { no_runs xxnullformal }
  | cr; s = SYMBOL; cr                                      { lift1 (no_runs xxfirstformal0) s }
  | cr; s = SYMBOL; cr; EQ_ASSIGN; cr; e = expr (cr); cr    { lift2 (no_runs xxfirstformal1) s e }
  | l = formlist; COMMA; cr; s = SYMBOL; cr                 { lift2 xxaddformal0 l s }
  | l = formlist; COMMA; cr; s = SYMBOL; cr; EQ_ASSIGN; cr; e = expr (cr); cr
                                                            { lift3 xxaddformal1 l s e }

cr:
  | NEW_LINE; cr    { }
  | %prec EMPTY     { }

%inline empty:
  |                 { }

%%

