%{
    (** This file translates the Bison parser of R in Menhir’s syntax. **)

    open Low

    type token_type = globals -> runs_type -> state -> sExpRec_pointer result

    let wrap_no_globals f : token_type = fun _ -> f
    let wrap_no_runs f : token_type = fun g _ -> f g
    let wrap_only_state f : token_type = fun _ _ -> f

    (** This function is inspired from the [install_and_save] function
      * of the original interpreter. It takes into advantage the fact
      * that ocamllex is functional: its behaviour is exactly the same
      * than the install function. It here serves as a wrapper, to
      * change the order of the arguments of [install]. **)
    let install_and_save str : token_type = fun g r s ->
      install g r s (string_to_char_list str)

    (** The function [R_atof] has not been formalised. We instead rely
     * on the OCaml functions [*_of_string]. **)
    let mkFloat str : token_type = fun _ _ s ->
      let (s, e) = scalarReal s (float_of_string str) in
      Result_success (s, e)
    let mkInt str : token_type = fun _ _ s ->
      let (s, e) = scalarInteger s (int_of_string str) in
      Result_success (s, e)
    let mkComplex str : token_type = fun _ _ s ->
      let c = {
          rcomplex_r = 0. ;
          rcomplex_i = float_of_string str
        } in
      let (s, e) = alloc_vector_cplx s c in
      Result_success (s, e)
%}

%token-table

(** * Token Declaration **)

(** Some tokens have been commented out, as they only help report errors. **)

%token                  END_OF_INPUT (*ERROR*)
%token<token_type>      STR_CONST NUM_CONST NULL_CONST SYMBOL FUNCTION
(*%token                INCOMPLETE_STRING*)
%token<token_type>      LEFT_ASSIGN EQ_ASSIGN RIGHT_ASSIGN LBB
%token<token_type>      FOR IF WHILE NEXT BREAK REPEAT
%token                  IN ELSE
%token<token_type>      GT GE LT LE EQ NE AND OR AND2 OR2
%token<token_type>      NS_GET NS_GET_INT
%token      COMMENT LINE_DIRECTIVE
%token      SYMBOL_FORMALS
%token      EQ_FORMALS
%token      EQ_SUB SYMBOL_SUB
%token      SYMBOL_FUNCTION_CALL
%token      SYMBOL_PACKAGE
%token      COLON_ASSIGN
%token      SLOT

(** These are additional tokens, directly used as characters in gran.y. **)

%token<token_type>      LBRACE LPAR LSQBRACKET
%token                  RBRACE RPAR RSQBRACKET
%token<token_type>      QUESTION_MARK TILDE PLUS MINUS TIMES DIV COLON EXP DOLLAR AT
%token<char list>       SPECIAL
%token                  COMMA SEMICOLON NEW_LINE

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

%%

(* * Grammar *)

prog: END_OF_INPUT              { YYACCEPT; }
    | NEW_LINE                  { yyresult = xxvalue(NULL,2,NULL); goto yyreturn; }
    | expr_or_assign NEW_LINE   { yyresult = xxvalue($1,3,&@1); goto yyreturn; }
    | expr_or_assign SEMICOLON  { yyresult = xxvalue($1,4,&@1); goto yyreturn; }
    | error                     { YYABORT; }
    ;

expr_or_assign: expr         { $$ = $1; }
              | equal_assign { $$ = $1; }
              ;

equal_assign: expr EQ_ASSIGN expr_or_assign { $$ = xxbinary($2,$1,$3); }
            ;

expr: NUM_CONST                 { $$ = $1; setId( $$, @$); }
    | STR_CONST                 { $$ = $1; setId( $$, @$); }
    | NULL_CONST                { $$ = $1; setId( $$, @$); }
    | SYMBOL                    { $$ = $1; setId( $$, @$); }

    | LBRACE exprlist RBRACE    { $$ = xxexprlist($1,&@1,$2); setId( $$, @$); }
    | LPAR expr_or_assign RPAR  { $$ = xxparen($1,$2); setId( $$, @$); }

    | MINUS expr %prec UMINUS   { $$ = xxunary($1,$2); setId( $$, @$); }
    | PLUS expr %prec UMINUS    { $$ = xxunary($1,$2); setId( $$, @$); }
    | NOT expr %prec UNOT       { $$ = xxunary($1,$2); setId( $$, @$); }
    | TILDE expr %prec TILDE    { $$ = xxunary($1,$2); setId( $$, @$); }
    | QUESTION_MARK expr        { $$ = xxunary($1,$2); setId( $$, @$); }

    | expr COLON  expr          { $$ = xxbinary($2,$1,$3); setId( $$, @$); }
    | expr PLUS  expr           { $$ = xxbinary($2,$1,$3); setId( $$, @$); }
    | expr MINUS expr           { $$ = xxbinary($2,$1,$3); setId( $$, @$); }
    | expr TIMES expr           { $$ = xxbinary($2,$1,$3); setId( $$, @$); }
    | expr DIV expr             { $$ = xxbinary($2,$1,$3); setId( $$, @$); }
    | expr EXP expr             { $$ = xxbinary($2,$1,$3); setId( $$, @$); }
    | expr SPECIAL expr         { $$ = xxbinary($2,$1,$3); setId( $$, @$); }
    (** The lexeme '%' seems not to be produced by R’s tokenizer: the following
     * (commented out) line seems to be dead code. **)
    (*| expr '%' expr           { $$ = xxbinary($2,$1,$3); setId( $$, @$); }*)
    | expr TILDE expr           { $$ = xxbinary($2,$1,$3); setId( $$, @$); }
    | expr QUESTION_MARK expr   { $$ = xxbinary($2,$1,$3); setId( $$, @$); }
    | expr LT expr              { $$ = xxbinary($2,$1,$3); setId( $$, @$); }
    | expr LE expr              { $$ = xxbinary($2,$1,$3); setId( $$, @$); }
    | expr EQ expr              { $$ = xxbinary($2,$1,$3); setId( $$, @$); }
    | expr NE expr              { $$ = xxbinary($2,$1,$3); setId( $$, @$); }
    | expr GE expr              { $$ = xxbinary($2,$1,$3); setId( $$, @$); }
    | expr GT expr              { $$ = xxbinary($2,$1,$3); setId( $$, @$); }
    | expr AND expr             { $$ = xxbinary($2,$1,$3); setId( $$, @$); }
    | expr OR expr              { $$ = xxbinary($2,$1,$3); setId( $$, @$); }
    | expr AND2 expr            { $$ = xxbinary($2,$1,$3); setId( $$, @$); }
    | expr OR2 expr             { $$ = xxbinary($2,$1,$3); setId( $$, @$); }

    | expr LEFT_ASSIGN expr     { $$ = xxbinary($2,$1,$3); setId( $$, @$); }
    | expr RIGHT_ASSIGN expr    { $$ = xxbinary($2,$3,$1); setId( $$, @$); }
    | FUNCTION LPAR formlist RPAR cr expr_or_assign %prec LOW
                                { $$ = xxdefun($1,$3,$6,&@$); setId( $$, @$); }
    | expr LPAR sublist RPAR    { $$ = xxfuncall($1,$3); setId( $$, @$); modif_token( &@1, SYMBOL_FUNCTION_CALL ) ; }
    | IF ifcond expr_or_assign  { $$ = xxif($1,$2,$3); setId( $$, @$); }
    | IF ifcond expr_or_assign ELSE expr_or_assign
                                { $$ = xxifelse($1,$2,$3,$5); setId( $$, @$); }
    | FOR forcond expr_or_assign %prec FOR
                                { $$ = xxfor($1,$2,$3); setId( $$, @$); }
    | WHILE cond expr_or_assign { $$ = xxwhile($1,$2,$3); setId( $$, @$); }
    | REPEAT expr_or_assign     { $$ = xxrepeat($1,$2); setId( $$, @$); }
    | expr LBB sublist RSQBRACKET RSQBRACKET
                                { $$ = xxsubscript($1,$2,$3); setId( $$, @$); }
    | expr LSQBRACKET sublist RSQBRACKET
                                { $$ = xxsubscript($1,$2,$3); setId( $$, @$); }
    | SYMBOL NS_GET SYMBOL      { $$ = xxbinary($2,$1,$3); setId( $$, @$); modif_token( &@1, SYMBOL_PACKAGE ) ; }
    | SYMBOL NS_GET STR_CONST   { $$ = xxbinary($2,$1,$3); setId( $$, @$); modif_token( &@1, SYMBOL_PACKAGE ) ; }
    | STR_CONST NS_GET SYMBOL   { $$ = xxbinary($2,$1,$3); setId( $$, @$); }
    | STR_CONST NS_GET STR_CONST
                                { $$ = xxbinary($2,$1,$3); setId( $$, @$); }
    | SYMBOL NS_GET_INT SYMBOL  { $$ = xxbinary($2,$1,$3); setId( $$, @$); modif_token( &@1, SYMBOL_PACKAGE ) ;}
    | SYMBOL NS_GET_INT STR_CONST
                                { $$ = xxbinary($2,$1,$3); setId( $$, @$); modif_token( &@1, SYMBOL_PACKAGE ) ;}
    | STR_CONST NS_GET_INT SYMBOL
                                { $$ = xxbinary($2,$1,$3); setId( $$, @$); }
    | STR_CONST NS_GET_INT STR_CONST
                                { $$ = xxbinary($2,$1,$3); setId( $$, @$); }
    | expr DOLLAR SYMBOL        { $$ = xxbinary($2,$1,$3); setId( $$, @$); }
    | expr DOLLAR STR_CONST     { $$ = xxbinary($2,$1,$3); setId( $$, @$); }
    | expr AT SYMBOL            { $$ = xxbinary($2,$1,$3); setId( $$, @$); modif_token( &@3, SLOT ) ; }
    | expr AT STR_CONST         { $$ = xxbinary($2,$1,$3); setId( $$, @$); }
    | NEXT                      { $$ = xxnxtbrk($1); setId( $$, @$); }
    | BREAK                     { $$ = xxnxtbrk($1); setId( $$, @$); }
    ;

cond: LPAR expr RPAR    { $$ = xxcond($2); }
    ;

ifcond: LPAR expr RPAR  { $$ = xxifcond($2); }
      ;

forcond: LPAR SYMBOL IN expr RPAR   { $$ = xxforcond($2,$4); setId( $$, @$); }
       ;


exprlist:                                   { $$ = xxexprlist0(); setId( $$, @$); }
        | expr_or_assign                    { $$ = xxexprlist1($1, &@1); }
        | exprlist SEMICOLON expr_or_assign { $$ = xxexprlist2($1, $3, &@3); }
        | exprlist SEMICOLON                { $$ = $1; setId( $$, @$); }
        | exprlist NEW_LINE expr_or_assign  { $$ = xxexprlist2($1, $3, &@3); }
        | exprlist NEW_LINE                 { $$ = $1;}
        ;

sublist: sub                    { $$ = xxsublist1($1); }
       | sublist cr COMMA sub   { $$ = xxsublist2($1,$4); }
       ;

sub:                            { $$ = xxsub0(); }
   | expr                       { $$ = xxsub1($1, &@1); }
   | SYMBOL EQ_ASSIGN           { $$ = xxsymsub0($1, &@1); modif_token( &@2, EQ_SUB ) ; modif_token( &@1, SYMBOL_SUB ) ; }
   | SYMBOL EQ_ASSIGN expr      { $$ = xxsymsub1($1,$3, &@1); modif_token( &@2, EQ_SUB ) ; modif_token( &@1, SYMBOL_SUB ) ; }
   | STR_CONST EQ_ASSIGN        { $$ = xxsymsub0($1, &@1); modif_token( &@2, EQ_SUB ) ; }
   | STR_CONST EQ_ASSIGN expr   { $$ = xxsymsub1($1,$3, &@1); modif_token( &@2, EQ_SUB ) ; }
   | NULL_CONST EQ_ASSIGN       { $$ = xxnullsub0(&@1); modif_token( &@2, EQ_SUB ) ; }
   | NULL_CONST EQ_ASSIGN expr  { $$ = xxnullsub1($3, &@1); modif_token( &@2, EQ_SUB ) ; }
   ;

formlist:                           { $$ = xxnullformal(); }
        | SYMBOL                    { $$ = xxfirstformal0($1); modif_token( &@1, SYMBOL_FORMALS ) ; }
        | SYMBOL EQ_ASSIGN expr     { $$ = xxfirstformal1($1,$3); modif_token( &@1, SYMBOL_FORMALS ) ; modif_token( &@2, EQ_FORMALS ) ; }
        | formlist COMMA SYMBOL     { $$ = xxaddformal0($1,$3, &@3); modif_token( &@3, SYMBOL_FORMALS ) ; }
        | formlist COMMA SYMBOL EQ_ASSIGN expr
                                    { $$ = xxaddformal1($1,$3,$5,&@3); modif_token( &@3, SYMBOL_FORMALS ) ; modif_token( &@4, EQ_FORMALS ) ;}
        ;

cr: { EatLines = 1; }
  ;

%%

