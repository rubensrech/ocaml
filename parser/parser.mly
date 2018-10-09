%{
    open Types
%}

%token <int> INT
%token PLUS MINUS TIMES DIVIDE
%token LT LE EQ NE GE GT
%token TRUE FALSE
%token IF THEN ELSE
%token FN COLON RD_ARROW
%token LET REC IN RS_ARROW
%token TYPE_INT TYPE_BOOL
%token LPAREN RPAREN
%token <string> ID
%token EOF

/* Associativity and Precedence */
%left EQ NE
%left LT GT LE GE
%right THEN ELSE
%left PLUS MINUS
%left TIMES DIVIDE
%left RS_ARROW RD_ARROW
%left exp
%right TYPE_INT TYPE_BOOL
%nonassoc COLON IN TRUE FALSE INT IF ID FN LET REC LPAREN RPAREN

%start main             /* the entry point */

%type <Types.term> main
%type <Types.op> op
%type <Types.termType> e_type
%type <Types.term> e_if
%type <Types.term> e_fn
%type <Types.term> e_let
%type <Types.term> e_let_rec
%type <Types.term> expr

%%

main:
      expr EOF              { $1 }
    | EOF                   { raise EmptyInput }    

op:
      PLUS                  { Plus }
    | MINUS                 { Minus }
    | TIMES                 { Times }
    | LT                    { LT }
    | LE                    { LE }
    | EQ                    { EQ }
    | NE                    { NE }
    | GE                    { GE }
    | GT                    { GT };

e_type:
      TYPE_INT                          { TypeInt }
    | TYPE_BOOL                         { TypeBool }
    | e_type RS_ARROW e_type            { TypeFunc($1, $3) }
    | LPAREN e_type RPAREN              { $2 };

e_if:
    IF expr THEN expr ELSE expr         { If($2, $4, $6) };

e_fn:
    FN ID COLON e_type RD_ARROW expr    { Fn($2, $4, $6) };

e_let:
    LET ID COLON e_type EQ expr IN expr { Let($2, $4, $6, $8) };

e_let_rec:
    LET REC ID COLON e_type EQ LPAREN e_fn RPAREN IN expr   { LetRec($3, $5, $8, $11) };

expr:
      INT                       { Int($1) }
    | TRUE                      { Bool(true) }
    | FALSE                     { Bool(false) }
    | LPAREN expr RPAREN        { $2 }
    | expr op expr %prec exp    { Op($2, $1, $3) }
    | e_if                      { $1 }
    | ID                        { Id($1) }
    | expr expr %prec exp       { Apply($1, $2) }
    | e_fn                      { $1 }
    | e_let                     { $1 }
    | e_let_rec                 { $1 };