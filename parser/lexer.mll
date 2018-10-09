{
    open Parser        (* The type token is defined in parser.mli *)
    exception Eof
}
rule token = parse
      [' ' '\t']            { token lexbuf }     (* skip blanks *)
    | ['\n']                { token lexbuf }

    | ['0'-'9']+ as lxm     { INT(int_of_string lxm) }

    | '+'                   { PLUS }
    | '-'                   { MINUS }
    | '*'                   { TIMES }
    | '/'                   { DIVIDE }
    | '<'                   { LT }
    | "<="                  { LE }
    | '='                   { EQ }
    | "!="                  { NE }
    | '>'                   { GT }
    | ">="                  { GE }

    | "true"                { TRUE }
    | "false"               { FALSE }

    | "if"                  { IF }
    | "then"                { THEN }
    | "else"                { ELSE }

    | "fn"                  { FN }
    | ":"                   { COLON }
    | "=>"                  { RD_ARROW }

    | "let"                 { LET }
    | "rec"                 { REC }
    | "in"                  { IN }
    | "->"                  { RS_ARROW }

    | "int"                 { TYPE_INT }
    | "bool"                { TYPE_BOOL }

    | '('                   { LPAREN }
    | ')'                   { RPAREN }

    | ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '0'-'9' '_']* as id { ID(id) }

    | eof                   { EOF }