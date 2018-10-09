exception EmptyInput

type termType =
	| TypeInt
	| TypeBool
	(* T1 -> T2 *)
	| TypeFunc of termType * termType

(* 			+	   -	   *	   / 	  <	   <=	=	 <=	  >=   >	*)
type op = Plus | Minus | Times | Divide | LT | LE | EQ | NE | GE | GT

type term =
	| Int of int
	| Bool of bool
	| If of term * term * term
	| Op of op * term * term
	| Id of string
	| Apply of term * term
	| Fn of string * termType * term
	| Let of string * termType * term * term
	| LetRec of string * termType * term * term

	(* >> Structs for evaluation << *)
	| Closure of string * term * environment
	| RecClosure of string * string * term * environment
	(* Cyclic type declaration *)
	and environment = (string * term) list

(* > Compilation *)
type inst =
    | INT of int
    | BOOL of bool
    | POP
    | COPY
    | INV
    | ADD
    | SUB
    | MULT
    | DIV
    | NE
    | EQ
    | GT
    | GE
    | LE
    | LT
    | AND
    | OR
    | NOT
    | JUMP of int
    | JUMPIFTRUE of int
    | VAR of string
    | APPLY
    | FUN of string * code
    | RFUN of string * string * code
    (* Cyclic type declaration *)
    and code = inst list

type sv =
    | Int of int
    | Bool of bool
    | Clos of env * string * code
    | RClos of env * string * string * code
    and env = (string * sv) list

type stack = sv list
type dump = (code * stack * env) list
type state = code * stack * env * dump