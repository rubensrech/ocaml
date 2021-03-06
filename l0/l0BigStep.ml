(* Gramatica: t ::= true | false | if(t1,t2,t3) | 0 | succ(t) | pred(t) | iszero(t) *)
(* Big step *)

type term =
	| TmTrue
	| TmFalse
	| TmZero
	| TmIf of term * term * term
	| TmSucc of term
	| TmPred of term
	| TmIsZero of term
  
type termType =
	| TypeBool
	| TypeNat

type inst =
	| Push of int
	| Pop
	| Copy
	| Inc
	| Dec
	| Jump of int
	| JmpIfZero of int

type code = inst list
type stack = int list

(* Printing functions *)
let typeToString (t: termType) : string = match t with
	| TypeBool -> "bool"
	| TypeNat -> "int"

let rec termToString (t: term) : string = match t with
	| TmTrue -> "true"
	| TmFalse -> "false"
	| TmZero -> "0"
	| TmIf(t1,t2,t3) ->
		"if (" ^ termToString t1 ^ ") then (" ^ termToString t2 ^ ") else (" ^ termToString t3 ^ ")"
	| TmSucc(t1) ->
		"succ(" ^ termToString t1 ^ ")"
	| TmPred(t1) ->
		"pred(" ^ termToString t1 ^ ")"
	| TmIsZero(t1) ->
		"isZero(" ^ termToString t1 ^ ")"

let rec instToString (i: inst) : string = match i with
	| Push(n) -> "PUSH " ^ (string_of_int n)
	| Pop -> "POP"
	| Copy -> "COPY"
	| Inc -> "INC"
	| Dec -> "DEC"
	| Jump(n) -> "JUMP " ^ (string_of_int n)
	| JmpIfZero(n) -> 	"JMPIFZERO " ^ (string_of_int n)

let rec printCode (l: code) = match l with
	| [] -> ()
	| h::t ->
		print_endline (instToString h);
		printCode t

let rec printStack (s: stack) = match s with
	| [] -> ()
	| h::t ->
		print_endline (string_of_int h);
		printStack t

(* Excecao a ser ativada quando houver ERRO DE AVALIÇÃO *)
exception NoRuleApplies
(* Excecao a ser ativada quando houver ERRO DE TIPOS *)
exception TypeMismatch
(* Excecao a ser ativada quando nao houver n elementos em listDrop l n *)
exception DropFailure

(* Auxiliary functions *)
let rec listDrop (l: code) (n: int) : code = match l with
	| [] -> 
		if n = 0
		then []
		else raise DropFailure
	| h::t ->
		if n > 0
		then listDrop t (n-1)
		else l
		
let rec isNumericalVal (t: term) : bool = match t with
	| TmZero -> true
	| TmSucc(t1) -> isNumericalVal t1
	| _ -> false

(* Main functions *)
let rec eval (t: term) (q: int) : term * int =
    let q' = q + 1 in
    (match t with
	| TmTrue -> (TmTrue, q)
	| TmFalse -> (TmFalse, q)
	| TmZero -> (TmZero, q)
	| TmIf(t1,t2,t3) ->
		(match (eval t1 q') with
			| (TmTrue, q1) -> eval t2 q1
			| (TmFalse, q1) -> eval t3 q1
			| _ -> raise NoRuleApplies)
	| TmSucc(t1) ->
        (match eval t1 q' with
            | (t1', q1) ->
                if (isNumericalVal t1')
                then (TmSucc(t1'), q1)
                else raise NoRuleApplies)
	| TmPred(t1) ->
		(match eval t1 q' with
			| (TmZero, q1) -> (TmZero, q1)
            | (TmSucc(t1'), q1) when (isNumericalVal t1') ->
                (t1', q1)
			| _ -> raise NoRuleApplies)
	| TmIsZero(t1) ->
		(match eval t1 q' with
			| (TmZero, q1) -> (TmTrue, q1)
            | (TmSucc(t1'), q1) when (isNumericalVal t1') ->
                (TmFalse, q1)
            | _ -> raise NoRuleApplies)
    )

let rec typeInfer (t: term) : termType = match t with
	| TmTrue -> TypeBool			(* regra T-TRUE *)
	| TmFalse -> TypeBool			(* regra T-FALSE *)
	| TmZero -> TypeNat				(* regra T-ZERO *)
	| TmPred(t1) when 				(* regra T-PRED *)
		(typeInfer t1) = TypeNat
		-> TypeNat
	| TmSucc(t1) when 				(* regra T-SUCC *)
		(typeInfer t1) = TypeNat
		-> TypeNat
	| TmIsZero(t1) when				(* regra T-IS-ZERO *)
		(typeInfer t1) = TypeNat
		-> TypeBool
	| TmIf(t1,t2,t3) when			(* regra T-IF *)
		(typeInfer t1) = TypeBool ->
		let t2Type = typeInfer t2 and
			t3Type = typeInfer t3 in
			if (t2Type = t3Type)
			then t2Type
			else (raise TypeMismatch)
	| _ -> raise TypeMismatch

let rec comp (t: term) : code = match t with
	| TmTrue -> [Push(1)]
	| TmFalse -> [Push(0)]
	| TmZero -> [Push(0)]
	| TmSucc(t1) -> List.append (comp t1) [Inc]
	| TmIf(t1,t2,t3) ->
		let n2 = List.length (comp t2) and
			n3 = List.length (comp t3) in
			let l1 = List.append (comp t1) [JmpIfZero((n2+1))] in
			let l2 = List.append l1 (comp t2) in
			let l3 = List.append l2 [Jump(n3)] in
				List.append l3 (comp t3)
	| TmIsZero(t1) ->
		List.append (comp t1) [JmpIfZero(2); Push(0); Jump(1); Push(1)]
	| TmPred(t1) ->
		List.append (comp t1) [Copy; JmpIfZero(1); Dec]


let rec evalCode (c: code) (s: stack) (q: int) : code * stack * int = match c with
	| [] -> (c, s, q)
    | i::c' ->
        let q' = q + 1 in
		(match i with
			| Push(n) -> evalCode c' (n::s) q'
			| Pop -> evalCode c' s q'
			| Copy -> 
				let hd = List.hd s in
					evalCode c' (hd::s) q'
			| Inc ->
				let hd = List.hd s and
					tl = List.tl s in
					evalCode c' ((hd+1)::tl) q'
			| Dec ->
				let hd = List.hd s and
					tl = List.tl s in
				    evalCode c' ((hd-1)::tl) q'
			| Jump(n) -> evalCode (listDrop c' n) s q'
			| JmpIfZero(n) ->
				let hd = List.hd s and
					tl = List.tl s in
					if hd = 0
					then evalCode (listDrop c' n) tl q'
                    else evalCode c' tl q'
        )

let evalStart (t: term) = 
	print_string "> Input: ";
	print_endline (termToString t);
	print_string "> Output type: ";
	print_endline (typeToString (typeInfer t))

(* Testing functions *)

let bigStepEval (t: term) =
	evalStart t;
    let s = eval t 0 in
        (match s with
            | (t1, q) ->
                print_endline ("> Output value: " ^ (termToString t1));
                print_endline ("> Cost: " ^ (string_of_int q))
        )
	    

let compEval (t: term) =
	evalStart t;
	let code = comp t in
		print_endline "----- Code -----";
		printCode code;
		print_endline "----- Stack -----";
		match (evalCode code [] 0) with
            | (code, stack, q) ->
                print_endline ("Cost: " ^ (string_of_int q));
				printStack stack


(* ASTs para teste *)
let t1 = TmIsZero(TmZero);;
let t2 = TmZero;;
let t3 = TmSucc(TmZero);;
let tif = TmIf(t1,t2,t3);;
let t4 = TmIsZero(TmSucc(TmZero));;
let t5 = TmIsZero(tif);;

bigStepEval tif