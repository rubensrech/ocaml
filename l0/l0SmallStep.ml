(* Gramatica: t ::= true | false | if(t1,t2,t3) | 0 | succ(t) | pred(t) | iszero(t) *)
(* Small step *)

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

let rec toString t = match t with
	| TmTrue -> "true"
	| TmFalse -> "false"
	| TmZero -> "0"
	| TmIf(t1,t2,t3) ->
		"if (" ^ toString t1 ^ ") then (" ^ toString t2 ^ ") else (" ^ toString t3 ^ ")"
	| TmSucc(t1) ->
		"succ(" ^ toString t1 ^ ")"
	| TmPred(t1) ->
		"pred(" ^ toString t1 ^ ")"
	| TmIsZero(t1) ->
		"isZero(" ^ toString t1 ^ ")"
	
let printTerm t = 
	print_endline (toString t);;

(* Excecao a ser ativada quando termo for uma FORMA NORMAL *)
exception NoRuleApplies
(* Excecao a ser ativada quando houver ERRO DE TIPOS *)
exception TypeMismatch

(* Funcao auxiliar para determinar se um termo e um VALOR NUMERICO *)
let rec isNumericVal t = match t with
	| TmZero -> true
	| TmSucc(t1) -> isNumericVal t1
	| _ -> false;;

(* Implementacao da funcao STEP de avaliacao em um passo *)
let rec step t = match t with
	(* IF *)
	| TmIf(TmTrue,t2,t3) -> t2 		(* E-IF-TRUE *)
	| TmIf(TmFalse,t2,t3) -> t3 	(* E-IF-FALSE *)
	| TmIf(t1,t2,t3) -> 					(* E−IF *)
		let t1' = step t1 in
		TmIf(t1',t2,t3)
	(* SUCC *)
	| TmSucc(t1) -> 							(* E-SUCC *)
		let t1' = step t1 in
		TmSucc(t1')
	(* PRED *)
	| TmPred(TmZero) -> TmZero		(* E-PRED-ZERO *)
	| TmPred(TmSucc(nv1)) when		(* E-PRED-SUCC *)
		(isNumericVal nv1) -> nv1 
	| TmPred(t1) -> 							(* E-PRED *)
		let t1' = step t1 in
		TmPred(t1')
	(* ISZERO *)
	| TmIsZero(TmZero) -> TmTrue	(* E-IS-ZERO-ZERO *)
	| TmIsZero(TmSucc(nv1)) when	(* E-IS-ZERO-SUCC *)
		(isNumericVal nv1) -> TmFalse
	| TmIsZero(t1) ->							(* E-IS-ZERO *)
		let t1' = step t1 in
		TmIsZero(t1')
	(* ELSE *)
	| _ -> raise NoRuleApplies;;

(* Implementacao de EVAL *)
let rec eval t =
	try 
		let t' = step t in
		eval t'
	with NoRuleApplies -> t;;

let rec typeInfer t = match t with
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
	| _ -> raise TypeMismatch;;

(* ASTs para teste *)
let t1 = TmIsZero(TmZero);;
let t2 = TmZero;;
let t3 = TmSucc(TmZero);;
let tif = TmIf(t1,t2,t3);;
let t4 = TmIsZero(TmSucc(TmZero));;
let t5 = TmIsZero(tif);;

let te1 = TmIsZero(TmIsZero(TmZero));;
let te2 = TmIsZero(TmFalse);;

let inputTerm = t1;;
print_endline ("Input: " ^ (toString inputTerm));;
typeInfer inputTerm;;
print_endline "Type infer succeeded";;
printTerm (eval inputTerm);;