open Types

(* - Map list *)
exception NotFound of string

let mapList_hasKey mapList key = match mapList with
  | [] -> false
  | h::t ->
	List.exists (fun (k, _) -> k = key) mapList;;

let mapList_removeKey mapList key =
  List.filter (fun (k, _) -> k <> key) mapList;;

let mapList_setKey mapList key value = match mapList with
  | [] -> [(key, value)]
  | h::t ->
	if (mapList_hasKey mapList key)
	then List.append (mapList_removeKey mapList key) [(key, value)]
	else List.append mapList [(key, value)];;

let rec mapList_getKey mapList key = match mapList with
  | [] -> raise (NotFound(key))
  | (k, v)::t ->
	if (k = key)
	then v
	else mapList_getKey t key;;

let mapList_print mapList printFn =
  let rec printElements = function
	| [] -> ()
	| (k, v)::t ->
	  print_string (k ^ ": " ^ (printFn v) ^ ", ");
	  printElements t
  in
  print_string "{ ";
  printElements mapList;
  print_string "}\n";;

(* > Types inferance *)
exception UndeclaredId of string
exception TypeMismatch

let typesTable = [];;

let rec typeToString (t: termType) : string = match t with
  | TypeBool -> "Bool"
  | TypeInt -> "Int"
  | TypeFunc(t1,t2) -> 
	let t1' = typeToString t1 and
	  t2' = typeToString t2 in
	  "(" ^ t1' ^ ", " ^ t2' ^ ")";;

let printTypesTable table =
  mapList_print table typeToString

let typesTableHasId table id = 
  mapList_hasKey table id;;

let removeFromTypesTable table (id: string) =
  mapList_removeKey table id

let updateTypesTable table (id: string) (idType: termType) = 
  mapList_setKey table id idType;;

let rec lookupTypesTable table (id: string) =
  try mapList_getKey table id
  with NotFound(k) -> raise (UndeclaredId(k));;

let rec typeInfer tTable (t: term) : termType = match t with
  | Int(n) -> TypeInt
  | Bool(b) -> TypeBool
  | Op(op, e1, e2) when
	(typeInfer tTable e1) = TypeInt &&
	(typeInfer tTable e2) = TypeInt ->
	  (match op with
		| Plus -> TypeInt
		| Minus -> TypeInt
		| Times -> TypeInt
		| Divide -> TypeInt
		| _ -> TypeBool)
  | If(e1, e2, e3) when
	  (typeInfer tTable e1) = TypeBool ->
	  let e2Type = (typeInfer tTable e2) and
		  e3Type = (typeInfer tTable e3) in
		  if e2Type = e3Type
		  then e2Type
		  else (raise TypeMismatch)
  | Id(x) -> lookupTypesTable tTable x
  | Fn(x, t, e) ->
	let tTable' = updateTypesTable tTable x t in
	  let eType = typeInfer tTable' e in
		TypeFunc(t, eType)
  | Apply(e1, e2) ->
	(match (typeInfer tTable e1) with
	  | TypeFunc(t1, t2) when
		(t1 = (typeInfer tTable e2))
		-> t2
	  | _ -> raise TypeMismatch)	
  | Let(x, t, e1, e2) when
	(typeInfer tTable e1) = t ->
	  let tTable' = updateTypesTable tTable x t in
		(typeInfer tTable' e2)
  | LetRec(f, TypeFunc(t1, t2), Fn(x, t, e1), e2)
	when t1 = t ->
	  let tTable1 = updateTypesTable tTable f (TypeFunc(t1,t2)) in
		let tTable2 = updateTypesTable tTable1 x t1 in
		  if ((typeInfer tTable2 e1) <> t2)
		  then raise TypeMismatch;
		typeInfer tTable1 e2
  | _ -> raise TypeMismatch

(* > Evaluation *)
exception EvalError of string

let emptyEnv: environment = [];;

let opToString (op: op) : string = match op with
  | Plus -> "+"
  | Minus -> "-"
  | Times -> "*"
  | Divide -> "/"
  | LT -> "<"
  | LE -> "<="
  | EQ -> "="
  | NE -> "!="
  | GE -> ">="
  | GT -> ">"

let rec termToString (t: term) : string = match t with
  | Int(n) -> string_of_int n
  | Bool(false) -> "false"
  | Bool(true) -> "true"
  | If(e1, e2, e3) -> "if (" ^ (termToString e1) ^ ")\n  then (" ^ (termToString e2) ^ ")\n  else (" ^ (termToString e3) ^ ")"
  | Op(op, e1, e2) -> (termToString e1) ^ " " ^ (opToString op)  ^  " " ^ (termToString e2)
  | Id(x) -> x
  | Apply(e1, e2) -> (termToString e1) ^ " " ^ (termToString e2)
  | Fn(x, t, e) -> "(fn " ^ x ^ " =>\n  " ^ (termToString e) ^ ")"
  | Let(x, t, e1, e2) -> "let " ^ x ^ " = " ^ (termToString e1) ^ " in\n" ^ (termToString e2)
  | LetRec(f, t, e1, e2) -> "let rec " ^ f ^ " = " ^ (termToString e1) ^ " in\n" ^ (termToString e2)
  | Closure(x, e, env) -> "<closure: " ^ x ^ ">"
  | RecClosure(f, x, e, env) -> "<closure " ^ f ^ " : " ^ x ^ ">"

let envHasKey (env: environment) (key: string): bool =
  mapList_hasKey env key

let updateEnv env (key: string) value =
  mapList_setKey env key value

let lookupEnv env (key: string) =
  mapList_getKey env key
let printEnv (env: environment) =
  mapList_print env termToString

let rec eval (env: environment) (t: term) : term = match t with
  | Int(n) -> Int(n)
  | Bool(b) -> Bool(b)
  | Id(x) -> lookupEnv env x
  | Op(op, e1, e2) ->
	let v1 = eval env e1 and
	  v2 = eval env e2 in
	  (match op, v1, v2 with
		(* Arithmetic *)
		| Plus, Int(n1), Int(n2) -> Int(n1 + n2)
		| Minus, Int(n1), Int(n2) -> Int(n1 - n2)
		| Times, Int(n1), Int(n2) -> Int(n1 * n2)
		| Divide, Int(n1), Int(n2) -> Int(n1 / n2)
		(* Logic *)
		| LT, Int(n1), Int(n2) -> Bool(n1 < n2)
		| LE, Int(n1), Int(n2) -> Bool(n1 <= n2)
		| EQ, Int(n1), Int(n2) -> Bool(n1 = n2)
		| NE, Int(n1), Int(n2) -> Bool(n1 <> n2)
		| GE, Int(n1), Int(n2) -> Bool(n1 >= n2)
		| GT, Int(n1), Int(n2) -> Bool(n1 > n2)
		| _ -> raise (EvalError("Unrecognized op")))
  | If(e1, e2, e3) when
	(eval env e1) = Bool(true)
	-> eval env e2
  | If(e1, e2, e3) when
	(eval env e1) = Bool(false)
	-> eval env e3
  | Fn(x, t, e) -> Closure(x, e, env)
  | Apply(e1, e2) ->
	(match (eval env e1) with
	  | Closure(x, e, env') ->
		let v' = eval env e2 in
		  let env1 = updateEnv env' x v' in 
			eval env1 e
	  | RecClosure(f, x, e, env') ->
		let v' = eval env e2 in
		  let env1 = updateEnv env' x v' and
			rC = RecClosure(f, x, e, env') in
			let env2 = updateEnv env1 f rC in
			  eval env2 e
	  | _ -> raise (EvalError "Apply: expected Clousure"))
  | Let(x, t, e1, e2) ->
	let v' = eval env e1 in
	  let env' = updateEnv env x v' in
		eval env' e2
  | LetRec(f, t1, Fn(x, t2, e1), e2) ->
	let rC = RecClosure(f, x, e1, env) in
	  let env' = updateEnv env f rC in
		eval env' e2
  | t' -> raise (EvalError("Unrecognized term: " ^ (termToString t')))


(* Compilation *)
exception CompilationError of string
exception CodeEvalError of string
exception DropFailure

let rec instToString (i: inst) : string =
	let rec codeToStr (c: code) = match c with
		| [] -> ""
		| h::t ->
			(instToString h) ^ "\n" ^ (codeToStr t)
	in 
		(match i with
		| INT(n) -> "INT " ^ (string_of_int n)
		| BOOL(b) -> "BOOL " ^ (string_of_bool b)
		| POP -> "POP"
		| COPY -> "COPY"
		| INV -> "INV"
		| ADD -> "ADD"
		| SUB -> "SUB"
		| MULT -> "MULT"
		| DIV -> "DIV"
		| NE -> "NE"
		| EQ -> "EQ"
		| GT -> "GT"
		| GE -> "GE"
		| LE -> "LE"
		| LT -> "LT"
		| AND -> "AND"
		| OR -> "OR"
		| NOT -> "NOT"
		| JUMP(n) -> "JUMP " ^ (string_of_int n)
		| JUMPIFTRUE(n)-> "JUMPIFTRUE " ^ (string_of_int n)
		| VAR(x) -> "VAR " ^ x
		| APPLY -> "APPLY"
		| FUN(x, c) -> "---------\nFUN " ^ x ^ "\n" ^ (codeToStr c) ^ "---------"
		| RFUN(f, x, c) -> "---------\nRFUN " ^ f ^ ", " ^ x ^ "\n" ^ (codeToStr c) ^ "---------")

let rec printCode (l: code) = match l with
  | [] -> ()
  | h::t ->
	print_endline (instToString h);
	printCode t

let svToString (sv: sv) : string = match sv with
	| Int(n) -> string_of_int n
	| Bool(b) -> string_of_bool b
	| Clos(e, x, c) -> "<clos " ^ x ^ ">"
	| RClos(e, f, x, c) -> "<rclos " ^ f ^ ":" ^ x ^ ">"

let printOutputState (st: state) = match st with
	| (c, s, e, d) ->
		let sv = List.hd s in
      print_endline (svToString sv)
      
let rec comp (t: term) : code = match t with
	| Int(n) -> [INT(n)]
	| Bool(b) -> [BOOL(b)]
	| Op(op, e1, e2) ->
		let c = List.append (comp e2) (comp e1) in
			(match op with
				| Plus -> List.append c [ADD]
				| Minus -> List.append c [SUB]
				| Times -> List.append c [MULT]
				| Divide -> List.append c [DIV]
				| LT -> List.append c [LT]
				| LE -> List.append c [LE]
				| EQ -> List.append c [EQ]
				| NE -> List.append c [NE]
				| GE -> List.append c [GE]
				| GT -> List.append c [GT])
	| If(e1, e2, e3) ->
		let e2c = (comp e2) and
			e3c = (comp e3) in
		let n2 = List.length e2c and
			n3 = List.length e3c in
		let c1 = List.append (comp e1) [JUMPIFTRUE(n3+1)] in
		let c2 = List.append c1 e3c in
		let c3 = List.append c2 [JUMP(n2)] in
			List.append c3 e2c
	| Id(x) -> [VAR(x)]
	| Apply(e1, e2) ->
		let c = List.append (comp e2) (comp e1) in
			List.append c [APPLY]
	| Fn(x, t, e) -> [FUN(x, (comp e))]
	| Let(y, t, e1, e2) ->
		let c = List.append (comp e1) [FUN(y, (comp e2))] in
			List.append c [APPLY]
	| LetRec(f, t1, Fn(y, t2, e1), e2) ->
		[RFUN(f, y, (comp e1)) ; FUN(f, (comp e2)) ; APPLY]
  | t' -> raise (CompilationError("Unrecognized term: " ^ (termToString t')))
  
let rec codeDrop (c: code) (n: int) : code = match c with
  | [] -> 
	if n = 0
	then []
	else raise DropFailure
  | h::t ->
	if n > 0
	then codeDrop t (n-1)
	else c

let rec codeEval (state: state) : state = match state with
  | (c, s, e, d) ->
  (match c with
	| [] ->
	  let sv = List.hd s in
	  (match d with
		| [] -> ([], [sv], e, [])
		| (c', s', e')::d' -> codeEval (c', sv::s', e', d'))
	| INT(n)::c' -> codeEval (c', Int(n)::s, e, d)
	| BOOL(b)::c' -> codeEval (c', Bool(b)::s, e, d)
	| POP::c' -> codeEval (c', s, e, d)
	| COPY::c' ->
	  let sv = List.hd s in	
		codeEval (c', sv::s, e, d)
	| ADD::c' ->
	  (match s with
		| Int(n1)::Int(n2)::s' -> codeEval (c', Int(n1+n2)::s', e, d)
		| _ -> raise (CodeEvalError "ADD"))
	| SUB::c' ->
	  (match s with
		| Int(n1)::Int(n2)::s' -> codeEval (c', Int(n1-n2)::s', e, d)
		| _ -> raise (CodeEvalError "SUB"))
	| MULT::c' ->
	  (match s with
		| Int(n1)::Int(n2)::s' -> codeEval (c', Int(n1*n2)::s', e, d)
		| _ -> raise (CodeEvalError "MULT"))
	| DIV::c' ->
	  (match s with
		| Int(n1)::Int(n2)::s' -> codeEval (c', Int(n1/n2)::s', e, d)
		| _ -> raise (CodeEvalError "DIV"))
	| INV::c' ->
	  (match s with
		| Int(n)::s' -> codeEval (c', Int(-n)::s', e, d)
		| _ -> raise (CodeEvalError "INV"))
	| EQ::c' ->
	  (match s with
		| Int(n1)::Int(n2)::s' ->
		  if (n1 = n2)
		  then codeEval (c', Bool(true)::s', e, d)
		  else codeEval (c', Bool(false)::s', e, d)
		| _ -> raise (CodeEvalError "EQ"))
	| NE::c' ->
	  (match s with
		| Int(n1)::Int(n2)::s' ->
		  if (n1 <> n2)
		  then codeEval (c', Bool(true)::s', e, d)
		  else codeEval (c', Bool(false)::s', e, d)
		| _ -> raise (CodeEvalError "NE"))
	| GT::c' ->
	  (match s with
		| Int(n1)::Int(n2)::s' ->
		  if (n1 > n2)
		  then codeEval (c', Bool(true)::s', e, d)
		  else codeEval (c', Bool(false)::s', e, d)
		| _ -> raise (CodeEvalError "GT"))
	| GE::c' ->
	  (match s with
		| Int(n1)::Int(n2)::s' ->
		  if (n1 >= n2)
		  then codeEval (c', Bool(true)::s', e, d)
		  else codeEval (c', Bool(false)::s', e, d)
		| _ -> raise (CodeEvalError "GE"))
	| LE::c' ->
	  (match s with
		| Int(n1)::Int(n2)::s' ->
		  if (n1 <= n2)
		  then codeEval (c', Bool(true)::s', e, d)
		  else codeEval (c', Bool(false)::s', e, d)
		| _ -> raise (CodeEvalError "LE"))
	| LT::c' ->
	  (match s with
		| Int(n1)::Int(n2)::s' ->
		  if (n1 < n2)
		  then codeEval (c', Bool(true)::s', e, d)
		  else codeEval (c', Bool(false)::s', e, d)
		| _ -> raise (CodeEvalError "LT"))
	| AND::c' ->
	  (match s with
		| Bool(false)::Bool(b)::s' -> codeEval (c', Bool(false)::s', e, d)
		| Bool(true)::Bool(b)::s' -> codeEval (c', Bool(b)::s', e, d)
		| _ -> raise (CodeEvalError "AND"))
	| OR::c' ->
	  (match s with
		| Bool(true)::Bool(b)::s' -> codeEval (c', Bool(true)::s', e, d)
		| Bool(false)::Bool(b)::s' -> codeEval (c', Bool(b)::s', e, d)
		| _ -> raise (CodeEvalError "OR"))
	| NOT::c' ->
	  (match s with
		| Bool(b)::s' -> codeEval (c', Bool(not b)::s', e, d)
		| _ -> raise (CodeEvalError "NOT"))
	| JUMP(n)::c' -> codeEval ((codeDrop c' n), s, e, d)
	| JUMPIFTRUE(n)::c' ->
	  (match s with
		| Bool(b)::s' ->
		  if (b)
		  then codeEval ((codeDrop c' n), s', e, d)
		  else codeEval (c', s', e, d)
		| _ -> raise (CodeEvalError "JUMPIFTRUE"))
	| VAR(x)::c' ->
	  let v = (lookupEnv e x) in
		codeEval (c', v::s, e, d)
	| FUN(x, fc)::c' -> codeEval (c', Clos(e, x, fc)::s, e, d)
	| RFUN(f, x, fc)::c' -> codeEval (c', RClos(e, f, x, fc)::s, e, d)
	| APPLY::c' ->
	  (match s with
		| Clos(e', x, fc)::sv::s' ->
		  let cEnv = updateEnv e' x sv in
			codeEval (fc, [], cEnv, (c', s', e)::d)
		| RClos(e', f, x, fc)::sv::s' ->
		  let cEnv = updateEnv e' x sv in
		  let cEnv' = updateEnv cEnv f (RClos(e', f, x, fc)) in
			codeEval (fc, [], cEnv', (c', s', e)::d)
		| _ -> raise (CodeEvalError "APPLY"))
	)

(* TESTS *)

let run (t: term) =
	print_endline "> Input";
	print_endline (termToString t);
	print_string "> Output type: ";
	print_endline (typeToString (typeInfer typesTable t));
	print_endline ("> Output value: " ^ (termToString (eval emptyEnv t)))
;;

let runComp (t: term)  = 
	print_endline "> Input";
	print_endline (termToString t);
	print_string "> Output type: ";
	print_endline (typeToString (typeInfer typesTable t));
  print_endline "> Code:";
	let code = comp t in
			printCode code;
			print_string "> Output value: ";
			printOutputState (codeEval (code, [], [], []))
;;

let _ =
	try 
		let lexbuf = Lexing.from_channel stdin in
		let inputTerm = Parser.main Lexer.token lexbuf in
			runComp inputTerm
	with 
		| Parsing.Parse_error ->
			print_endline "Syntax error"
		| EmptyInput ->
			print_endline "Empty input"