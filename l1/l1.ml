open Types

(* - Map list *)
exception NotFound of string

let mapList_hasKey mapList key = match mapList with
    | [] -> false
    | h::t ->
        List.exists (fun (k, _) -> k = key) mapList

let mapList_removeKey mapList key =
    List.filter (fun (k, _) -> k <> key) mapList

let mapList_setKey mapList key value = match mapList with
    | [] -> [(key, value)]
    | h::t ->
	    if (mapList_hasKey mapList key)
        then List.append (mapList_removeKey mapList key) [(key, value)]
        else List.append mapList [(key, value)]

let rec mapList_getKey mapList key = match mapList with
  | [] -> raise (NotFound(key))
  | (k, v)::t ->
	if (k = key)
	then v
	else mapList_getKey t key

let mapList_print mapList printFn =
    let rec printElements = function
        | [] -> ()
        | (k, v)::t ->
            print_string (k ^ ": " ^ (printFn v) ^ ", ");
            printElements t
    in
        print_string "{ ";
        printElements mapList;
        print_string "}\n"

(* > Types inferance *)
exception UndeclaredId of string
exception TypeMismatch

let typesTable = [];;

(* val typeToString : termType -> string *)
let rec typeToString (t: termType) : string = match t with
    | TypeBool -> "Bool"
    | TypeInt -> "Int"
    | TypeFunc(t1,t2) -> 
        let t1' = typeToString t1 and
            t2' = typeToString t2 in
            "(" ^ t1' ^ ", " ^ t2' ^ ")"

(* val printTypesTable : (string * termType) list) -> unit *)
let printTypesTable table : unit =
    mapList_print table typeToString

(* val typesTableHasId : (string * termType) list) -> string -> bool *)
let typesTableHasId table (id: string) : bool = 
    mapList_hasKey table id;;

(* val removeFromTypesTable : (string * termType) list) -> string -> (string * type) *)
let removeFromTypesTable table (id: string) : (string * termType) list =
    mapList_removeKey table id

(* val updateTypesTable : (string * termType) list -> string -> termType -> (string * termType) list *)
let updateTypesTable table (id: string) (idType: termType) : (string * termType) list = 
    mapList_setKey table id idType;;

(* val lookupTypesTable : (string * termType) list -> string -> termType *)
let rec lookupTypesTable table (id: string) : termType =
    try mapList_getKey table id
    with NotFound(k) -> raise (UndeclaredId(k));;

(* val typeInfer : (string * termType) list -> term -> termType *)
let rec typeInfer (tTable: (string * termType) list) (t: term) : termType = match t with
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

let rec countOccurrences (v: string) (t: term) (c: int) : int =
    match t with
    | Int(n) -> c
    | Bool(b) -> c
    | Id(x) ->
        if x = v
        then (c + 1)
        else c
    | Op(op, e1, e2) ->
        let c1 = countOccurrences v e1 0 and
            c2 = countOccurrences v e2 0 in
            (c + c1 + c2)
    | If (e1, e2, e3) ->
        let c1 = countOccurrences v e1 0 and
            c2 = countOccurrences v e2 0 and
            c3 = countOccurrences v e3 0 in
            (c + c1 + c2 + c3)
    | Fn(x, t, e) ->
        if x = v
        then c  (* new scope -> ignore occurrences *)
        else 
            let c1 = countOccurrences v e 0 in
                (c + c1)
    | Apply(e1, e2) ->
        let c1 = countOccurrences v e1 0 and
            c2 = countOccurrences v e2 0 in
            (c + c1 + c2)
    | Let(x, t, e1, e2) ->
        let c2 = countOccurrences v e2 0 in
            if x = v
            then (c + c2)  (* new scope -> ignore occurrences *)
            else
                let c1 = countOccurrences v e1 0 in
                    (c + c1 + c2)
    | LetRec(f, t1, e1, e2) ->
        let c2 = countOccurrences v e2 0 in
            if f = v
            then (c + c2)  (* new scope -> ignore occurrences *)
            else
                let c1 = countOccurrences v e1 0 in
                    (c + c1 + c2)
    | _ -> c


(* val opToString : op -> string *)
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

(* val termToString : term -> string *)
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

(* val envHasKey : environment -> string -> bool *)
let envHasKey (env: environment) (key: string): bool =
     mapList_hasKey env key

(* val updateEnv : environment -> string -> term -> (string * term) list *)
let updateEnv env (key: string) value =
    mapList_setKey env key value

(* val lookupEnv : environment -> string -> term *)
let lookupEnv env (key: string) =
    mapList_getKey env key

(* val printEnv : environment -> unit *)
let printEnv (env: environment) : unit =
    mapList_print env termToString

(* val eval : environmnet -> term -> int -> term * int *)
let rec eval (env: environment) (t: term) (q: int) : term * int =
    match t with
    (* Int *)
    | Int(n) -> (Int(n), q)
    (* Bool *)
    | Bool(b) -> (Bool(b), q)
    (* Id *)
    | Id(x) ->
        let q' = q + 1 in
            (lookupEnv env x, q')
    (* Op *)
    | Op(op, e1, e2) ->
        let v1 = eval env e1 0 and
            v2 = eval env e2 0 in
        let q1 = snd v1 and
            q2 = snd v2 in
        let q' = (q + 1 + q1 + q2) and
            e' : Types.term = match op, fst v1, fst v2 with
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
                | _ -> raise (EvalError("Unrecognized op"))
                in
                    (e', q')
    (* If *)
    | If (e1, e2, e3) ->
        let e1' = eval env e1 0 in
        let v1 = fst e1' and
            q1 = snd e1' in
        let q' = q + 1 + q1 in
            (match v1 with
                | Bool(true) -> eval env e2 q'
                | Bool(false) -> eval env e3 q'
                | t' -> raise (EvalError("Expected bool, got: " ^ (termToString t'))))
    (* Fn *)
    | Fn(x, t, e) ->
        let q' = q + 1 in    
            (Closure(x, e, env), q')
    (* Apply *)
    | Apply(e1, e2) ->
        let e1' = eval env e1 0 and
            e2' = eval env e2 0 in
        let v1 = fst e1' and
            v2 = fst e2' and
            q1 = snd e1' and
            q2 = snd e2' in
            (match v1 with
                (* Clousure *)
                | Closure(x, e, env') ->
                    let q' = q + 1 + q1 + q2 and
                        env1 = updateEnv env' x v2 in 
                        eval env1 e q'
                (* RecClousure *)
                | RecClosure(f, x, e, env') ->
                    let q' = q + 1 + q1 + q2 and
                        env1 = updateEnv env' x v2 and
                        rC = RecClosure(f, x, e, env') in
                    let env2 = updateEnv env1 f rC in
                        eval env2 e q'
                | _ -> raise (EvalError "Apply: expected Clousure"))
    (* Let *)
    | Let(x, t, e1, e2) ->
        let e1' = eval env e1 0 in
        let v1 = fst e1' and
            q1 = snd e1' in
        let env' = updateEnv env x v1 in
        let q' = q + 1 + q1 in
            eval env' e2 q'
    (* LetRec *)
    | LetRec(f, t1, Fn(x, t2, e1), e2) ->
        let q' = q + 1 and
            rC = RecClosure(f, x, e1, env) in
        let env' = updateEnv env f rC in
            eval env' e2 q'
    (* Error *)
    | t' -> raise (EvalError("Unrecognized term: " ^ (termToString t')))


(* Compilation *)
exception CompilationError of string
exception CodeEvalError of string
exception DropFailure

(* val instToString : inst -> string *)
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

(* val printCode : code -> unit *)
let rec printCode (l: code) = match l with
    | [] -> ()
    | h::t ->
        print_endline (instToString h);
        printCode t

(* val svToString : sv -> string *)
let svToString (sv: sv) : string = match sv with
	| Int(n) -> string_of_int n
	| Bool(b) -> string_of_bool b
	| Clos(e, x, c) -> "<clos " ^ x ^ ">"
	| RClos(e, f, x, c) -> "<rclos " ^ f ^ ":" ^ x ^ ">"

(* val printOutputState : state -> unit *)
let printOutputState (st: state) : unit = match st with
	| (c, s, e, d) ->
		let sv = List.hd s in
      print_endline (svToString sv)
     
(* val comp : term -> code *)
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

(* val codeDrop : code -> int -> code *)
let rec codeDrop (c: code) (n: int) : code = match c with
    | [] -> 
        if n = 0
        then []
        else raise DropFailure
    | h::t ->
        if n > 0
        then codeDrop t (n-1)
        else c

(* val codeEval : state -> int -> state * int *)
let rec codeEval (state: state) (q: int) : state * int =
    let q' = q + 1 in
    (match state with
        (* End of code *)
        | ([], s, e, d) ->
            let sv = List.hd s in
                (match d with
                    (* Empty Dump *)
                    | [] -> (([], [sv], e, []), q')
                    (* Non-Empty Dump *)
                    | (c', s', e')::d' -> codeEval (c', sv::s', e', d') q'
                )
        (* INT *)
        | (INT(n)::c', s, e, d) ->
            codeEval (c', Int(n)::s, e, d) q'
        (* BOOL *)
        | (BOOL(b)::c', s, e, d) ->
            codeEval (c', Bool(b)::s, e, d) q'
        (* POP *)
        | (POP::c', s, e, d) ->
            codeEval (c', s, e, d) q'
        (* COPY *)
        | (COPY::c', s, e, d) ->
            let sv = List.hd s in	
                codeEval (c', sv::s, e, d) q'
        (* ADD *)
        | (ADD::c', Int(n1)::Int(n2)::s', e, d)  ->
            codeEval (c', Int(n1+n2)::s', e, d) q'
        (* SUB *)
        | (SUB::c', Int(n1)::Int(n2)::s', e, d) ->
            codeEval (c', Int(n1-n2)::s', e, d) q'
        (* MULT *)
        | (MULT::c', Int(n1)::Int(n2)::s', e, d) ->
            codeEval (c', Int(n1*n2)::s', e, d) q'
        (* DIV *)
        | (DIV::c', Int(n1)::Int(n2)::s', e, d) ->
            codeEval (c', Int(n1/n2)::s', e, d) q'
        (* INV *)
        | (INV::c', Int(n)::s', e, d) ->
            codeEval (c', Int(-n)::s', e, d) q'
        (* EQ *)
        | (EQ::c', Int(n1)::Int(n2)::s', e, d) ->
            if (n1 = n2)
            then codeEval (c', Bool(true)::s', e, d) q'
            else codeEval (c', Bool(false)::s', e, d) q'
        (* NE *)
        | (NE::c', Int(n1)::Int(n2)::s', e, d) ->
            if (n1 <> n2)
            then codeEval (c', Bool(true)::s', e, d) q'
            else codeEval (c', Bool(false)::s', e, d) q'
        (* GT *)
        | (GT::c', Int(n1)::Int(n2)::s', e, d) ->
            if (n1 > n2)
            then codeEval (c', Bool(true)::s', e, d) q'
            else codeEval (c', Bool(false)::s', e, d) q'
        (* GE *)
        | (GE::c', Int(n1)::Int(n2)::s', e, d) ->
            if (n1 >= n2)
            then codeEval (c', Bool(true)::s', e, d) q'
            else codeEval (c', Bool(false)::s', e, d) q'
        (* LE *)
        | (LE::c', Int(n1)::Int(n2)::s', e, d) ->
            if (n1 <= n2)
            then codeEval (c', Bool(true)::s', e, d) q'
            else codeEval (c', Bool(false)::s', e, d) q'
        (* LT *)
        | (LT::c', Int(n1)::Int(n2)::s', e, d) ->
            if (n1 < n2)
            then codeEval (c', Bool(true)::s', e, d) q'
            else codeEval (c', Bool(false)::s', e, d) q'
        (* AND *)
        | (AND::c', s, e, d) ->
            (match s with
                | Bool(false)::Bool(b)::s' -> codeEval (c', Bool(false)::s', e, d) q'
                | Bool(true)::Bool(b)::s' -> codeEval (c', Bool(b)::s', e, d) q'
                | _ -> raise (CodeEvalError "AND"))
        (* OR *)
        | (OR::c', s, e, d) ->
                (match s with
                    | Bool(true)::Bool(b)::s' -> codeEval (c', Bool(true)::s', e, d) q'
                    | Bool(false)::Bool(b)::s' -> codeEval (c', Bool(b)::s', e, d) q'
                    | _ -> raise (CodeEvalError "OR"))
        (* NOT *)
        | (NOT::c', Bool(b)::s', e, d) ->
            codeEval (c', Bool(not b)::s', e, d) q'
        (* JUMP *)
        | (JUMP(n)::c', s, e, d) ->
            codeEval ((codeDrop c' n), s, e, d) q'
        (* JUMPIFTRUE *)
        | (JUMPIFTRUE(n)::c', Bool(b)::s', e, d) ->
            if (b)
            then codeEval ((codeDrop c' n), s', e, d) q'
            else codeEval (c', s', e, d) q'
        (* VAR *)
        | (VAR(x)::c', s, e, d) ->
            let v = (lookupEnv e x) in
                codeEval (c', v::s, e, d) q'
        (* FUN *)
        | (FUN(x, fc)::c', s, e, d) ->
            codeEval (c', Clos(e, x, fc)::s, e, d) q'
        (* RFUN *)
        | (RFUN(f, x, fc)::c', s, e, d) ->
            codeEval (c', RClos(e, f, x, fc)::s, e, d) q'
        (* APPLY *)
        | (APPLY::c', s, e, d) ->
            (match s with
                | Clos(e', x, fc)::sv::s' ->
                    let cEnv = updateEnv e' x sv in
                        codeEval (fc, [], cEnv, (c', s', e)::d) q'
                | RClos(e', f, x, fc)::sv::s' ->
                    let cEnv = updateEnv e' x sv in
                    let cEnv' = updateEnv cEnv f (RClos(e', f, x, fc)) in
                        codeEval (fc, [], cEnv', (c', s', e)::d) q'
                | _ -> raise (CodeEvalError "APPLY"))
        | (inst::c', _, _, _) -> raise (CodeEvalError (instToString inst)) )

(* TESTS *)

let run (t: term) : unit =
	print_endline "> Input";
	print_endline (termToString t);
	print_string "> Output type: ";
    print_endline (typeToString (typeInfer typesTable t));
    let evalRes = eval emptyEnv t 0 in
    let t' = fst evalRes and
        q = snd evalRes in
        print_endline ("> Output value: " ^ (termToString t'));
        print_endline ("> Cost: " ^ (string_of_int q))
;;

let runComp (t: term) : unit  = 
	print_endline "> Input";
	print_endline (termToString t);
	print_string "> Output type: ";
	print_endline (typeToString (typeInfer typesTable t));
    print_endline "> Code:";
	let code = comp t in
        printCode code;
        let evalRes = codeEval (code, [], [], []) 0 in
        let s' = fst evalRes and
            q = snd evalRes in
            print_string "> Output value: ";
            printOutputState s';
            print_endline ("> Cost: " ^ (string_of_int q))
;;

let _ =
	try 
		let lexbuf = Lexing.from_channel stdin in
		let inputTerm = Parser.main Lexer.token lexbuf in
			run inputTerm
	with 
		| Parsing.Parse_error ->
			print_endline "Syntax error"
		| EmptyInput ->
			print_endline "Empty input"