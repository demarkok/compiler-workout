open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let rec eval env conf = function
 	| [] -> conf
 	| (instr :: rest) -> match instr with
		| LABEL _ -> eval env conf rest
		| JMP label -> eval env conf (env#labeled label)
		| CJMP (c, label) ->
			let ((h :: tail), sConf) = conf in
			let toEval = if (h = 0 && c = "z" || h != 0 && c = "nz") then env#labeled label else rest in
			eval env (tail, sConf) toEval
		| BINOP _ | CONST _ | WRITE | READ | LD _ | ST _ ->
			let nconf = (match (conf, instr) with
				| (fst :: snd :: tail, ((state, _, _) as sConf)), (BINOP op) ->
			    let res = (Language.Expr.eval state (Language.Expr.Binop (op, Language.Expr.Const snd, Language.Expr.Const fst))) in
			    ((res :: tail), sConf)
			  | (stack, sConf), (CONST c) ->
			    (c :: stack, sConf)
			  | (fst :: tail, (state, inp, out)), WRITE ->
			    (tail, (state, inp, out @ [fst]))
			  | (stack, (state, (z :: inpTail), out)), READ ->
			    (z :: stack, (state, inpTail, out))
			  | (stack, ((state, _, _) as sConf)), (LD var) ->
			    (state var :: stack, sConf)
			  | ((fst :: tail), (state, inp, out)), (ST var) ->
			    (tail, (Language.Expr.update var fst state, inp, out)))
			in eval env nconf rest


(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o


let nameGenerator = object
	val mutable suffix = 0
	method getName = 
		suffix <- (suffix + 1);
		(Printf.sprintf "label_%d" suffix)
end 


(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
let rec compile stmt =
  let rec exprCompile expr = match expr with
  | Language.Expr.Const c -> [CONST c]
  | Language.Expr.Var var -> [LD var]
  | Language.Expr.Binop (op, e1, e2) -> exprCompile e1 @ exprCompile e2 @ [BINOP op]
  in
  match stmt with
  | Language.Stmt.Seq (stm1, stm2) -> compile stm1 @ compile stm2
  | Language.Stmt.Assign (var, expr) -> exprCompile expr @ [ST var]
  | Language.Stmt.Read var -> [READ; ST var]
  | Language.Stmt.Write expr -> exprCompile expr @ [WRITE]
 	| Language.Stmt.Skip -> []
 	| Language.Stmt.If (cond, thenBranch, elseBranch) -> 
 		let thenInstructions = compile thenBranch in
 		let elseInstructions = compile elseBranch in
 		let elseLabel = nameGenerator#getName in
 		let exitLabel = nameGenerator#getName in
		exprCompile cond @ 
 		[CJMP ("z", elseLabel)] @
 		thenInstructions @
 		[JMP exitLabel] @
 		[LABEL elseLabel] @
 		elseInstructions @
 		[LABEL exitLabel]
 	| Language.Stmt.While (cond, body) ->
 		let beginLabel = nameGenerator#getName in
 		let loopLabel = nameGenerator#getName in
 		[JMP beginLabel] @
 		[LABEL loopLabel] @
 		compile body @
 		[LABEL beginLabel] @
 		exprCompile cond @
 		[CJMP ("nz", loopLabel)]
 	| Language.Stmt.Repeat (body, cond) ->
 		let loopLabel = nameGenerator#getName in
 		[LABEL loopLabel] @
 		compile body @
 		exprCompile cond @
 		[CJMP ("z", loopLabel)]

