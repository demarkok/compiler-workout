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
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)     

let rec drop k xs = match (k, xs) with
  | 0, l         -> l
  | _, []        -> []
  | n, (_ :: t)  -> drop (n - 1) t

let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) = function
 	| [] -> conf
 	| (instr :: rest) -> match instr with
		| LABEL _ -> eval env conf rest
		| JMP label -> eval env conf (env#labeled label)
		| CJMP (c, label) ->
			let (st, (h :: tail), sConf) = conf in
			let toEval = if (h = 0 && c = "z" || h != 0 && c = "nz") then env#labeled label else rest in
			eval env (st, tail, sConf) toEval
		| BINOP _ | CONST _ | WRITE | READ | LD _ | ST _ ->
			let nconf = (match ((stack, c), instr) with
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
			    (State.eval state var :: stack, sConf)
			  | ((fst :: tail), (state, inp, out)), (ST var) ->
			    (tail, (Language.State.update var fst state, inp, out)))
			in eval env (cstack, fst nconf, snd nconf) rest
    | CALL name -> 
      let conf' = ((rest, st) :: cstack, stack, c) in
      eval env conf' (env#labeled name)
    
    | END -> (match cstack with
      | ((p', st') :: rest)  -> eval env (rest, stack, (Language.State.leave st' st, i, o)) p'
      | [] -> conf)

    | BEGIN (argNames, locals) -> 
      let update' s x v = Language.State.update x v s in
      let preparedState = List.fold_left2 update' (Language.State.enter st (argNames @ locals)) argNames stack in
      eval env (cstack, (drop (List.length argNames) stack), (preparedState, i, o)) rest
    
      

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run p i : GT.int list =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in 
  o


let nameGenerator = object
	val mutable suffix = 0
	method getName = 
		suffix <- (suffix + 1);
		(Printf.sprintf "label_%d" suffix)
end 


(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile (defs, p) = 
  let funLabel name = Printf.sprintf "fun_%s" name in
  let rec compile' stmt =
    let rec exprCompile expr = match expr with
    | Language.Expr.Const c -> [CONST c]
    | Language.Expr.Var var -> [LD var]
    | Language.Expr.Binop (op, e1, e2) -> exprCompile e1 @ exprCompile e2 @ [BINOP op]
    in
    match stmt with
    | Language.Stmt.Seq (stm1, stm2) -> compile' stm1 @ compile' stm2
    | Language.Stmt.Assign (var, expr) -> exprCompile expr @ [ST var]
    | Language.Stmt.Read var -> [READ; ST var]
    | Language.Stmt.Write expr -> exprCompile expr @ [WRITE]
   	| Language.Stmt.Skip -> []
   	| Language.Stmt.If (cond, thenBranch, elseBranch) -> 
   		let thenInstructions = compile' thenBranch in
   		let elseInstructions = compile' elseBranch in
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
     		compile' body @
     		[LABEL beginLabel] @
     		exprCompile cond @
     		[CJMP ("nz", loopLabel)]
   	| Language.Stmt.Repeat (body, cond) ->
   		let loopLabel = nameGenerator#getName in
     		[LABEL loopLabel] @
     		compile' body @
     		exprCompile cond @
     		[CJMP ("z", loopLabel)]
    | Language.Stmt.Call (name, args) ->
        List.concat (List.rev_map exprCompile args) @
        [CALL (funLabel name)] in
  let rec compileDef (name, (argNames, locals, body)) = 
    [LABEL (funLabel name)]@
    [BEGIN (argNames, locals)]@
    compile' body @
    [END] in

  compile' p @ 
  [END] @ 
  List.concat @@ List.map compileDef defs

