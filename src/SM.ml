open GT

       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Syntax.Stmt.config

(* Stack machine interpreter

f 0 = 1
f n = n * f (n - 1)

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)   
let eval conf pr =
  let eval1 (conf : config) (instr : insn) : config = match (conf, instr) with
  | (fst :: snd :: tail, ((state, _, _) as sConf)), (BINOP op) ->
    let res = (Syntax.Expr.eval state (Syntax.Expr.Binop (op, Syntax.Expr.Const fst, Syntax.Expr.Const snd))) in
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
    (tail, (Syntax.Expr.update var fst state, inp, out))  
  in
  List.fold_left eval1 conf pr

(* Top-level evaluation

     val run : int list -> prg -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run i p = let (_, (_, _, o)) = eval ([], (Syntax.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
let rec compile stmt =
  let rec exprCompile expr = match expr with
  | Syntax.Expr.Const c -> [CONST c]
  | Syntax.Expr.Var var -> [LD var]
  | Syntax.Expr.Binop (op, e1, e2) -> exprCompile e2 @ exprCompile e1 @ [BINOP op]
  in
  match stmt with
  | Syntax.Stmt.Seq (stm1, stm2) -> compile stm1 @ compile stm2
  | Syntax.Stmt.Assign (var, expr) -> exprCompile expr @ [ST var]
  | Syntax.Stmt.Read var -> [READ; ST var]
  | Syntax.Stmt.Write expr -> exprCompile expr @ [WRITE]
 