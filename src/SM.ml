open GT       
open Language
       
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
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let eval conf pr =
  let eval1 (conf : config) (instr : insn) : config = match (conf, instr) with
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
    (tail, (Language.Expr.update var fst state, inp, out))  
  in
  List.fold_left eval1 conf pr
(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Expr.empty, i, [])) p in o

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
                         
