open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string                      
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool with show
                                                   
(* The type for the stack machine program *)
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
        

let rec drop k xs = match (k, xs) with
  | 0, l         -> l
  | _, []        -> []
  | n, (_ :: t)  -> drop (n - 1) t

let rec take k xs = match (k, xs) with
  | 0, _         -> []
  | _, []        -> []
  | n, (x :: t)  -> x :: take (n - 1) t



(* let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) prg = failwith "Not implemented" *)
let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) = function
  | [] -> conf
  | (instr :: rest) -> 
    (* Printf.printf "%s\n" (GT.transform(insn) (new @insn[show]) () instr);  *)
    match instr with
    | LABEL _ -> eval env conf rest
    | JMP label -> eval env conf (env#labeled label)
    | CJMP (c, label) ->
      let (st, (h :: tail), sConf) = conf in
      let h = Language.Value.to_int h in
      let toEval = if (h = 0 && c = "z" || h != 0 && c = "nz") then env#labeled label else rest in
      eval env (st, tail, sConf) toEval
    | BINOP _ | CONST _  | LD _ | ST _ | STRING _ ->
      let nconf = (match ((stack, c), instr) with
        | (fst :: snd :: tail, ((state, _, _) as sConf)), (BINOP op) ->
          let res = Language.Expr.evalBinop op (Language.Value.to_int snd) (Language.Value.to_int fst) in
          ((Language.Value.of_int res :: tail), sConf)
        | (stack, sConf), (CONST c) ->
          (Language.Value.of_int c :: stack, sConf)
        | (stack, ((state, _, _) as sConf)), (STRING str) ->
          (Language.Value.of_string str :: stack, sConf)
        | (stack, ((state, _, _) as sConf)), (LD var) ->
          (Language.State.eval state var :: stack, sConf)
        | ((fst :: tail), (state, inp, out)), (ST var) ->
          (tail, (Language.State.update var fst state, inp, out)))
      in eval env (cstack, fst nconf, snd nconf) rest
    | STA (arr, n) ->
        let (x :: stack) = stack in
        let indexes = take n stack in
        let stack = drop n stack in
        eval env (cstack, stack, (Language.Stmt.update st arr x indexes, i, o)) rest
    | CALL (name, args, from_stmt) -> 
      (* Printf.printf "AA: %s\n" name; *)
      if env#is_label name then
        let conf' = ((rest, st) :: cstack, stack, c) in
        eval env conf' (env#labeled name)
      else
        eval env (env#builtin conf name args from_stmt) rest
    | END | RET _ -> (match cstack with
      | ((p', st') :: rest)  -> eval env (rest, stack, (Language.State.leave st st', i, o)) p'
      | [] -> conf)
    | BEGIN (_, argNames, locals) -> 
      let update' (state, (h :: tl)) x = (State.update x h state, tl) in 
      let (state', stack') = List.fold_left update' (Language.State.enter st (argNames @ locals), stack) argNames in
      eval env (cstack, stack', (state', i, o)) rest

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           (* Printf.printf "Builtin: %s\n" f; *)
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
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
  let funLabel name = Printf.sprintf "L%s" name in
  let rec compile' stmt =
    let rec exprCompile expr = match expr with
    | Language.Expr.Const c -> [CONST c]
    | Language.Expr.Var var -> [LD var]
    | Language.Expr.Binop (op, e1, e2) -> exprCompile e1 @ exprCompile e2 @ [BINOP op]
    | Language.Expr.Call (name, args) ->  
        List.concat (List.rev_map exprCompile args) @
        [CALL (funLabel name, List.length args, false)]
    | Language.Expr.Array arr -> 
        List.concat (List.map exprCompile arr) @
        [CALL ("$array", List.length arr, false)]
    | Language.Expr.String str -> [STRING str]
    | Language.Expr.Elem (arr, ind) -> exprCompile arr @ exprCompile ind @ [CALL ("$elem", 2, false)]
    | Language.Expr.Length arr -> exprCompile arr @ [CALL ("$length", 1, false)]
    in
    match stmt with
    | Language.Stmt.Seq (stm1, stm2) -> compile' stm1 @ compile' stm2
    | Language.Stmt.Assign (var, [], expr) -> exprCompile expr @ [ST var]
    | Language.Stmt.Assign (var, indexes, expr) ->
        List.concat (List.rev_map exprCompile indexes) @
        exprCompile expr @ 
        [STA (var, List.length indexes)]
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
        [CALL (funLabel name, List.length args, true)] 
    | Language.Stmt.Return None ->
        [RET false]
    | Language.Stmt.Return (Some v) ->
        exprCompile v @
        [RET true]
    in
  let rec compileDef (name, (argNames, locals, body)) = 
    [LABEL (funLabel name)]@
    [BEGIN (name, argNames, locals)]@
    compile' body @
    [END] in

  compile' p @ 
  [END] @ 
  List.concat @@ List.map compileDef defs