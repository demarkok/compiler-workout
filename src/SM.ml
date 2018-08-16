open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
with show
                                                   
(* The type for the stack machine program *)
type prg = insn list

let print_prg p = List.iter (fun i -> Printf.printf "%s\n" (show(insn) i)) p
                            
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
        (* let (indexes, stack) = split n stack *)
        let indexes = List.rev (take n stack) in
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
      let (state', stack') = List.fold_left update' (Language.State.enter st (argNames @ locals), stack) (List.rev argNames) in
      eval env (cstack, stack', (state', i, o)) rest
    | SEXP (tag, args) ->
      let (values, stack) = split args stack in
      let sexp = Language.Value.sexp tag (List.rev values) in
      eval env (cstack, sexp :: stack, c) rest
    | DROP -> let (x :: xs) = stack in eval env (cstack, xs, c) rest
    | DUP ->  let (x :: xs) = stack in eval env (cstack, x :: stack, c) rest
    | SWAP -> let (x :: y :: xs) = stack in eval env (cstack, y :: x :: xs, c) rest
    | TAG tag -> 
      let (x :: xs) = stack in
      let result = (match x with
        | Value.Sexp (tag', _) when tag = tag' -> 1
        | _ -> 0
      ) in
      eval env (cstack, Value.of_int result :: xs, c) rest
    | ENTER xs ->
      let (values, stack) = split (List.length xs) stack in 
      let new_state = List.fold_left2 (fun state x value -> Language.State.bind x value state) State.undefined xs values in
      eval env (cstack, stack, (Language.State.push st new_state xs, i, o)) rest
    | LEAVE -> eval env (cstack, stack, (Language.State.drop st, i, o)) rest


(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (* print_prg p; *)
  (* Printf.printf "\n\n\n";  *)
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
           Printf.printf "Builtin: %s\n";
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
    let rec exprCompile expr = 
    (* Printf.printf "%s\n\n" (GT.transform(Expr.t) (new @Expr.t[show]) () expr); *)
    match expr with
    | Language.Expr.Const c -> [CONST c]
    | Language.Expr.Var var -> [LD var]
    | Language.Expr.Binop (op, e1, e2) -> exprCompile e1 @ exprCompile e2 @ [BINOP op]
    | Language.Expr.Call (name, args) ->  
        List.concat (List.map exprCompile args) @
        [CALL (funLabel name, List.length args, false)]
    | Language.Expr.Array arr -> 
        List.concat (List.map exprCompile arr) @
        [CALL (".array", List.length arr, false)]
    | Language.Expr.String str -> [STRING str]
    | Language.Expr.Elem (arr, ind) -> exprCompile arr @ exprCompile ind @ [CALL (".elem", 2, false)]
    | Language.Expr.Length arr -> exprCompile arr @ [CALL (".length", 1, false)]
    | Language.Expr.Sexp (tag, arr) -> (List.flatten @@ List.map exprCompile arr) @ [SEXP (tag, List.length arr)]
    in
    match stmt with
    | Language.Stmt.Seq (stm1, stm2) -> compile' stm1 @ compile' stm2
    | Language.Stmt.Assign (var, [], expr) -> exprCompile expr @ [ST var]
    | Language.Stmt.Assign (var, indexes, expr) ->
        (List.concat (List.map exprCompile indexes)) @
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
    | Language.Stmt.Leave -> 
        [LEAVE]
    | Language.Stmt.Case (to_match, branches) ->
      let super_end_label = nameGenerator#getName in
      
      let is_primary_pattern = function
        | Stmt.Pattern.Sexp _ -> false
        | _                   -> true 
      in

      let rec match_pattern pat true_label false_label = (match pat with 
        | Stmt.Pattern.Wildcard -> [DROP]
        | Stmt.Pattern.Ident _  -> [DROP]
        | Stmt.Pattern.Sexp (tag, pts) ->
          let new_false_label = nameGenerator#getName in
          let l = List.length pts in
          [DUP] @ [TAG tag] @ [CJMP ("z", false_label)] @
          [DUP] @ [CALL(".length", 1, false)] @ [CONST(List.length pts)] @ [BINOP ("==")] @ [CJMP ("z", false_label)] @
          (List.flatten @@ List.mapi 
            (fun i pt -> [DUP] @ [CONST i] @ [CALL(".elem", 2, false)] @ match_pattern pt true_label new_false_label) 
            pts) @
          [DROP] @
          [JMP true_label] @
          (if List.for_all is_primary_pattern pts then []
                                                  else [LABEL new_false_label] @ [DROP] @ [JMP false_label])
      ) in
      let rec size pat = (match pat with
        | Stmt.Pattern.Wildcard -> 0
        | Stmt.Pattern.Ident _  -> 1
        | Stmt.Pattern.Sexp (_, pts) -> List.fold_left (fun sum pt -> sum + size pt) 0 pts
      ) in
      let rec down pat n = (match pat with
        | Stmt.Pattern.Wildcard -> []
        | Stmt.Pattern.Ident _ -> []
        | Stmt.Pattern.Sexp (_, pts) ->
          let rec skip k i (pt :: rest) = 
            let k' = k + size pt in
            if k' >= n then [CONST i] @ [CALL(".elem", 2, false)] @ (down pt (n - k)) else skip k' (i + 1) rest
          in
          skip 0 0 pts
      ) in
      let compile_branch (pat, body) =
        let vars = Language.Stmt.Pattern.vars pat in 
        let vars_len = List.length vars in
        let next_branch_label = nameGenerator#getName in
        let true_label = "TRUE" ^ nameGenerator#getName in 
        [DUP] @
        match_pattern pat true_label next_branch_label @
        (if is_primary_pattern pat then [] else [LABEL true_label]) @ (*здесь мы с одним исксом*)
        (List.flatten @@ List.mapi (fun i _ -> [DUP] @ (down pat (i + 1)) @ [SWAP]) vars) @ 
        [DROP] @ (*здесь у нас пустой стек*)
        [ENTER vars] @
        compile' body @
        [LEAVE] @
        [JMP super_end_label] @
        (if is_primary_pattern pat then [] else [LABEL next_branch_label] @ [DROP])  (*здесь мы с двумя исксами*) 
      in
      exprCompile to_match @
      (List.flatten @@ List.map compile_branch branches) @
      [LABEL super_end_label]
    in
  let rec compileDef (name, (argNames, locals, body)) = 
    [LABEL (funLabel name)]@
    [BEGIN (name, argNames, locals)]@
    compile' body @
    [END] in

  compile' p @ 
  [END] @ 
  List.concat @@ List.map compileDef defs