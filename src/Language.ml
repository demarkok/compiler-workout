(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
                

let default y = function
| Some x -> x
| None -> y

(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option
                                             

    let itob i = i <> 0
    let btoi b = if b then 1 else 0

    (* string -> int -> int -> int *)
    let evalBinop op e1 e2 = match op with
      |"+" -> e1 + e2
      |"-" -> e1 - e2
      |"*" -> e1 * e2
      |"/" -> e1 / e2
      |"%" -> e1 mod e2
      |">" -> btoi (e1 > e2)
      |"<" -> btoi (e1 < e2)
      |">=" -> btoi (e1 >= e2)
      |"<=" -> btoi (e1 <= e2)
      |"==" -> btoi (e1 = e2)
      |"!=" -> btoi (e1 <> e2)
      |"&&" -> btoi ((itob e1) && (itob e2))
      |"!!" -> btoi ((itob e1) || (itob e2))
 

    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
    *)                                                       
    let rec eval env ((st, i, o, r) as conf) expr = match expr with
      | Const c             -> c, (st, i, o, Some c)
      | Var x               -> let v = State.eval st x in v, (st, i, o, Some v)
      | Binop (op, e1, e2)  ->
        let r1, conf'               = eval env conf e1 in
        let r2, (st'', i'', o'', _) = eval env conf' e2 in
        let result                  = evalBinop op r1 r2 in
        result, (st'', i'', o'', Some result)
      | Call (f, es)        -> 
        let (c, vs) = eval_list env conf es in
        let ((_, _, _, Some result) as c) = env#definition env f vs c in 
        result, c
    and eval_list env conf es = 
      List.fold_left 
        (fun (c, vs) e -> 
          let v, c' = eval env c e in
          (c', vs @ [v]))
        (conf, []) 
        es
        
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)
    let opList2ExprOstapList opList = List.map (fun s -> (ostap($(s)), fun x y -> Binop (s, x, y))) opList
    
    ostap (
      expr:
        !(Ostap.Util.expr
           (fun x -> x)
           [|
             `Lefta , opList2ExprOstapList ["!!"];
             `Lefta , opList2ExprOstapList ["&&"];
             `Nona  , opList2ExprOstapList ["!="; "=="; "<="; ">="; "<"; ">"];
             `Lefta , opList2ExprOstapList ["+"; "-"];
             `Lefta , opList2ExprOstapList ["*"; "/"; "%"]
           |]
           primary
         );

      primary: 
        name:IDENT "(" args:!(Ostap.Util.list0)[expr] ")" { Call (name, args) }
      | x:IDENT {Var x} 
      | n:DECIMAL {Const n} 
      | -"(" expr -")";
                                        
      
      parse: expr
    )
  end

   
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let rec eval env ((st, i, o, r) as conf) k stmt = 
      let (<|>) a b = match b with
        | Skip -> a
        | _ -> Seq (a, b)
      in
      (* Printf.printf "%s\n" (GT.transform(t) (new @t[show]) () stmt); *)
      match stmt with
        | Read  var                         -> 
          let (x :: tl) = i in
          eval env (State.update var x st, tl, o, None) Skip k
        | Write expr                        -> 
          let v, (st', i', o', _) = Expr.eval env conf expr in
          eval env (st', i', o' @ [v], None) Skip k
        | Assign (var, expr)                ->
          let v, (st', i', o', _) = Expr.eval env conf expr in
          eval env (State.update var v st', i', o', None) Skip k
        | Seq (stm1, stm2)                  ->
          eval env conf (stm2 <|> k) stm1
        | Skip                              -> (match k with
          | Skip  -> conf
          | _     -> eval env conf Skip k
        )
        | If (cond, thenBranch, elseBranch) -> (match (Expr.eval env conf cond) with
          | 1, (st', i', o', _) -> eval env (st', i', o', None) k thenBranch
          | 0, (st', i', o', _) -> eval env (st', i', o', None) k elseBranch
          )
        | (While (cond, body)) as loop      -> (match (Expr.eval env conf cond) with
          | 1, (st', i', o', _) -> eval env (st', i', o', None) (loop <|> k) body
          | 0, (st', i', o', _) -> eval env (st', i', o', None)  Skip        k
        )
        | Repeat (body, cond)               -> 
          eval env conf ((While (Binop ("==", cond, Const 0), body)) <|> k) body
        | Return mbResult                   -> (match mbResult with
          | Some expr -> let (_, c') = Expr.eval env conf expr in c'
          | None      -> conf
        )
        | Call (f, args)                    -> 
          let (c, vs) = Expr.eval_list env conf args in
          eval env (env#definition env f vs c) Skip k 
 
    (* Statement parser *)
    ostap (
      simple_stmt:
        x:IDENT ":=" e:!(Expr.expr)     { Assign (x, e) }
      | "read"  "(" x:IDENT     ")"     { Read x }
      | "write" "(" e:!(Expr.expr) ")"  { Write e }
      | %"skip"                         { Skip }
      | %"if" cond:!(Expr.expr) %"then" 
          thenBranch:stmt
        elifBranches:(%"elif" !(Expr.expr) %"then" stmt)*
        elseBranch:(%"else" stmt)?
        %"fi"                           { If (cond, 
                                             thenBranch, 
                                             List.fold_right (fun (c, b) e -> If (c, b, e)) elifBranches (default Skip elseBranch))
                                        }     
      | %"while" cond:!(Expr.expr) %"do"
          body:stmt
        %"od"                           { While (cond, body) }
      | %"repeat" 
          body:stmt 
        %"until" cond:!(Expr.expr)      { Repeat (body, cond) }
      | %"for" init:stmt "," cond:!(Expr.expr) "," update:stmt %"do"
          body:stmt
        %"od"                           { Seq (init, While (cond, Seq (body, update))) }
      | %"return" value:!(Expr.expr)?   { Return  value }
      | name:IDENT "(" args:!(Ostap.Util.list0)[Expr.expr] ")" 
                                        { Call (name, args) };
      stmt: 
        !(Ostap.Util.expr
          (fun x -> x)
          [|
            `Lefta , [ostap (";"), (fun x y -> Seq (x, y))]
          |]
          simple_stmt
        );      
      parse: stmt
    ) 
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
      }
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args (st, i, o, r) =
           let xs, locs, s      = snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
