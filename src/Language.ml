(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
                         
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    let emptyOld x = failwith (Printf.sprintf "Undefined variable %s" x)

    (* Empty state *)
    let empty = {g = emptyOld; l = emptyOld; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v {g; l; scope} =
      let update' x' v' s' = fun y -> if x' = y then v' else s' y in
      match (List.mem x scope) with
        | false -> {g = update' x v g; l = l; scope = scope}
        | true  -> {g = g; l = update' x v l; scope = scope}
                                 
    (* Evals a variable in a state w.r.t. a scope *)
    let eval {g; l; scope} x = 
      match (List.mem x scope) with
      | false -> g x
      | true  -> l x

    (* Creates a new scope, based on a given state *)
    let enter {g; _; _} xs = {g = g; l = emptyOld; scope = xs}


    (* Drops a scope *)
    let leave {_; l; scope} {g; _; _} = {g; l; scope}

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
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
      
    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)                                                       

   (* TODO: extract binop evaluation *)
    let itob i = i <> 0
    let btoi b = if b then 1 else 0


    let rec eval st ex = match ex with
      | Const c -> c
      | Var var -> State.eval st var
      | Binop ("+", e1, e2) -> eval st e1 + eval st e2
      | Binop ("-", e1, e2) -> eval st e1 - eval st e2
      | Binop ("*", e1, e2) -> eval st e1 * eval st e2
      | Binop ("/", e1, e2) -> eval st e1 / eval st e2
      | Binop ("%", e1, e2) -> eval st e1 mod eval st e2
      | Binop (">", e1, e2) -> btoi ((eval st e1) > (eval st e2))
      | Binop ("<", e1, e2) -> btoi ((eval st e1) < (eval st e2))
      | Binop (">=", e1, e2) -> btoi ((eval st e1) >= (eval st e2))
      | Binop ("<=", e1, e2) -> btoi ((eval st e1) <= (eval st e2))
      | Binop ("==", e1, e2) -> btoi ((eval st e1) = (eval st e2))
      | Binop ("!=", e1, e2) -> btoi ((eval st e1) <> (eval st e2))
      | Binop ("&&", e1, e2) -> btoi ((itob @@ eval st e1) && (itob @@ eval st e2))
      | Binop ("!!", e1, e2) -> btoi ((itob @@ eval st e1) || (itob @@ eval st e2))


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

      primary: x:IDENT {Var x} | n:DECIMAL {Const n} | -"(" expr -")";
      
      parse: expr
    )
    
  end
                

let default y = function
| Some x -> x
| None -> y

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
    (* call a procedure                 *) | Call   of string * Expr.t list with show

                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters, local variables, and a body for given definition
    *)

    let rec eval env ((state, inp, out) as conf) stm = match stm with
      | Seq (stm1, stm2) -> eval env (eval env conf stm1) stm2
      | Assign (var, expr) -> (State.update var (Expr.eval state expr) state, inp, out)
      | Read var -> (State.update var (List.hd inp) state, List.tl inp, out)
      | Write expr -> (state, inp, out @ [(Expr.eval state expr)])
      | Skip -> conf
      | If (cond, thenBranch, elseBranch) -> (match (Expr.eval state cond) != 0 with
        | true -> eval env conf thenBranch
        | false -> eval env conf elseBranch)
      | (While (cond, body)) as loop -> (match (Expr.eval state cond) != 0 with
        | true -> eval env (eval env conf body) loop
        | false -> conf)
      | Repeat (body, cond) -> 
        let afterBody = eval env conf body in
        eval env afterBody (While ((Binop("==", cond, Const 0)), body)) (*not sure if it's a good idea*)
      | Call (f, args) -> 
        let argsVals = List.map (Expr.eval state) args in
        let (argNames, locals, body) = env#definition f in
        let update' s x v = State.update x v s in
        let preparedState = List.fold_left2 update' (State.enter state (argNames @ locals)) argNames argsVals in
        let (afterBody, inp', out') = eval env (preparedState, inp, out) body in
        (State.leave state afterBody, inp', out')
        

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
      | name:IDENT "(" args:!(Expr.parse)* ")" 
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
      def:
        %"fun" name:IDENT "(" argNames:IDENT* ")" locals:!(ostap(%"local" IDENT+))? "{"
          body:!(Stmt.stmt)
        "}"                    { (name, (argNames, default [] locals, body)) };
      parse: def
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
  let env = List.fold_left (fun m ((name, content)) -> M.add name content m) M.empty defs in
  let (_, _, o) = Stmt.eval (object method definition x = M.find x env end) (State.empty, i, []) body in
  o

                                   
(* Top-level parser *)
let parse = ostap (
  defs:!(Definition.def)* 
  body:!(Stmt.stmt)         { (defs, body) }
)
