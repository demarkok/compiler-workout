(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
       
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
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

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
      | Var var -> st var
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
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval ((state, inp, out) as conf) stm = match stm with
      | Seq (stm1, stm2) -> eval (eval conf stm1) stm2
      | Assign (var, expr) -> (Expr.update var (Expr.eval state expr) state, inp, out)
      | Read var -> (Expr.update var (List.hd inp) state, List.tl inp, out)
      | Write expr -> (state, inp, out @ [(Expr.eval state expr)])

    (* Statement parser *)
    ostap (
      simple_stmt:
        x:IDENT ":=" e:!(Expr.expr)     {Assign (x, e)}
      | "read"  "(" x:IDENT     ")"  {Read x}
      | "write" "(" e:!(Expr.expr) ")"  {Write e};

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

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o

(* Top-level parser *)
let parse = Stmt.parse                                                     
