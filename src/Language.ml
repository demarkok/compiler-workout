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


let list_init n f =
  let rec loop i accum =
    if i = 0 then accum
    else loop (i - 1) (f (i - 1) :: accum)
  in
  loop n []



(* Values *)
module Value =
  struct

    @type t = Int of int | String of string | Array of t list | Sexp of string * t list with show

    let to_int = function 
    | Int n -> n 
    | _ -> failwith "int value expected"

    let to_string = function 
    | String s -> s 
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let sexp   s vs = Sexp (s, vs)
    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let tag_of = function
    | Sexp (t, _) -> t
    | _ -> failwith "symbolic expression expected"

    let update_string s i x = String.init (String.length s) (fun j -> if j = i then x else s.[j])
    let update_array  a i x = list_init   (List.length a)   (fun j -> if j = i then x else List.nth a j)

  end
       
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t =
    | G of (string -> Value.t)
    | L of string list * (string -> Value.t) * t

    (* Undefined state *)
    let undefined x = failwith (Printf.sprintf "Undefined variable: %s" x)

    (* Bind a variable to a value in a state *)
    let bind x v s = fun y -> if x = y then v else s y 

    (* Empty state *)
    let empty = G undefined

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let rec inner = function
      | G s -> G (bind x v s)
      | L (scope, s, enclosing) ->
         if List.mem x scope then L (scope, bind x v s, enclosing) else L (scope, s, inner enclosing)
      in
      inner s

    (* Evals a variable in a state w.r.t. a scope *)
    let rec eval s x =
      match s with
      | G s -> s x
      | L (scope, s, enclosing) -> if List.mem x scope then s x else eval enclosing x

    (* Creates a new scope, based on a given state *)
    let rec enter st xs =
      match st with
      | G _         -> L (xs, undefined, st)
      | L (_, _, e) -> enter e xs

    (* Drops a scope *)
    let leave st st' =
      let rec get = function
      | G _ as st -> st
      | L (_, _, e) -> get e
      in
      let g = get st in
      let rec recurse = function
      | L (scope, s, e) -> L (scope, s, recurse e)
      | G _             -> g
      in
      recurse st'

    (* Push a new local scope *)
    let push st s xs = L (xs, s, st)

    (* Drop a local scope *)
    let drop (L (_, _, e)) = e
                               
  end

(* Builtins *)
module Builtin =
  struct
      
    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | ".elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String   s  -> Value.of_int @@ Char.code s.[i]
                                     | Value.Array    a  -> List.nth a i
                                     | Value.Sexp (_, a) -> List.nth a i
                               )
                    )         
    | ".length"  -> (st, i, o, Some (Value.of_int (match List.hd args with 
                                                      | Value.Array a -> List.length a 
                                                      | Value.String s -> String.length s
                                                      | Value.Sexp (_, a) -> List.length a)))
    | ".array"   -> (st, i, o, Some (Value.of_array args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))       
  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* S-expressions      *) | Sexp   of string * t list
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t 
    (* function call      *) | Call   of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option
                                



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
          val eval : env -> config -> t -> config
       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method
           method definition : env -> string -> int list -> config -> config
       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
    *)                         
    let rec eval env ((st, i, o, r) as conf) expr = match expr with
      | Const c             -> (st, i, o, Some (Value.of_int c))
      | Var x               -> let v = State.eval st x in (st, i, o, Some v)
      | Binop (op, e1, e2)  ->
        let (st', i', o', Some r1) as conf' = eval env conf e1 in
        let (st'', i'', o'', Some r2)       = eval env conf' e2 in
        let result                     = evalBinop op (Value.to_int r1) (Value.to_int r2) in
        (st'', i'', o'', Some (Value.of_int result))
      | Call (f, es)        -> eval_call env conf es f
      | Array vs            -> eval_call env conf vs ".array"
      | Elem (arr, i)       -> eval_call env conf [arr; i] ".elem"
      | Length arr          -> eval_call env conf [arr] ".length"
      | String str          -> (st, i, o, Some (Value.of_string str))
      | Sexp (tag, arr)     -> 
        let ((st, i, o, _), vs) = eval_list env conf arr in
        (st, i, o, Some (Value.sexp tag vs))
    and eval_list env conf es = 
      List.fold_left 
        (fun (c, vs) e -> 
          let (_, _, _, Some v) as c' = eval env c e in
          (c', vs @ [v]))
        (conf, []) 
        es
    and eval_call env conf args name = 
      let ((st, i, o, _), vs) = eval_list env conf args in
      let c' = (st, i, o, None) in
      env#definition env name vs c'



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

      base:
        name:IDENT -"(" args:!(Ostap.Util.list0)[expr] -")" { Call (name, args) }
      | x:IDENT { Var x } 
      | -"[" elems:!(Ostap.Util.list0)[expr] -"]" { Array elems }
      | s:STRING { String (String.sub s 1 (String.length s - 2)) }
      | c:CHAR    { Const (Char.code c)}
      | n:DECIMAL { Const n } 
      | "`" tag:IDENT arr:(-"(" !(Ostap.Util.list0)[expr] -")")? { Sexp (tag, default [] arr) };
                                        
      elem: 
        arr:base indexes:(-"[" expr -"]")* { List.fold_left (fun a i -> Elem (a, i)) arr indexes };

      primary:
        x:elem l:("." %"length")? { match l with Some _ -> Length x | None -> x }
      | -"(" expr -")";

      parse: expr
    )     
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* Patterns in statements *)
    module Pattern =
      struct

        (* The type for patterns *)
        @type t =
        (* wildcard "-"     *) | Wildcard
        (* S-expression     *) | Sexp   of string * t list
        (* identifier       *) | Ident  of string
        with show, foldl

        (* Pattern parser *)                                 
        ostap (
          pattern:
            %"_" { Wildcard }
          | "`" tag:IDENT arr:(-"(" !(Ostap.Util.list0)[pattern] -")")? { Sexp (tag, default [] arr) }
          | x:IDENT { Ident x };

          parse: pattern
        )
        
        let vars p = 
          transform(t) (object inherit [string list] @t[foldl] method c_Ident s _ name = name::s end) [] p
        
      end
        
    (* The type for statements *)
    @type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* pattern-matching                 *) | Case   of Expr.t * (Pattern.t * t) list
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list 
    (* leave a scope                    *) | Leave  with show
                                                                                   
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let update st x v is =
      let rec update a v = function
      | []    -> v           
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update (List.nth a i) v tl))
          ) 
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st

    let rec eval env ((st, i, o, r) as conf) k stmt = 
      let (<|>) a b = match b with
        | Skip -> a
        | _ -> Seq (a, b)
      in
      (* Printf.printf "%s\n\n" (GT.transform(t) (new @t[show]) () stmt); *)
      match stmt with
        | Assign (var, indexes, expr)       ->
          let conf, indexes = Expr.eval_list env conf indexes in
          let (st', i', o', Some v) = Expr.eval env conf expr in
          eval env (update st var v indexes, i', o', None) Skip k
        | Seq (stm1, stm2)                  ->
          eval env conf (stm2 <|> k) stm1
        | Skip                              -> (match k with
          | Skip  -> conf
          | _     -> eval env conf Skip k
        )
        | If (cond, thenBranch, elseBranch) -> 
          let (st', i', o', Some v) = Expr.eval env conf cond in (match (Value.to_int v) with
          | 1 -> eval env (st', i', o', None) k thenBranch
          | 0 -> eval env (st', i', o', None) k elseBranch
          )
        | (While (cond, body)) as loop      -> 
          let (st', i', o', Some v) = Expr.eval env conf cond in (match (Value.to_int v) with
            | 1 -> eval env (st', i', o', None) (loop <|> k) body
            | 0 -> eval env (st', i', o', None)  Skip        k
          )
        | Repeat (body, cond)               -> 
          eval env conf ((While (Binop ("==", cond, Const 0), body)) <|> k) body
        | Return mbResult                   -> (match mbResult with
          | Some expr -> Expr.eval env conf expr
          | None      -> conf
        )
        | Call (f, args)                    -> 
          let (c, vs) = Expr.eval_list env conf args in
          eval env (env#definition env f vs c) Skip k 
        | Leave                             -> eval env (State.drop st, i, o, None) Skip k
        | Case (to_match, branches)                 ->
          let (st, i, o, Some to_match) = Expr.eval env conf to_match in
          let rec match_one_pattern obj pat = (match pat with
            | Pattern.Wildcard      -> Some []
            | Pattern.Ident var     -> Some [(var, obj)]
            | Pattern.Sexp (tag0, pats) -> (match obj with
              | Value.Sexp (tag1, objs)
                when (tag0 = tag1 && List.length pats = List.length objs) ->
                  let f r o p = match (r, match_one_pattern o p) with
                  | (Some lr, Some ln) -> Some (lr @ ln)
                  | _ -> None
                  in List.fold_left2 f (Some []) objs pats
              | _ -> None
            )
          ) in 
          let rec match_patterns = function
            | [] -> failwith "Pattern matching failed"
            | ((pat, body)::tail) -> (match (match_one_pattern to_match pat) with
              | None -> match_patterns tail
              | Some bindings ->
                let st' = List.fold_left (fun sc (x, v) -> State.bind x v sc) State.undefined bindings in
                let names = List.map fst bindings in 
                eval env (State.push st st' names, i, o, None) k (body <|> Leave)
            ) 
          in
          match_patterns branches 


    (* Statement parser *)
    ostap (
      simple_stmt:
        x:IDENT indexes:(-"[" !(Expr.expr) -"]")* ":=" e:!(Expr.expr)  { Assign (x, indexes, e) }
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
                                        { Call (name, args) }
      | %"case" v:!(Expr.expr) %"of" 
          branches:!(Util.list0By)[ostap("|")][branch] 
        %"esac"                         { Case (v, branches) };

      branch:
        !(Pattern.pattern) -"->" stmt;
      
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
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      =  snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
