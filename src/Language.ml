(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT
open List

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

    let to_int b = if b then 1 else 0

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)                                                       
    let rec eval s e = match e with
                    | Const c -> c
                    | Var v -> s v
                    | Binop ("+",  a, b) -> eval s a + eval s b
                    | Binop ("-",  a, b) -> eval s a - eval s b
                    | Binop ("*",  a, b) -> eval s a * eval s b
                    | Binop ("/",  a, b) -> eval s a / eval s b
                    | Binop ("%",  a, b) -> eval s a mod eval s b
                    | Binop ("<",  a, b) -> to_int (eval s a < eval s b)
                    | Binop ("<=", a, b) -> to_int (eval s a <= eval s b)
                    | Binop (">",  a, b) -> to_int (eval s a > eval s b)
                    | Binop (">=", a, b) -> to_int (eval s a >= eval s b)
                    | Binop ("==", a, b) -> to_int (eval s a == eval s b)
                    | Binop ("!=", a, b) -> to_int (eval s a != eval s b)
                    | Binop ("!!", a, b) -> to_int (eval s a != 0 || eval s b != 0)
                    | Binop ("&&", a, b) -> to_int (eval s a != 0 && eval s b != 0)
                    | _ -> failwith @@ Printf.sprintf "Syntax error"

    let binop op x y = Binop (op, x, y)

    let binopSpecifier ops = List.map (fun op -> ostap ( - $(op) ), binop op) ops


    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)
    ostap (                                      
        expr:
                !(Ostap.Util.expr
                   (fun x -> x)
                   [|
                     `Lefta , binopSpecifier ["!!"];
                     `Lefta , binopSpecifier ["&&"];
                     `Nona  , binopSpecifier [">="; ">"; "=="; "!="; "<="; "<"];
                     `Lefta , binopSpecifier ["+"; "-"];
                     `Lefta , binopSpecifier ["*"; "/"; "%"];
                   |]
                   primary
                );
        primary:
            c: DECIMAL { Const c } |
            x: IDENT { Var x } |
            - "(" expr - ")"
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read    of string
    (* write the value of an expression *) | Write   of Expr.t
    (* assignment                       *) | Assign  of string * Expr.t
    (* composition                      *) | Seq     of t * t
    (* empty statement                  *) | Skip
    (* conditional                      *) | If      of Expr.t * t * t
    (* loop with a pre-condition        *) | While   of Expr.t * t
    (* loop with a post-condition       *) | Repeat  of t * Expr.t with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

         val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval (s, i, o) stmt =
            match stmt with
                | Read x -> (match i with
                                | z::t -> Expr.update x z s, t, o
                                | _ -> failwith "Read from empty input"
                            )
                | Write e -> s, i, o @ [Expr.eval s e]
                | Assign (x, e) -> Expr.update x (Expr.eval s e) s, i, o
                | Seq (st1, st2) -> eval (eval (s, i, o) st1) st2
                | Skip -> s, i, o
                | If (cond, st1, st2)-> (
                    let res = Expr.eval s cond in
                    if res = 0
                    then eval (s, i, o) st2
                    else  eval (s, i, o) st1
                )
                | While (cond, st) -> (
                    let res = Expr.eval s cond in
                    if res = 0
                    then s, i, o
                    else eval (eval (s, i, o) st) (While (cond, st))
                )
                | Repeat (st, cond) -> (
                    let (s', i', o') = eval (s, i, o) st in
                    let res = Expr.eval s' cond in
                    if res != 0
                    then s', i', o'
                    else eval (s', i', o') (Repeat (st, cond))
                )

    (* Statement parser *)
    ostap (
        stmt:
            "read"  "(" x:IDENT ")"                        {Read x}           |
            "write" "(" e:!(Expr.expr) ")"                 {Write e}          |
            x:IDENT  ":=" e:!(Expr.expr)                   {Assign (x, e)}    |
            b: (iff | forr | whil | repeat)                {b}                |
            "skip"                                         {Skip};
        repeat:
            "repeat" b:parse
            "until" cond:!(Expr.expr)                      {Repeat (b, cond)};
        forr:
            "for" a:stmt
            "," cond:!(Expr.expr)
            "," st:stmt
            "do" b:parse
            "od"                                           {Seq (a, While (cond, Seq(b, st)))};
        iff:
            "if" e:!(Expr.expr)
                "then" thb:parse
                elb:elif?
                "fi"                                       {If (e, thb, match elb with Some b -> b | None -> Skip)};
        elif:
            "else" eb:parse                                {eb}              |
            "elif" e:!(Expr.expr)
                "then" thb:parse
                elb:elif                                   {If (e, thb, elb)};
        whil:
            "while" cond:!(Expr.expr)
            "do" b:parse
            "od"                                           {While (cond, b)};
        parse:
            st:stmt ";" tail:parse                         {Seq (st, tail)}   |
            stmt
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
