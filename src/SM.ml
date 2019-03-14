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

let ( !? ) n = Language.Expr.Const n
let binop op x y = Language.Expr.Binop (op, x, y)

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
*)                         
let rec eval (stk, (s, i, o)) prg = match prg with
    | ins::p -> (match ins with
                    | BINOP op -> eval (match stk with
                                    | y::x::t -> (Language.Expr.eval s (binop op !?x !?y))::t, (s, i, o)
                                    | _ -> failwith "Too few elements on stack") p
                    | CONST z -> eval (z::stk, (s, i, o)) p
                    | READ -> eval (match i with
                                    | z::t -> z::stk, (s, t, o)
                                    | _ -> failwith "Read from empty input") p
                    | WRITE -> eval (match stk with
                                    | z::t -> t, (s, i, o @ [z])
                                    | _ -> failwith "Write from empty stack") p
                    | LD x -> eval ((s x)::stk, (s, i, o)) p
                    | ST x -> eval (match stk with
                                    | z::t -> t, ((Language.Expr.update x z s), i, o)
                                    | _ -> failwith "Store from empty stack") p
                )
    | [] -> (stk, (s, i, o))

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
  function
  | Stmt.Seq (s1, s2)  -> compile s1 @ compile s2
  | Stmt.Read x        -> [READ; ST x]
  | Stmt.Write e       -> expr e @ [WRITE]
  | Stmt.Assign (x, e) -> expr e @ [ST x]
