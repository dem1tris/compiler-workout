open GT

open Syntax

(*
open Embedding
No implementations provided for the following modules:
         Embedding referenced from ../src/SM.cmx
*)

       
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


let ( !? ) n = Syntax.Expr.Const n
let binop op x y = Syntax.Expr.Binop (op, x, y)

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)

let rec eval (stk, (s, i, o)) prg = match prg with
    | ins::p -> (match ins with
                    | BINOP op -> eval (match stk with
                                    | y::x::t -> (Syntax.Expr.eval s (binop op !?x !?y))::t, (s, i, o)
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
                                    | z::t -> t, ((Syntax.Expr.update x z s), i, o)
                                    | _ -> failwith "Store from empty stack") p
                )
    | [] -> (stk, (s, i, o))


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
    let rec translateExpr expr = match expr with
        | Syntax.Expr.Const c            -> [CONST c]
        | Syntax.Expr.Var x              -> [LD x]
        | Syntax.Expr.Binop (o, x, y)    -> (translateExpr x) @ (translateExpr y) @ [BINOP o] in
    match stmt with
        | Syntax.Stmt.Read x             -> [READ; ST x]
        | Syntax.Stmt.Write e            -> (translateExpr e) @ [WRITE]
        | Syntax.Stmt.Assign (x, e)      -> (translateExpr e) @ [ST x]
        | Syntax.Stmt.Seq (stmt1, stmt2) -> (compile stmt1) @ (compile stmt2)
