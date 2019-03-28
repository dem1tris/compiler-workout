open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

let ( !? ) n = Language.Expr.Const n
let binop op x y = Language.Expr.Binop (op, x, y)

let sufToOp = function
    | "z" -> let f a = (a = 0) in f
    | "nz" -> let f a = a != 0 in f
    | _ -> failwith "Invalid CJMP suffix"

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let rec eval env cfg prg =
    let stk, (s, i, o) = cfg in
    match prg with
    | ins::p -> (match ins with
                    | BINOP op -> (let cfg' = match stk with
                                     | y::x::t -> (Language.Expr.eval s (binop op !?x !?y))::t, (s, i, o)
                                     | _ -> failwith "Too few elements on stack" in
                                   eval env cfg' p
                                  )
                    | CONST z -> (let cfg' = (z::stk, (s, i, o)) in
                                  eval env cfg' p
                                 )
                    | READ -> (let cfg' = match i with
                                  | z::t -> z::stk, (s, t, o)
                                  | _ -> failwith "Read from empty input" in
                               eval env cfg' p
                              )
                    | WRITE -> (let cfg' = match stk with
                                   | z::t -> t, (s, i, o @ [z])
                                   | _ -> failwith "Write from empty stack" in
                                eval env cfg' p
                               )
                    | LD x -> eval env ((s x)::stk, (s, i, o)) p
                    | ST x -> eval env (match stk with
                                    | z::t -> t, ((Language.Expr.update x z s), i, o)
                                    | _ -> failwith "Store from empty stack") p
                    | LABEL l -> eval env (stk, (s, i, o)) p
                    | JMP l -> eval env (stk, (s, i, o)) (env#labeled l)
                    | CJMP (suf, l) ->  (let h::stk = stk in
                                         eval env (stk, (s, i, o)) (if sufToOp suf h
                                                                    then env#labeled l
                                                                    else p)
                                        )
                )
    | [] -> (stk, (s, i, o))

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
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

let labels =
    object
        val mutable cnt = 0 (* number of used labels *)
        method newLabel infix =
            cnt <- cnt + 1; Printf.sprintf "L_%s%d" infix cnt
    end
(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile prog =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
  let rec compile' lab =
  function
  | Stmt.Seq (s1, s2)               -> (let lab1 = labels#newLabel "sem" in
                                        let p1, used1 = compile' lab1 s1 in
                                        let p2, used2 = compile' lab s2 in
                                        p1 @ (if used1 then [LABEL lab1] else []) @ p2, used2
                                       )
  | Stmt.Read x                     -> [READ; ST x], false
  | Stmt.Write e                    -> expr e @ [WRITE], false
  | Stmt.Assign (x, e)              -> expr e @ [ST x], false
  | Stmt.Skip                       -> [], false
  | Stmt.If (cond, b1, b2)          -> (let lelse = labels#newLabel "else" in
                                        let p1, used1 = compile' lab b1 in
                                        let p2, used2 = compile' lab b2 in
                                        expr cond @ [CJMP ("z", lelse)]
                                        @ p1 @ (if used1 then [] else [JMP lab]) @ [LABEL lelse]
                                        @ p2 @ (if used1 then [] else [JMP lab]), true
                                        )
  | Stmt.While (cond, b)            -> (let lcheck = labels#newLabel "wh_check" in
                                        let lloop = labels#newLabel "wh_loop" in
                                        let p, used = compile' lcheck b in
                                        [JMP lcheck; LABEL lloop] @ p @
                                        [LABEL lcheck] @ expr cond @ [CJMP ("nz", lloop)], false
                                       )
  | Stmt.Repeat (b, cond)           -> (let lloop = labels#newLabel "rp_loop" in
                                        let lcheck = labels#newLabel "rp_check" in
                                        let p, used = compile' lloop b in
                                        [LABEL lloop] @ p @ (if used then [LABEL lcheck] else []) @ expr cond @ [CJMP ("z", lloop)], false
                                       )
  in
  let lab = labels#newLabel "end" in
  let res, used = compile' lab prog in
  res @ (if used then [LABEL lab] else [])
