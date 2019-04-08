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
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL  of string * int * bool
(* returns from a function         *) | RET   of bool with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Expr.config
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

(*let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) prg = failwith "Not implemented"*)
let rec eval env cfg prg =
    let cs, stk, (s, i, o) = cfg in
    match prg with
    | ins::p -> (match ins with
                    | BINOP op -> (let cfg' = match stk with
                                     | y::x::t -> cs, (Language.Expr.to_func op x y)::t, (s, i, o)
                                     | _ -> failwith "Too few elements on stack" in
                                   eval env cfg' p
                                  )
                    | CONST z -> (let cfg' = (cs, z::stk, (s, i, o)) in
                                  eval env cfg' p
                                 )
                    | READ -> (let cfg' = match i with
                                  | z::t -> cs, z::stk, (s, t, o)
                                  | _ -> failwith "Read from empty input" in
                               eval env cfg' p
                              )
                    | WRITE -> (let cfg' = match stk with
                                   | z::t -> cs, t, (s, i, o @ [z])
                                   | _ -> failwith "Write from empty stack" in
                                eval env cfg' p
                               )
                    | LD x -> eval env (cs, (State.eval s x)::stk, (s, i, o)) p
                    | ST x -> eval env (match stk with
                                    | z::t -> cs, t, ((Language.State.update x z s), i, o)
                                    | _ -> failwith "Store from empty stack") p
                    | LABEL l -> eval env (cs, stk, (s, i, o)) p
                    | JMP l -> eval env (cs, stk, (s, i, o)) (env#labeled l)
                    | CJMP (suf, l) ->  (let h::stk = stk in
                                         eval env (cs, stk, (s, i, o)) (if sufToOp suf h
                                                                    then env#labeled l
                                                                    else p)
                                        )
                    | BEGIN (_, args, locals) -> (
                        let s' = State.enter s (args @ locals) in
                        let take_params = List.map (fun x -> ST x) args in
                        eval env (cs, stk, (s', i, o)) (take_params @ p)
                    )
                    | RET _ | END -> (match cs with
                                        | (p', s')::tail -> eval env (tail, stk, (State.leave s s', i, o)) p'
                                        | [] -> [], stk, (s, i, o)
                                     )
                    | CALL (label, _, _) -> eval env ((p, s)::cs, stk, (s, i, o)) (JMP(label)::p)
                )
    | [] -> (cs, stk, (s, i, o))

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
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

  let labels =
      object
          val mutable cnt = 0 (* number of used labels *)
          method newLabel infix =
              cnt <- cnt + 1; Printf.sprintf "L_%s%d" infix cnt
      end

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compileBody prog =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  | Expr.Call (name, params) -> List.flatten (List.map (expr) (List.rev params)) @ [CALL (name, List.length params, true)]
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
  | Stmt.Call (name, params)        -> List.flatten (List.map (expr) (List.rev params)) @ [CALL (name, List.length params, false)], false
  | Stmt.Return e                   -> (match e with Some x -> (expr x) @ [RET true] | None -> [RET false]), false
  in
  let lab = labels#newLabel "end" in
  let res, used = compile' lab prog in
  res @ (if used then [LABEL lab] else [])

let compileDefs defs =
  let compiler = fun (name, (args, locals, body)) -> [LABEL name; BEGIN (name, args, locals)] @ compileBody body @ [END] in
  List.flatten (List.map compiler defs)

let compile (defs, first_instr) =
  let body = compileBody first_instr in
  let funcs = compileDefs defs in
  body @ [END] @ funcs
