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
                                      | DROPN   of int
(* conditional multiple drop&jmp   *) | CDRNJ   of string * int * string
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
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
          
let rec eval env cfg prg =
    let cs, stk, (s, i, o) = cfg in
    match prg with
    | ins::p -> (
    (*Printf.eprintf "\nExecuting %s with stack \n\t[%s]\n" (show insn ins) (String.concat " ,\n\t" (List.map Value.v2s stk));*)
                 (*Printf.printf "---%s\n" (show(insn) ins);*)
                 match ins with
                    | BINOP op -> (let cfg' = match stk with
                                     | y::x::t -> cs, (Value.of_int (Expr.to_func op (Value.to_int x) (Value.to_int y)))::t, (s, i, o)
                                     | _ -> failwith "Too few elements on stack" in
                                   eval env cfg' p
                                  )
                    | CONST z -> (let cfg' = (cs, (Value.of_int z)::stk, (s, i, o)) in
                                  eval env cfg' p
                                 )
                    | STRING str -> eval env (cs, (Value.of_string str)::stk, (s, i, o)) p
                    | LD x -> eval env (cs, (State.eval s x)::stk, (s, i, o)) p
                    | ST x -> eval env (match stk with
                                    | z::t -> cs, t, ((State.update x z s), i, o)
                                    | _ -> failwith "Store from empty stack") p
                    | STA (x, n) -> let v::ids, stk' = split (n + 1) stk in
                                    let s' = Stmt.update s x v ids in
                                    eval env (cs, stk', (s', i, o)) p
                    | LABEL l -> eval env (cs, stk, (s, i, o)) p
                    | JMP l -> eval env (cs, stk, (s, i, o)) (env#labeled l)
                    | CJMP (suf, l) ->  let h::stk = stk in
                                        eval env (cs, stk, (s, i, o)) (if sufToOp suf @@ Value.to_int h
                                                                       then env#labeled l
                                                                       else p)
                    | CDRNJ (suf, dep, l) -> let h::stk = stk in
                                        if sufToOp suf @@ Value.to_int h
                                        then let _, stk = split dep stk in eval env (cs, stk, (s, i, o)) (env#labeled l)
                                        else eval env (cs, stk, (s, i, o)) p
                    | DROPN n -> let _, stk = split n stk in eval env (cs, stk, (s, i, o)) p
                    | BEGIN (_, args, locals) -> (
                        let s' = State.enter s (args @ locals) in
                        let take_params = List.map (fun x -> ST x) args in
                        eval env (cs, stk, (s', i, o)) (take_params @ p)
                    )
                    | RET _ | END -> (match cs with
                                        | (p', s')::tail -> eval env (tail, stk, (State.leave s s', i, o)) p'
                                        | [] -> [], stk, (s, i, o)
                                     )
                    | CALL (label, n, is_func) -> if env#is_label label
                                            then eval env ((p, s)::cs, stk, (s, i, o)) (JMP(label)::p)
                                            else eval env (env#builtin cfg label n (not is_func)) p
                    | SEXP (t, n) -> let vs, stk' = split n stk in
                                     eval env (cs, (Value.sexp t @@ List.rev vs)::stk', (s, i, o)) p
                    | DROP          -> (*)Printf.printf "%d\n" List.length stk;*) eval env (cs, List.tl stk, (s, i, o)) p
                    | DUP           -> eval env (cs, List.hd stk :: stk, (s, i, o)) p
                    | SWAP          -> let x::y::stk' = stk in
                                       eval env (cs, y::x::stk', (s, i, o)) p
                    | TAG t         -> let x::stk' = stk in
                                       eval env (cs, (Value.of_int
                                       @@ match x with Value.Sexp (t', _) when t' = t -> 1 | _ -> 0) :: stk', (s, i, o)) p
                    | ENTER xs      -> let vs, stk' = split (List.length xs) stk in
                                       eval env (cs, stk',
                                       (State.push s (List.fold_left (fun s (x, v) -> State.bind x v s)
                                       State.undefined (List.combine xs vs)) xs, i, o)) p
                    | LEAVE         -> eval env (cs, stk, (State.drop s, i, o)) p
                 )
    | [] -> (cs, stk, (s, i, o))

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (*print_prg p;*)
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
           let (st, i, o, r) = Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           (*Printf.printf "Builtin:\n";*)
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let labels =
      object
          val mutable cnt = 0 (* number of used labels *)
          method newLabel infix =
              cnt <- cnt + 1; Printf.sprintf "L_%s%d" infix cnt
      end

let compileBody prog =
  let rec pattern lfalse depth = function
  | Stmt.Pattern.Wildcard       -> false, [DROP]
  | Stmt.Pattern.Ident _        -> false, [DROP]
  | Stmt.Pattern.Sexp (t, ps) -> true, [TAG t] @ [CDRNJ ("z", depth, lfalse)] @ (
                                     List.flatten @@
                                       List.mapi
                                       (fun i p -> [DUP; CONST i; CALL (".elem", 2, true)] @
                                           [DUP] @ snd (pattern lfalse (depth + 1) p) @ [DROP]
                                       ) ps
                                     ) in

  let bindings p =
    let rec makeIndexedPaths p' = match p' with
      | Stmt.Pattern.Wildcard -> []  (* do nothing *)
      | Stmt.Pattern.Ident _ -> [[]] (* later: DUP; go [].length == 0 levels deeper & SWAP *)
      | Stmt.Pattern.Sexp (_, subexprs) ->
         (* concat index on current level with deeper subpaths *)
         let numerate i subexp = List.map (fun subpath -> i::subpath) (makeIndexedPaths subexp) in
         List.flatten (List.mapi numerate subexprs) in
    let takeNth n = [CONST n; CALL (".elem", 2, true)] in
    (* DUP; go deeper by indices; SWAP*)
    let takeByPath indexedPath = [DUP] @ (List.flatten (List.map takeNth indexedPath)) @ [SWAP] in
    [LABEL "bindings_dbg"] @ List.flatten (List.map takeByPath (List.rev (makeIndexedPaths p))) @ [LABEL "\\\bindings_dbg"] in

  let rec expr = function
  | Expr.Var   x                -> [LD x]
  | Expr.Const n                -> [CONST n]
  | Language.Expr.String str    -> [STRING str]
  | Expr.Binop (op, x, y)       -> expr x @ expr y @ [BINOP op]
  | Expr.Call (name, params)    -> List.flatten (List.map (expr) (List.rev params)) @ [CALL (name, List.length params, true)]
  | Expr.Array elems      -> let compiled_elems = List.concat (List.map (expr) (elems)) in
                             compiled_elems @ [CALL (".array", (List.length compiled_elems), true)]
  | Expr.Sexp (t, xs)     -> List.flatten (List.map expr xs) @ [SEXP (t, List.length xs)]
  | Expr.Elem (e, i)      -> expr e @ expr i @ [CALL (".elem", 2, true)]
  | Expr.Length e         -> expr e @ [CALL (".length", 1, true)]
  in
  let rec compile' lab =
  function
  | Stmt.Seq (s1, s2)               -> (let lab1 = labels#newLabel "seq" in
                                        let p1, used1 = compile' lab1 s1 in
                                        let p2, used2 = compile' lab s2 in
                                        p1 @ (if used1 then [LABEL lab1] else []) @ p2, used2
                                       )
  | Stmt.Assign (x, is, e)          -> (match is with
                                           | [] -> (expr e @ [ST x]), false
                                           | is -> let compiled_is = List.fold_left
                                                    (fun p id -> p @ (expr id)) [] (List.rev is) in
                                                    compiled_is @ expr e @ [STA (x, List.length is)], false)
  | Stmt.Skip                       -> [], false
  | Stmt.If (cond, b1, b2)          -> (let lelse = labels#newLabel "else" in
                                        let p1, used1 = compile' lab b1 in
                                        let p2, used2 = compile' lab b2 in
                                        expr cond @ [CJMP ("z", lelse)]
                                        @ p1 @ (if used1 then [] else [JMP lab]) @ [LABEL lelse]
                                        @ p2 @ (if used2 then [] else [JMP lab]), true
                                        )
  | Stmt.While (cond, b)            -> (let lcheck = labels#newLabel "wh_check" in
                                        let lloop = labels#newLabel "wh_loop" in
                                        let p, _ = compile' lcheck b in
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
  | Stmt.Leave                      -> [LEAVE], false
  | Stmt.Case (e, bs)               -> let n = List.length bs - 1 in
                                       let _, _, code
                                       = List.fold_left
                                          (fun (l, i, code) (p, s) ->
                                            let lFalse, jmp = if i = n then lab, []
                                                              else labels#newLabel "caseb", [JMP lab] in
                                            let _, pCode = pattern lFalse 0 p in
                                            let sBody, _ = compile' lab (Stmt.Seq (s, Stmt.Leave)) in
                                            let amLabel = match l with Some x -> [LABEL x; DUP] | None -> [] in
                                            (*(Some lFalse, i + 1, (amLabel @ pCode @ bindings p @ [DROP; LABEL labels#newLabel "_dbg_1"; ENTER (List.rev (Stmt.Pattern.vars p))] @ sBody @ jmp) :: code)*)
                                            (Some lFalse, i + 1, (amLabel @ pCode @ bindings p @ [DROP; ENTER (List.rev (Stmt.Pattern.vars p))] @ sBody @ jmp) :: code)
                                          ) (None, 0, []) bs in
                                       expr e @ [DUP] @ (List.flatten @@ List.rev code), true
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
