(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators

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
    let push_scope st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let drop_scope st st' = {st' with g = st.g}

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
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)    
    
    let rec eval st expr =      
      match expr with
      | Const n -> n
      | Var   x -> State.eval st x
      | Binop (op, x, y) -> to_func op (eval st x) (eval st y)

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)
    ostap (                                      
      parse:
	  !(Ostap.Util.expr 
             (fun x -> x)
	     (Array.map (fun (a, s) -> a, 
                           List.map  (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s
                        ) 
              [|                
		`Lefta, ["!!"];
		`Lefta, ["&&"];
		`Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
		`Lefta, ["+" ; "-"];
		`Lefta, ["*" ; "/"; "%"];
              |] 
	     )
	     primary);
      
      primary:
        n:DECIMAL {Const n}
      | x:IDENT   {Var x}
      | -"(" parse -")"
    )
    
  end

let unwrap o = match o with
    | None -> []
    | Some l -> l
                    
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

       which returns a list of formal parameters and a body for given definition
    *)
    let rec eval env (s, i, o) stmt =
                match stmt with
                    | Read x -> (match i with
                                    | z::t -> State.update x z s, t, o
                                    | _ -> failwith "Read from empty input"
                                )
                    | Write e -> s, i, o @ [Expr.eval s e]
                    | Assign (x, e) -> State.update x (Expr.eval s e) s, i, o
                    | Seq (st1, st2) -> eval env (eval env (s, i, o) st1) st2
                    | Skip -> s, i, o
                    | If (cond, st1, st2)-> (
                        let res = Expr.eval s cond in
                        if res = 0
                        then eval env (s, i, o) st2
                        else  eval env (s, i, o) st1
                    )
                    | While (cond, st) -> (
                        let res = Expr.eval s cond in
                        if res = 0
                        then s, i, o
                        else eval env (eval env (s, i, o) st) (While (cond, st))
                    )
                    | Repeat (st, cond) -> (
                        let (s', i', o') = eval env (s, i, o) st in
                        let res = Expr.eval s' cond in
                        if res != 0
                        then s', i', o'
                        else eval env (s', i', o') (Repeat (st, cond))
                    )
                    | Call (func, param_exprs) -> (
                        let (args, locals, body) = env#definition func in
                        let params = List.map (Expr.eval s) param_exprs in
                        let upd s x v = State.update x v s in
                        let s' = State.push_scope s (args @ locals) in
                        let s' = List.fold_left2 upd s' args params in
                        let (s'', i, o) = eval env (s', i, o) body in
                        (State.drop_scope s'' s, i, o)
                    )
                                
    (* Statement parser *)
    ostap (                                      
      stmt:
          f:IDENT "(" params:lst? ")"                    {Call (f, unwrap params)} |
          "read"  "(" x:IDENT ")"                        {Read x}           |
          "write" "(" e:!(Expr.parse) ")"                {Write e}          |
          x:IDENT  ":=" e:!(Expr.parse)                  {Assign (x, e)}    |
          b: (iff | forr | whil | repeat)                {b}                |
          "skip"                                         {Skip};
      lst:
          a:!(Expr.parse) "," tail:lst                   {a::tail} |
          a:!(Expr.parse)                                {[a]};
      repeat:
          "repeat" b:parse
          "until" cond:!(Expr.parse)                     {Repeat (b, cond)};
      forr:
          "for" a:stmt
          "," cond:!(Expr.parse)
          "," st:stmt
          "do" b:parse
          "od"                                           {Seq (a, While (cond, Seq(b, st)))};
      iff:
          "if" e:!(Expr.parse)
              "then" thb:parse
              elb:elif?
              "fi"                                       {If (e, thb, match elb with Some b -> b | None -> Skip)};
      elif:
          "else" eb:parse                                {eb}              |
          "elif" e:!(Expr.parse)
              "then" thb:parse
              elb:elif                                   {If (e, thb, elb)};
      whil:
          "while" cond:!(Expr.parse)
          "do" b:parse
          "od"                                           {While (cond, b)};
      parse:
          st:stmt ";" tail:parse                         {Seq (st, tail)}   |
          stmt
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (                                      
      parse:
        "fun" name:IDENT "(" args:lst? ")" locals:(-"local" lst)? "{" body:!(Stmt.parse)? "}"
                {name, (unwrap args, unwrap locals, match body with Some s -> s | _ -> Stmt.Skip)};
      lst:
        a:IDENT "," tail:lst {a::tail} |
        a:IDENT               {[a]}
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
  let m        = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o  = Stmt.eval (object method definition f = snd @@ M.find f m end) (State.empty, i, []) body in o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
