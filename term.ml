(*

q: a, y : a -> b |> (lambda z : a . (y z)) : a -> b

\--------V------/  \---------------V--------------/
      Context                  Statement

\-----------------------V-------------------------/
                    Judgement

*)

(* AST definitions *)
(* A type a type variable or a pair of types *)
type typ =
  | YVar of string
  | YFun of typ * typ

(* A declaration is a variable name and a type *)
type decl = Decl of string * typ

(* A Context is a list of declarations *)
type ctx = Ctx of decl list
let ctxCons d c =
  match c with
  | Ctx(l) -> Ctx(d :: l)

(* 
parser constructs string terms
converted to int terms (DeBruijn) for evaluation
*)
type 'a term =
  | TVar of 'a
  | TAbs of decl * 'a term
  | TApp of 'a term * 'a term

(* A statement is a term with a type *)
type 'a stm = Stm of 'a term * typ

(* A judgement is a statement with a context *)
type 'a jud = Jud of ctx * 'a stm

type strJud = string jud (* used for main type declaration in parser *)

(* AST to string *)
let greek s =
  match s with
  | "a" -> "α"
  | "b" -> "β"
  | "g" -> "γ"
  | "G" -> "Γ"
  | "d" -> "δ"
  | "D" -> "Δ"
  | "e" -> "ϵ"
  | "E" -> "E"
  | "z" -> "ζ"
  | "Z" -> "Z"
  | "h" -> "η"
  | "H" -> "H"
  | "o" -> "θ"
  | "O" -> "Θ"
  | "i" -> "ι"
  | "k" -> "κ"
  | "L" -> "Λ"
  | "m" -> "μ"
  | "M" -> "M"
  | "v" -> "ν"
  | "x" -> "ξ"
  | "X" -> "Ξ"
  | "p" -> "π"
  | "P" -> "Π"
  | "r" -> "ρ"
  | "s" -> "σ"
  | "S" -> "Σ"
  | "t" -> "τ"
  | "T" -> "T"
  | "u" -> "υ"
  | "U" -> "ϒ"
  | "f" -> "ϕ"
  | "F" -> "Φ"
  | "c" -> "ψ"
  | "C" -> "Ψ"
  | "w" -> "ω"
  | "W" -> "Ω"
  | _ -> s

let rec tyToString(t : typ) : string =
  match t with
  | YVar(ty) -> greek ty
  | YFun(ty1, ty2) -> "(" ^ tyToString(ty1) ^ " -> " ^ tyToString(ty2) ^ ")"

let dToString (Decl(v, ty) : decl) = v ^ " : " ^ tyToString(ty)

let rec cToString (Ctx(l) : ctx) =
  match l with
  | [] -> ""
  | d :: [] -> dToString d
  | d :: t -> dToString d ^ ", " ^ cToString (Ctx(t))

let rec tToString (t : 'a term) =
  match t with
(*| TVar(v) -> v*)
(*| TVar(v) -> string_of_int v*)
  | TVar(v) -> string_of_int v  
  | TAbs(d, t) -> "(λ " ^ dToString d ^ " . " ^ (tToString t) ^ ")"
  | TApp(t1, t2) -> "(" ^ tToString t1 ^ " " ^ tToString t2 ^ ")"

let sToString (Stm(t, ty) : 'a stm) : string = tToString t ^ " : " ^ tyToString ty

let jToString (Jud(c, s) : 'a jud) : string = cToString c ^ " |> " ^ sToString s

(* string2int *)
let ctxlen (ctx : ctx) : int =
  match ctx with
  | Ctx(l) -> List.length l

(* takes a variable name and a context 
   returns the index of the variable in the context 
   or Failer of not found *)
let rec find (x : string) (Ctx(lst) : ctx) : int =
  match lst with
  | [] -> raise (Failure "Not Found")
  | Decl(h, _) :: t -> if x = h then 0 else 1 + find x (Ctx(t))

(* Assign DeBruijn indexes *)
let rec string2intTerm (term : string term) (ctx : ctx) : (int term) =
  match term with
  | TVar(s) -> TVar(find s ctx)
  | TAbs(d, t) -> TAbs(d, string2intTerm t (ctxCons d ctx))
  | TApp(t1, t2) -> TApp((string2intTerm t1 ctx), (string2intTerm t2 ctx))

let string2intStm (stm : string stm) (ctx : ctx) : (int stm) =
  match stm with
  | Stm(term, ty) -> Stm(string2intTerm term ctx, ty)

let string2intJ (Jud(c, s) : string jud) : int jud = Jud(c, string2intStm s c) 

(* Type checking *)
(* c = cutoff, d = destination *)
let rec shift (c : int) (d : int) (t : int term) : int term =
  match t with
  | TVar(i) -> if i < c then TVar(i) else TVar(i + d)
  | TAbs(x, t) -> TAbs(x, shift (c+1) d t)
  | TApp(t1, t2) -> TApp(shift c d t1, shift c d t2)
let shift d t = shift 0 d t

let rec subs (j : int) (s : int term) (t : int term) =
  match t with
  | TVar(k) ->
    if k = j then s else TVar(k)
  | TAbs(name, t1) ->
    TAbs(name, subs (j+1) (shift 1 s) t1)
  | TApp(t1, t2) ->
    TApp(subs j s t1 , subs j s t2)

let substop s t =
  shift (-1) (subs 0 (shift 1 s) t)

exception Done
let rec beta1 t =
  let isval t =
    match t with
    | TApp(_, _) -> false
    | _ -> true
  in

  match t with
  | TApp(TAbs(_,m),n) when isval n ->
      substop n m

  | TApp(v1,t2) when isval v1 ->
      let t2' = beta1 t2 in
      TApp(v1, t2')

  | TApp(t1,t2) ->
      let t1' = beta1 t1 in
      TApp(t1', t2)

  | _ -> raise Done

let rec beta t =
  try let t' = beta1 t in
    beta t'
  with Done -> t

let beta (j : int jud) : int jud =
  match j with
  | Jud(c, Stm(t, ty)) -> Jud(c, Stm(beta t, ty))
