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

let rec ctxindex (x : string) (Ctx(lst) : ctx) : int =
  match lst with
  | [] -> raise (Failure "Variable not in context")
  | Decl(h, _) :: t -> if x = h then 0 else 1 + ctxindex x (Ctx(t))

let ctxfind (x : string) (Ctx(lst) : ctx) : decl =
  List.nth lst (ctxindex x (Ctx(lst)))

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

type query =
  | WellTyped of string term
  | TypeAssignment of ctx * string term
  | TypeCheck of string jud
  | TermSearch of ctx * typ

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
  | TVar(v) -> v  
  | TAbs(d, t) -> "(λ " ^ dToString d ^ " . " ^ (tToString t) ^ ")"
  | TApp(t1, t2) -> "(" ^ tToString t1 ^ " " ^ tToString t2 ^ ")"

let sToString (Stm(t, ty) : 'a stm) : string = tToString t ^ " : " ^ tyToString ty

let jToString (Jud(c, s) : 'a jud) : string = cToString c ^ " |> " ^ sToString s

(* string2int *)
let ctxlen (ctx : ctx) : int =
  match ctx with
  | Ctx(l) -> List.length l

(* Assign DeBruijn indexes *)
let rec string2intTerm (term : string term) (ctx : ctx) : (int term) =
  match term with
  | TVar(s) -> TVar(ctxindex s ctx)
  | TAbs(d, t) -> TAbs(d, string2intTerm t (ctxCons d ctx))
  | TApp(t1, t2) -> TApp((string2intTerm t1 ctx), (string2intTerm t2 ctx))

let string2intStm (stm : string stm) (ctx : ctx) : (int stm) =
  match stm with
  | Stm(term, ty) -> Stm(string2intTerm term ctx, ty)

let string2intJ (Jud(c, s) : string jud) : int jud = Jud(c, string2intStm s c) 

(* Well-typedeness *)
let typeOfDecl (d : decl) : typ =
  match d with Decl(_, ty) -> ty

let yFunFrom (t : typ) : typ =
  match t with
  | YFun(f, _) -> f
  | _ ->
    let msg = "Expected YFun but got " ^ (tyToString t) ^ "." in
    raise (Failure msg)

let yFunTo (t : typ) : typ =
  match t with
  | YFun(_, t) -> t
  | _ -> 
  let msg = "Expected YFun but got " ^ (tyToString t) ^ "." in
  raise (Failure msg)

let rec typeOf (term : string term) (c : ctx) : typ =
  match term with
  | TVar(v) -> typeOfDecl(ctxfind v c)
  | TAbs(d, t) -> YFun((typeOfDecl d), (typeOf t (ctxCons d c)))
  | TApp(t1, t2) ->
    let t1y = (typeOf t1 c) in
    let t2y = (typeOf t2 c) in
    if (yFunFrom t1y) = t2y then (yFunTo t1y)
    else raise (Failure "Type error in application")

(* Type checking *)
type derrivation = 
  | DVar of string jud
  | DAbs of string jud * derrivation
  | DApp of string jud * derrivation * derrivation

exception DerrivationFail of string jud * string
let rec derrive (j : string jud) : derrivation =
  match j with
  | Jud(c, Stm(t, ty)) ->
    match t with
    | TVar(v) ->
      let Decl(_, cty) = (ctxfind v c) in
      if ty = cty then
        DVar(j)
      else
        let msg = "Expected type of " ^ (tyToString ty) ^
                  " but found " ^ (tyToString cty) in
        raise (DerrivationFail(j, msg))
    | TAbs(Decl(x, xty), t) ->
      (match ty with
       | YFun(lty, rty) ->
         if lty = xty then
           DAbs(j, (derrive (Jud((ctxCons (Decl(x, xty)) c), Stm(t, rty)))))
         else
           let msg = "Expected abstraction parameter of " ^ (tyToString lty) ^ " but got " ^ (tyToString ty) in
           raise (DerrivationFail(j, msg))
       | YVar(_) ->
         let msg = "Abstraction with non function type " ^ (tyToString ty) ^ "." in
         raise (DerrivationFail(j, msg)))
    | TApp(t1, t2) ->
      let t1y = (typeOf t1 c) in
      let t2y = (typeOf t2 c) in
      if (yFunFrom t1y) = t2y then
        DApp(j, (derrive (Jud(c, Stm(t1, t1y)))), (derrive (Jud(c, Stm(t2, t2y)))))
      else
        raise (DerrivationFail(j, "Type error in application"))

let rec derrivationToString (d : derrivation) =
    match d with
    | DVar(j) -> jToString(j) ^ "\t (var)\n"
    | DAbs(j, d) -> derrivationToString(d) ^ jToString(j) ^ "\t (abs) \n"
    | DApp(j, d1, d2) -> derrivationToString(d1) ^ derrivationToString(d2) ^ jToString(j) ^ "\t (app) \n"

let derriveAndPrint (j : string jud) : string =
  try derrivationToString (derrive j) with
    DerrivationFail(j, s) ->
    "Failed derriving: " ^ jToString j ^ "\n" ^ s

(* query to string *)
let queryToString q =
  match q with
  | WellTyped(t) ->
    "Well-typed: ? |> " ^ tToString(t) ^ " : ?"
  | TypeAssignment(c, t) ->
    let ty = (typeOf t  c) in
    "Type assignment: " ^ cToString(c) ^ " |> " ^ tToString(t) ^ " : ?\n" ^
    let j = Jud(c, Stm(t, ty)) in derriveAndPrint(j)
  | TypeCheck(j) ->
    "Type check: " ^ jToString j ^ "\n" ^
    derriveAndPrint(j)
  | TermSearch(c, t) ->
    "Term search: " ^ cToString(c) ^ " |> ? : " ^ tyToString(t)
