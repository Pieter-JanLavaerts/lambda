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

let ctxCons (d : decl) (Ctx(l) : ctx) : ctx = Ctx(d :: l)

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

type 'a query =
  | WellTyped of 'a term
  | TypeAssignment of ctx * 'a term
  | TypeCheck of 'a jud
  | TermSearch of ctx * typ

(* Assign DeBruijn indexes (str2int) *)
let ctxlen (ctx : ctx) : int =
  match ctx with
  | Ctx(l) -> List.length l

let rec ctxindex (x : string) (Ctx(lst) : ctx) : int =
  match lst with
  | [] -> raise (Failure "Variable not in context")
  | Decl(h, _) :: t -> if x = h then 0 else 1 + ctxindex x (Ctx(t))

let ctxfind (x : int) (Ctx(l): ctx) : decl =
  List.nth l x

let rec string2intTerm (term : string term) (ctx : ctx) : (int term) =
  match term with
  | TVar(s) -> TVar(ctxindex s ctx)
  | TAbs(d, t) -> TAbs(d, string2intTerm t (ctxCons d ctx))
  | TApp(t1, t2) -> TApp((string2intTerm t1 ctx), (string2intTerm t2 ctx))

let string2intStm (stm : string stm) (ctx : ctx) : (int stm) =
  match stm with
  | Stm(term, ty) -> Stm(string2intTerm term ctx, ty)

let string2intJud (Jud(c, s) : string jud) : int jud = Jud(c, string2intStm s c) 

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

let rec isNewDecl (Decl(v, vy) : decl) (Ctx(l) : ctx) : bool =
  match l with
  | [] -> true
  | Decl(vh, _) :: t ->
    if vh = v
    then false
    else (isNewDecl (Decl(v, vy)) (Ctx(t)))

let rec newDecl (d : decl) (l : ctx) : decl =
  if (isNewDecl d l)
  then d
  else match d with Decl(v, vy) -> (newDecl (Decl(v ^ "'", vy)) l)

let rec cToString (Ctx(l) : ctx) =
  match l with
  | [] -> ""
  | d :: [] -> dToString d
  | d :: t ->
    let dn = (newDecl d (Ctx(l))) in
    dToString dn ^ ", " ^ cToString (Ctx(t))

let rec tToString (t : int term) (c : ctx) : string =
  match t with
  | TVar(v) ->
    (match (ctxfind v c) with Decl(v, _) -> v)
  | TAbs(d, t) ->
    let Decl(v, vy) = (newDecl d c) in
    "(λ " ^ v ^ " : " ^ (tyToString vy) ^ " . " ^ (tToString t (ctxCons (Decl(v, vy)) c)) ^ ")"
  | TApp(t1, t2) -> "(" ^ (tToString t1 c) ^ " " ^ (tToString t2 c) ^ ")"

let sToString (Stm(t, ty) : int stm) (c : ctx) : string = tToString t c ^ " : " ^ tyToString ty

let jToString (Jud(c, s) : int jud) : string = cToString c ^ " |> " ^ (sToString s c)

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

let rec typeOf (term : 'a term) (c : ctx) : typ =
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
  | DVar of int jud
  | DAbs of int jud * derrivation
  | DApp of int jud * derrivation * derrivation

exception DerrivationFail of int jud * string
let rec derrive (j : 'a jud) : derrivation =
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

let derriveAndPrint (j : int jud) : string =
  try derrivationToString (derrive j) with
    DerrivationFail(j, s) ->
    "Failed derriving: " ^ jToString j ^ "\n" ^ s

(* query to string *)
type stringquery = string query

let string2intQuery (q : string query) : int query =
  match q with
  | WellTyped(t) -> WellTyped(string2intTerm t (Ctx([])))
  | TypeAssignment(c, t) -> TypeAssignment(c, string2intTerm t c)
  | TypeCheck(j) -> TypeCheck(string2intJud j)
  | TermSearch(c, ty) -> TermSearch(c, ty)

let queryToString sq =
  let q = string2intQuery sq in
  match q with
  | WellTyped(t) ->
    "Well-typed: ? |> " ^ (tToString t (Ctx([]))) ^ " : ?"
  | TypeAssignment(c, t) ->
    let ty = (typeOf t c) in
    "Type assignment: " ^ cToString(c) ^ " |> " ^ (tToString t c)  ^ " : ?\n" ^
    let j = Jud(c, Stm(t, ty)) in derriveAndPrint(j)
  | TypeCheck(j) ->
    "Type check: " ^ jToString j ^ "\n" ^
    derriveAndPrint(j)
  | TermSearch(c, t) ->
    "Term search: " ^ cToString(c) ^ " |> ? : " ^ tyToString(t)
