(*

q: a, y : a -> b |- (lambda z : a . (y z)) : a -> b

\--------V------/  \---------------V--------------/
      Context                  Statement

\-----------------------V-------------------------/
                    Judgement

*)

(* AST definitions *)
(* A type a type variable or a pair of types *)
type 'a typ =
  | YVar of 'a
  | YFun of 'a typ * 'a typ
  | YPi of string * 'a typ

(* A declaration is a variable name and a type *)
type 'a decl =
  | VDecl of string * 'a typ
  | YDecl of string

(* A Context is a list of declarations *)
type 'a ctx = 'a decl list

(* 
parser constructs string terms
converted to int terms (DeBruijn) for evaluation
*)
type 'a term =
  | TVar of 'a
  | TAbs of 'a decl * 'a term
  | TApp of 'a term * 'a term

(* A statement is a term with a type *)
type 'a stm =
  | TStm of 'a term * 'a typ
  | YStm of 'a typ

(* A judgement is a statement with a context *)
type 'a jud = Jud of 'a ctx * 'a stm
type stringjud = string jud

(* Assign DeBruijn indexes (str2int) *)
let rec ctxindex (x : string) (c : 'a ctx) : int =
  match c with
  | VDecl(v, _) :: _ when x = v -> 0
  | YDecl(v) :: _ when x = v -> 0
  | _ :: t -> 1 + ctxindex x t
  | [] -> raise (Failure ("ctxindex " ^ x))

let rec string2intTyp (t : string typ) (c : string ctx) : int typ =
  match t with
  | YVar(v) -> YVar(ctxindex v c)
  | YFun(t1, t2) -> YFun(string2intTyp t1 c, string2intTyp t2 c)
  | YPi(v, t) -> YPi(v, string2intTyp t (YDecl(v) :: c))

let string2intDecl (d : string decl) (c : string ctx) : int decl =
  match d with
  | VDecl(v, t) -> VDecl(v, string2intTyp t c)
  | YDecl(v) -> YDecl(v)

let rec string2intTerm (term : string term) (c : string ctx) : (int term) =
  match term with
  | TVar(s) -> TVar(ctxindex s c)
  | TAbs(d, t) -> TAbs(string2intDecl d c, string2intTerm t (List.append c [d]))
  | TApp(t1, t2) -> TApp((string2intTerm t1 c), (string2intTerm t2 c))

let string2intStm (stm : string stm) (c : string ctx) : (int stm) =
  match stm with
  | TStm(term, ty) -> TStm(string2intTerm term c, string2intTyp ty c)
  | YStm(ty) -> YStm(string2intTyp ty c)

let rec string2intCtxTop (c : string ctx) (top : string ctx) =
  match c with
  | h :: t -> string2intDecl h top :: string2intCtxTop t top
  | [] -> []

let string2intCtx (c : string ctx) = string2intCtxTop c c

let string2intJud (Jud(c, s) : string jud) : int jud = Jud(string2intCtx c, string2intStm s c) 

(* To String *)
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

let rec indexToName (i : int) (c : int ctx) : string =
  match c with
  | VDecl(v, _) :: _ when i = 0 -> v
  | YDecl(v) :: _ when i = 0 -> greek v
  | _ :: t -> indexToName (i - 1) t
  | [] -> raise (Failure "indexToName")

let varOfDecl (d : 'a decl) : string =
  match d with
  | VDecl(v, _) -> v
  | YDecl(v) -> v

let rec tyToString (ty : int typ) (c : int ctx) : string =
  match ty with
  | YVar(v) -> indexToName v c
  | YFun(t1, t2) -> tyToString t1 c ^ " -> " ^ tyToString t2 c
  | YPi(v, t) -> "(Π " ^ greek(v) ^ " : * . " ^ tyToString t (YDecl(v) :: c) ^ ")"

let dToString (d : int decl) (c : int ctx) : string =
  match d with
  | VDecl(v, ty) -> v ^ " : " ^ tyToString ty c
  | YDecl(v) -> greek(v) ^ " : *"

let rec tToString (t : int term) (c : int ctx) : string =
  match t with
  | TVar(v) -> indexToName v c
  | TAbs(d, t) -> "(λ " ^ dToString d c ^ " . " ^ tToString t (List.append c [d]) ^ ")"
  | TApp(t1, t2) -> "(" ^ tToString t1 c ^ " " ^ tToString t2 c ^ ")"

let rec cToStringTop (c : int ctx) (top : int ctx) : string =
  match c with
  | d :: [] -> dToString d top
  | d :: t -> dToString d top ^ ", " ^ cToStringTop t top
  | [] -> ""

let cToString (c : int ctx) : string = cToStringTop c c
    
let sToString (s : int stm) (c : int ctx) =
  match s with
  | TStm(t, ty) -> tToString t c ^ " : " ^ tyToString ty c
  | YStm(ty) -> tyToString ty c ^ " : *"

let jToString (Jud(c, s) : int jud) : string =
  cToString c ^ " |- " ^ sToString s c

(* Well-typedeness *)
let typeOfDecl (d : int decl) (c : int ctx) : int typ =
  match d with
  | VDecl(_, ty) -> ty
  | YDecl(n) -> YVar(ctxindex n c)

let yFunFrom (t : int typ) : int typ =
  match t with
  | YFun(f, _) -> f
  | _ ->
    let msg = "Expected YFun but got YVar or YPi." in
    raise (Failure msg)

let yFunTo (t : int typ) : int typ =
  match t with
  | YFun(_, t) -> t
  | _ -> 
  let msg = "Expected YFun but got YVar or YPi." in
  raise (Failure msg)

let rec typeOf (t : int term) (c : int ctx) : int typ =
  match t with
  | TVar(v) -> typeOfDecl (List.nth c v) c
  | TAbs(d, t) -> YFun((typeOfDecl d c), (typeOf t (d :: c)))
  | TApp(t1, t2) ->
    let t1y = (typeOf t1 c) in
    let t2y = (typeOf t2 c) in
    (match t1y with
     | YFun(_, _) ->
       if (yFunFrom t1y) = t2y then (yFunTo t1y)
       else raise (Failure "Type error in application")
     | YPi(_, _) -> raise (Failure "typeOf pi application not implemented yet")
     | YVar(_) -> raise (Failure "application or variable"))

(* lambda ml interface *)
let stringjToString (j : string jud) : string =
  let j = string2intJud j in
  let s = match j with Jud(c, s) ->
    (match s with
     | TStm(t, _) ->
       let ty = typeOf t c in
       "typeOf result: " ^ tyToString ty c ^ "\n"
     | YStm(_) -> "")
  in
  s ^ jToString j

(*
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
      if (yFunFrom t1y) = t2y && (yFunTo t1y) = ty then
        DApp(j, (derrive (Jud(c, Stm(t1, t1y)))), (derrive (Jud(c, Stm(t2, t2y)))))
      else
        raise (DerrivationFail(j, "Type error in application\n"))

let rec derrivationToString (d : derrivation) (linum : int) : string * int =
  let s, l =
    match d with
    | DVar(j) ->
      let js = (string_of_int linum) ^ ") " ^ (jToString j) in
      js ^ "\t (var)", linum + 1
    | DAbs(j, d1) ->
      let ds, _ = (derrivationToString d1 (linum + 1)) in
      let js = (string_of_int linum) ^ ") " ^ (jToString j) in
      ds ^ js ^ "\t (abs) of " ^ string_of_int (linum + 1), linum + 1
    | DApp(j, d1, d2) ->
      let js = (string_of_int linum) ^ ") " ^ (jToString j) in
      let s1, l1 = (derrivationToString d1 (linum + 1)) in
      let s2, l2 = (derrivationToString d2 l1) in
      s2 ^ s1 ^ js ^ "\t (appl) of " ^ string_of_int (linum + 1) ^ " and " ^ string_of_int l1, l2
  in
  s ^ "\n", l

let derriveAndPrint (j : int jud) : string =
  try let s, _ = derrivationToString (derrive j) 0 in s with
    DerrivationFail(j, s) ->
    "Failed derriving: " ^ jToString j ^ "\n" ^ s
*)
