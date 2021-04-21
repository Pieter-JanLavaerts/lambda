(*

q: a, y : a -> b |- (lambda z : a . (y z)) : a -> b

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
    let dn = (newDecl d (Ctx(t))) in
    dToString dn ^ ", " ^ cToString (Ctx(t))

let ctxfind (x : int) (Ctx(l): ctx) : decl =
  try List.nth l x with
    Failure _ ->
    raise (Failure ("ctxfind " ^ string_of_int x ^ " [" ^ (cToString (Ctx(l))) ^ "]"))

let rec tToString (t : int term) (c : ctx) : string =
  match t with
  | TVar(v) ->
    (match (ctxfind v c) with Decl(v, _) -> v)
  | TAbs(d, t) ->
    let Decl(v, vy) = (newDecl d c) in
    "(λ " ^ v ^ " : " ^ (tyToString vy) ^ " . " ^ (tToString t (ctxCons (Decl(v, vy)) c)) ^ ")"
  | TApp(t1, t2) -> "(" ^ (tToString t1 c) ^ " " ^ (tToString t2 c) ^ ")"

let sToString (Stm(t, ty) : int stm) (c : ctx) : string = tToString t c ^ " : " ^ tyToString ty

let jToString (Jud(c, s) : int jud) : string = cToString c ^ " |- " ^ (sToString s c)

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

(* TermSearch *)

let rec prodSearchNth (Ctx(l) : ctx) (ty : typ) : int =
  match l with
  | Decl(_, YFun(_, right)) :: _ when ty = right -> 0
  | _ :: tail -> 1 + (prodSearchNth (Ctx(tail)) ty)
  | [] -> raise (Failure "appSearch")

let rec replacenth (l : 'a list) (n : int) (elt : 'a) : 'a list =
  match l with
  | [] -> raise (Failure "replacenth")
  | h :: t ->
    if n = 0 then elt :: t
    else h :: (replacenth t (n - 1) elt)

let rec varSearchNth (Ctx(l) : ctx) (ty : typ) : int =
  match l with
  | Decl(_, h) :: t -> if h = ty then 0 else (1 + (varSearchNth (Ctx(t)) ty))
  | [] -> raise (Failure ("varSearch" ^ (cToString (Ctx(l)) ^ ", " ^ (tyToString ty))))

let appSearch (Ctx(lst) : ctx) (ty : typ) : int term =
  let c = Ctx(lst) in
  let n = prodSearchNth c ty in
  let d = List.nth lst n in
  let Decl(ntv, nty) = d in
  match nty with
  | YFun(l, r) -> TApp(TVar(n), TVar((varSearchNth (Ctx(replacenth lst n (Decl(ntv, r)))) l)))
  | _ -> raise (Failure "This wil never trigger")

let rec searchTerm (c : ctx) (ty : typ) : int term =
  try TVar(varSearchNth c ty) with
    Failure f1 ->
    (try (appSearch c ty) with
       Failure f2 ->
       (match ty with
        | YFun(l, r) -> TAbs(Decl("x", l), (searchTerm (ctxCons (Decl("x", l)) c) r))
        | YVar(_) -> raise (Failure ("searchTerm " ^ f1 ^ " " ^ f2))))

(* query to string *)
type stringquery = string query

let string2intQuery (q : string query) : int query =
  match q with
  | WellTyped(t) -> WellTyped(string2intTerm t (Ctx([])))
  | TypeAssignment(c, t) -> TypeAssignment(c, string2intTerm t c)
  | TypeCheck(j) -> TypeCheck(string2intJud j)
  | TermSearch(c, ty) -> TermSearch(c, ty)

let rec numFreeVars t =
  match t with
  | TVar(_) -> 1
  | TAbs(_, t2) -> (numFreeVars t2) - 1
  | TApp(t1, t2) -> (numFreeVars t1) + (numFreeVars t2)

let queryToString sq =
  match sq with
  | WellTyped(ts) ->
    if numFreeVars ts = 0 then
      let c = Ctx([]) in
      let t = string2intTerm ts c in
      let ty = (typeOf t c) in
      let j = Jud(c, Stm(t, ty)) in
      "Well typed:  ? |- " ^ (tToString t c)  ^ " : ?\n" ^
      derriveAndPrint(j)
    else
      string_of_int (numFreeVars ts) ^ " free variable(s).\n"
  | TypeAssignment(Ctx(l), ts) ->
    let fv = numFreeVars ts in
    let len = List.length l in
    if fv > len then
      "More free variables (" ^ string_of_int fv ^ ") than size of context (" ^ string_of_int len ^ "). \n"
    else
      let c = Ctx(l) in
      let t = string2intTerm ts c in
      let ty = (typeOf t c) in
      "Type assignment: " ^ cToString(c) ^ " |- " ^ (tToString t c)  ^ " : ?\n" ^
      let j = Jud(c, Stm(t, ty)) in derriveAndPrint(j)
  | TypeCheck(j) ->
    "Type check: " ^ jToString (string2intJud j) ^ "\n" ^
    derriveAndPrint(string2intJud j)
  | TermSearch(c, ty) ->
    "Term search: " ^ cToString(c) ^ " |- ? : " ^ tyToString(ty) ^ "\n" ^
    let t = (searchTerm c ty) in
    let j = Jud(c, Stm(t, ty)) in
    derriveAndPrint(j)
