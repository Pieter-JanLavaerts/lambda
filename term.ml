(* ast *)

type typ =
  | YVar of string
  | YFun of typ * typ

type decl = Decl of string * typ

type ctx = Ctx of decl list
let ctxCons d c =
  match c with
  | Ctx(l) -> Ctx(d :: l)

type 'a term =
  | TVar of 'a
  | TAbs of decl * 'a term
  | TApp of 'a term * 'a term

type 'a stm = Stm of 'a term * typ

type 'a jud = Jud of ctx * 'a stm

type strJud = string jud (* used for main type declaration in parser *)

(* to string *)
let rec tyToString(t : typ) : string =
  match t with
  | YVar(ty) -> ty
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
  | TAbs(d, t) -> "(lambda " ^ dToString d ^ " . " ^ (tToString t) ^ ")"
  | TApp(t1, t2) -> "(" ^ tToString t1 ^ " " ^ tToString t2 ^ ")"
let sToString (Stm(t, ty) : 'a stm) : string = tToString t ^ " : " ^ tyToString ty
let jToString (Jud(c, s) : 'a jud) : string = cToString c ^ " |> " ^ sToString s
  

(* str2int *)
let ctxlen (ctx : ctx) : int =
  match ctx with
  | Ctx(l) -> List.length l

let rec find (x : string) (Ctx(lst) : ctx) : int =
  match lst with
  | [] -> raise (Failure "Not Found")
  | Decl(h, _) :: t -> if x = h then 0 else 1 + find x (Ctx(t))

let rec string2intTerm (term : string term) (ctx : ctx) : (int term) =
  match term with
  | TVar(s) -> TVar(find s ctx)
  | TAbs(d, t) -> TAbs(d, string2intTerm t (ctxCons d ctx))
  | TApp(t1, t2) -> TApp((string2intTerm t1 ctx), (string2intTerm t2 ctx))

let string2intStm (stm : string stm) (ctx : ctx) : (int stm) =
  match stm with
  | Stm(term, ty) -> Stm(string2intTerm term ctx, ty)

let string2intJ (Jud(c, s) : string jud) : int jud = Jud(c, string2intStm s c) 

let eval j = jToString j

(*
(* Constructing terms from ast *)

let rec ast2termf ast ctx =
  match ast with
  | AVar(s) ->
    TVar(ctxlen ctx, find s ctx)
  | AAbs(s, t) ->
    TAbs(s, ast2termf t (s :: ctx))
  | AApp(a1, a2) ->
    TApp(ast2termf a1 ctx, ast2termf a2 ctx)

let rec freevars ast =
  let vars = 
    match ast with
    | AVar(s) ->
      [s]
    | AAbs(s, t) ->
      let f x = not (x = s) in
      List.filter f (freevars t)
    | AApp(a1, a2) ->
      List.append (freevars a1) (freevars a2)
  in
  List.sort_uniq String.compare vars

let ast2term ast =
  let vars = freevars ast in
  ast2termf ast vars

(* Printing terms *)
let pickname ctx name =
  if List.mem name ctx then
    let name' = name^"'" in
    (List.cons name' ctx, name')
  else
    (List.cons name ctx, name)

let rec term2string trm ctx =
  match trm with
  | TVar(n, x) ->
    if n <= ctxlen ctx then
      (List.nth ctx x)
    else
      Printf.sprintf "[bad index %d != %d]" n (ctxlen ctx)
  | TAbs(name, t) ->
    let (ctx', name') = pickname ctx name in
    "(lambda " ^ name' ^ " . " ^ term2string t ctx' ^ ")"
  | TApp(t1, t2) ->
    "(" ^ term2string t1 ctx ^ " " ^ term2string t2 ctx ^ ")"

(* Evaluation of terms *)
let rec shift c d t =
  match t with
  | TVar(n, k) ->
    if k < c then TVar(n, k) else TVar(n, k + d)
  | TAbs(name, t) ->
    TAbs(name, shift (c+1) d t)
  | TApp(t1, t2) ->
    TApp(shift c d t1, shift c d t2)

let shift d t = shift 0 d t

let rec subs j s t =
  match t with
  | TVar(n, k) ->
    if k = j then s else TVar(n, k)
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

let eval = beta
 *)
