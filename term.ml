(* ast is returned from the parser *)
type astTerm =
  | AVar of string
  | AAbs of string * astTerm
  | AApp of astTerm * astTerm

type astType =
  | ATVar of string
  | ATFun of astType * astType

type astStm = AStm of astTerm * astType

let getTerm stm =
  match stm with AStm(t, _) -> t;

(* 
TVar(len, x)
len is the length of the context for consistency checking
x is the Debruijn index 
*)
type term = 
  | TVar of int * int
  | TAbs of string * term
  | TApp of term * term

type context = string list
let ctxlen ctx = List.length ctx

(* Constructing terms from ast *)
let rec find x lst =
    match lst with
    | [] -> raise (Failure "Not Found")
    | h :: t -> if x = h then 0 else 1 + find x t

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

let a =
  AApp(
    AApp(
      AAbs("f", AAbs("x", AApp(AVar("f"), AApp(AVar("f"), AVar("x"))))), (* 2 *)

      AAbs("x", AApp(AVar("x"), AVar("x"))) (* (\x.x x) *)
    ),
    AVar("x")
  )
      
