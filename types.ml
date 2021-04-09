module Expr = 
struct
  type expr =
    | Variable of int
    | Application of expr
end;;
