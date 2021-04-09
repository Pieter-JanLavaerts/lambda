%token LAMBDA LPAREN RPAREN
%token <string> VAR
%token DERRIVES
%token ARROW COLON
%token DOT COMMA
%token EOL

%start <Term.strJud> main
%{open Term %}

%%

main:
  | j = judgement; EOL { j }

judgement:
  | c = context; DERRIVES; s = statement { Jud(c, s) }

statement:
  | t = term; COLON; ty = typ { Stm(t, ty) }

term:
  | v = var { TVar(v) }
  | LPAREN; LAMBDA;  d = decl; DOT; t = term; RPAREN { TAbs(d, t) }
  | LPAREN; t1 = term; t2 = term; RPAREN { TApp(t1, t2) }

context:
  | { Ctx([]) }
  | d = decl { ctxCons d (Ctx([])) }
  | d = decl; COMMA; c = context { ctxCons d c }

decl:
  | v = var; COLON; ty = typ { Decl(v, ty) }

typ:
  | v = var { YVar(v) }
  | LPAREN; ty1 = typ; ARROW; ty2 = typ; RPAREN { YFun(ty1, ty2) }

var:
  | v = VAR { Var(v) }
					 
