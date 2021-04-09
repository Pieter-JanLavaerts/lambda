%token LAMBDA LPAREN RPAREN
%token <string> VAR
%token DERRIVES
%token ARROW COLON
%token DOT COMMA
%token EOL

%start <Term.astJud> main
%{open Term %}

%%

main:
  | j = judgement; EOL { j }

judgement:
  | c = context; DERRIVES; s = statement { AJud(c, s) }

statement:
  | t = term; COLON; ty = typ { AStm(t, ty) }

term:
  | v = var { ATVar(v) }
  | LPAREN; LAMBDA;  d = decl; DOT; t = term; RPAREN { ATAbs(d, t) }
  | LPAREN; t1 = term; t2 = term; RPAREN { ATApp(t1, t2) }

context:
  | d = decl; { ACtx([d]) }
  | d = decl; COMMA; c = context { ctxCons d c }

decl:
  | v = var; COLON; ty = typ { ADecl(v, ty) }

typ:
  | v = var { AYVar(v) }
  | LPAREN; ty1 = typ; ARROW; ty2 = typ; RPAREN { AYFun(ty1, ty2) }

var:
  | v = VAR { AVar(v) }
					 
