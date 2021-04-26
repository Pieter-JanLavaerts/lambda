%token PI LAMBDA LPAREN RPAREN
%token <string> VAR
%token DERRIVES
%token COLSTAR ARROW COLON
%token DOT COMMA
%token QUESTION EOL

%start <Term.stringjud> main

%right ARROW

%{open Term %}

%%

main:
  | c = context; DERRIVES; s = statement; EOL { Jud(c, s) }

statement:
  | t = term; COLON; ty = typ { TStm(t, ty) }
  | ty = typ; COLSTAR { YStm(ty) }

term:
  | t = term2 { t }
  | l = lambda { l }

term2:
  | t = term3 { t }
  | tl = term2; t2 = term3 { TApp(tl, t2) }

term3:
  | v = VAR { TVar(v) }
  | LPAREN; l = lambda; RPAREN { l }
  | LPAREN; t1 = term2; t2 = term2; RPAREN { TApp(t1, t2) }

lambda:
  | LAMBDA; l = innerlambda { l }

innerlambda:
  | d = decl; DOT; t = term { TAbs(d, t) }
  | d = decl; COMMA?; l = innerlambda { TAbs(d, l) }

context:
  | { Ctx([]) }
  | d = decl { ctxCons d (Ctx([])) }
  | d = decl; COMMA; c = context { ctxCons d c }
  | d = decl; c = context { ctxCons d c }

decl:
  | v = VAR; COLON; ty = typ { VDecl(v, ty) }
  | v = VAR; COLSTAR { YDecl(v) }

typ:
  | v = VAR { YVar(v) }
  | LPAREN; ty1 = typ; ARROW; ty2 = typ; RPAREN { YFun(ty1, ty2) }
  | ty1 = typ; ARROW; ty2 = typ { YFun(ty1, ty2) }
  | LPAREN; PI; v = VAR; COLSTAR; DOT; ty = typ; RPAREN { YPi(v, ty) }
