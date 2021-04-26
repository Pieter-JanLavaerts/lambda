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
  | { [] }
  | d = decl { [d] }
  | d = decl; COMMA; c = context { d :: c }
  | d = decl; c = context { d :: c }

decl:
  | v = VAR; COLON; ty = typ { VDecl(v, ty) }
  | v = VAR; COLSTAR { YDecl(v) }

typ:
  | LPAREN; t = typ1; RPAREN { t }
  | t = typ1 { t }

typ1:
  | v = VAR { YVar(v) }
  | ty1 = typ; ARROW; ty2 = typ { YFun(ty1, ty2) }
  | p = pi { p }

pi:
  | PI; p = innerpi { p }

innerpi:
  | v = VAR; COLSTAR; DOT; ty = typ { YPi(v, ty) }
  | v = VAR; COLSTAR?; COMMA?; p = innerpi { YPi(v, p) }
