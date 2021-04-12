%token LAMBDA LPAREN RPAREN
%token <string> VAR
%token DERRIVES
%token ARROW COLON
%token DOT COMMA
%token QUESTION EOL

%start <Term.stringquery> main

%right ARROW

%{open Term %}

%%

main:
  | QUESTION; DERRIVES; t = term; COLON; QUESTION; EOL { WellTyped(t) }
  | c = context; DERRIVES; t = term; COLON; QUESTION; EOL { TypeAssignment(c, t) }
  | j = judgement; EOL { TypeCheck(j) }
  | c = context; DERRIVES; QUESTION; COLON; t = typ; EOL { TermSearch(c, t) }

judgement:
  | c = context; DERRIVES; s = statement { Jud(c, s) }

statement:
  | t = term; COLON; ty = typ { Stm(t, ty) }

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
  | v = VAR; COLON; ty = typ { Decl(v, ty) }

typ:
  | v = VAR { YVar(v) }
  | LPAREN; ty1 = typ; ARROW; ty2 = typ; RPAREN { YFun(ty1, ty2) }
  | ty1 = typ; ARROW; ty2 = typ { YFun(ty1, ty2) }
