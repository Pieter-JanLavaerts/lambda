%token LAMBDA LPAREN RPAREN
%token <string> VAR
%token ARROW COLON
%token DOT
%token EOL

%start <Term.astStm> main
%{open Term %}

%%

main:
  | s = stm; EOL { s }

stm:
  | t = term; COLON; ty = typ {AStm(t, ty)}

typ:
  | v = VAR { ATVar(v) }
  | LPAREN; t1 = typ; ARROW; t2 = typ; RPAREN { ATFun(t1, t2) }

term:
  | v = VAR { AVar(v) }
  | LPAREN; a1 = term; a2 = term; RPAREN { AApp(a1, a2) }
  | LPAREN LAMBDA; v = VAR; DOT; a = term; RPAREN { AAbs(v, a) }

