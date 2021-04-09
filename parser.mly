%token LAMBDA LPAREN RPAREN
%token <string> VAR
%token DOT
%token EOL

%start <Term.ast> main
%{open Term %}

%%

main:
  | t = term; EOL { t }

term:
  | v = VAR { AVar(v) }
  | LPAREN; a1 = term; a2 = term; RPAREN { AApp(a1, a2) }
  | LPAREN LAMBDA; v = VAR; DOT; a = term; RPAREN { AAbs(v, a) }

