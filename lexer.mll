{
  open Parser

  exception Error of string

}

(* This rule looks for a single line, terminated with '\n' or eof.
   It returns a pair of an optional string (the line that was found)
   and a Boolean flag (false if eof was reached). *)

rule line = parse
| ([^'\n']* '\n') as line
    (* Normal case: one line, no eof. *)
    { Some line, true }
| eof
    (* Normal case: no data, eof. *)
    { None, false }
| ([^'\n']+ as line) eof
    (* Special case: some data but missing '\n', then eof.
       Consider this as the last line, and add the missing '\n'. *)
    { Some (line ^ "\n"), false }

(* This rule analyzes a single line and turns it into a stream of
   tokens. *)

and token = parse
| [' ' '\t']
    { token lexbuf }
| [ '\n' ]
    { EOL }
| "pi"
    { PI }
| "lambda"
    { LAMBDA }
| "|-"
    { DERRIVES }
| "->"
    { ARROW }
| ":" " "* "*"
    { COLSTAR }
| ":"
    { COLON }
| [ '(' ]
    { LPAREN }
| [ ')' ]
    { RPAREN }
| [ '.' ]
    { DOT }
| [ ',' ]
    { COMMA }
| [ '?' ]
    { QUESTION }
| ['A'-'Z' 'a'-'z' '_']
  ['A'-'Z' 'a'-'z' '_' '0'-'9' '\'']*
    { VAR (Lexing.lexeme lexbuf) }
