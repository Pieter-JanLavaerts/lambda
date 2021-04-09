open Term

let process (line : string) =
  let linebuf = Lexing.from_string line in
  try
    (* Run the parser on this line of input. *)
    let AStm(res, _) = (Parser.main Lexer.token linebuf) in
    let term = ast2term res in
    let vars = freevars res in
    Printf.printf "=> %s\n%!" (term2string (eval term) vars)
  with
  | Lexer.Error msg ->
      Printf.fprintf stderr "%s%!" msg
  | Parser.Error ->
      Printf.fprintf stderr "At offset %d: syntax error.\n%!" (Lexing.lexeme_start linebuf)

let process (optional_line : string option) =
  match optional_line with
  | None ->
    ()
  | Some line ->
      process line

let rec repeat channel =
  (* Attempt to read one line. *)
  let optional_line, continue = Lexer.line channel in
  process optional_line;
  if continue then
    repeat channel
  
let () =
  repeat (Lexing.from_channel stdin)
