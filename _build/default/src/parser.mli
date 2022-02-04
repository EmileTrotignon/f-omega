
(* The type of tokens. *)

type token = 
  | VAL
  | TYPE
  | TTYPE
  | STRING of (string)
  | STAR
  | SEMI
  | RPAREN
  | REC
  | RBRACKET
  | RBRACE
  | RANGLE
  | OPTION
  | LPAREN
  | LIDENT of (string)
  | LET
  | LBRACKET
  | LBRACE
  | LANGLE
  | LAMBDA
  | INT of (int)
  | INCLUDE
  | IN
  | FUN
  | EXI
  | EQUAL
  | EOF
  | DOUBLEARROW
  | DOT
  | DOLAR
  | COMMA
  | COLONCOLON
  | COLON
  | CIDENT of (string)
  | AS
  | ARROW
  | ALL

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val typ_: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Syntax.styp_loc)

val program: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Syntax.directive list * Syntax.program)

val interface: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Syntax.svar Syntax.typed_decl_ list)

val exp_: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Syntax.exp)

val decl_: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Syntax.decl)
