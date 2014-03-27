(*  A modular module system.
    The lexical analyzer for core-C.

    Copyright 1999 Xavier Leroy.
    This file is distributed under the GNU Public Licence. *)

{

exception Lexical_error of string
(* Auxiliary Caml code *)

open MiniCparser

(* The table of keywords and infixes *)

let keyword_table = (Hashtbl.create 17 : (string, token) Hashtbl.t)

let _ = List.iter (fun (str,tok) -> Hashtbl.add keyword_table str tok)
  [ "else", ELSE;
    "end", END;
    "float", FLOAT;
    "for", FOR;
    "functor", FUNCTOR;
    "if", IF;
    "int", INT;
    "module", MODULE;
    "return", RETURN;
    "sig", SIG;
    "struct", STRUCT;
    "typedef", TYPEDEF;
    "void", VOID ]

(* End of auxiliary Caml definitions *)
}

(* Lexer rules *)

rule token = parse
    [ ' ' '\010' '\013' '\009' '\012' ] +
            { token lexbuf }
  | [ 'a'-'z' '_' ] [ 'A'-'Z' 'a'-'z' '0'-'9' '_' ] *
            { let s = Lexing.lexeme lexbuf in
              try
                Hashtbl.find keyword_table s
              with Not_found ->
                LIDENT s }
  | [ 'A'-'Z' ] [ 'A'-'Z' 'a'-'z' '0'-'9' '_' ] *
            { UIDENT(Lexing.lexeme lexbuf) }
  |   ['1'-'9'] ['0'-'9']*
    | '0' ['x' 'X'] ['0'-'9' 'A'-'F' 'a'-'f']+
    | '0' ['0'-'7']+
            { INTCONST (int_of_string(Lexing.lexeme lexbuf)) }
  | ['0'-'9']+ ('.' ['0'-'9']*)? (['e' 'E'] ['+' '-']? ['0'-'9']+)?
            { FLOATCONST (float_of_string(Lexing.lexeme lexbuf)) }
  | "/*"
            { comment lexbuf; token lexbuf }
  
  | "!" { BANG }
  | "!=" { BANGEQUAL }
  | ":" { COLON }
  | "," { COMMA }
  | "." { DOT }
  | "=" { EQUAL }
  | "==" { EQUALEQUAL }
  | ">" { GREATER }
  | ">=" { GREATEREQUAL }
  | "{" { LBRACE }
  | "[" { LBRACKET }
  | "<" { LESS }
  | "<=" { LESSEQUAL }
  | "(" { LPAREN }
  | "-" { MINUS }
  | "+" { PLUS }
  | "}" { RBRACE }
  | "]" { RBRACKET }
  | ")" { RPAREN }
  | ";" { SEMI }
  | "/" { SLASH }
  | "*" { STAR }

  | eof     { EOF }

  | _       { raise(Lexical_error "illegal character") }

and comment = parse
    "*/"
            { () }
  | eof
            { raise (Lexical_error "comment not terminated") }
  | _
            { comment lexbuf }

