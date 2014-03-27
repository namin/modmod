(*  A modular module system.
    The lexical analyzer for mini-ML.

    Copyright 1999 Xavier Leroy.
    This file is distributed under the GNU Public Licence. *)

{
(* Auxiliary Caml code *)

exception Lexical_error of string

open MiniMLparser             (* "parser" provides the type for tokens. *)

(* The table of keywords and infixes *)

let keyword_table = (Hashtbl.create 17 : (string, token) Hashtbl.t)

let _ = List.iter (fun (str,tok) -> Hashtbl.add keyword_table str tok)
 ["function", FUNCTION;
  "fun", FUNCTION;
  "let", LET;
  "struct", STRUCT;
  "end", END;
  "functor", FUNCTOR;
  "val", VALUE;
  "type", TYPE;
  "module", MODULE;
  "sig", SIG;
  "in", IN;
  "if", IF;
  "then", THEN;
  "else", ELSE]

(* End of auxiliary Caml definitions *)
}

(* Lexer rules *)

rule token = parse
    [ ' ' '\010' '\013' '\009' '\012' ] +
            { token lexbuf }
  | [ 'A'-'Z' 'a'-'z' '\192'-'\214' '\216'-'\246' '\248'-'\254' ]
    [ 'A'-'Z' 'a'-'z' '\192'-'\214' '\216'-'\246' '\248'-'\254'
      '0'-'9' '_' '\'' ] *
            { let s = Lexing.lexeme lexbuf in
              try
                Hashtbl.find keyword_table s
              with Not_found ->
                IDENT s }
  | ['0'-'9']+
    | '0' ['x' 'X'] ['0'-'9' 'A'-'F' 'a'-'f']+
    | '0' ['o' 'O'] ['0'-'7']+
    | '0' ['b' 'B'] ['0'-'1']+
            { INT (int_of_string(Lexing.lexeme lexbuf)) }
  | "(*"
            { comment lexbuf; token lexbuf }
  
  | "("     { LPAREN }
  | ")"     { RPAREN }
  | "."     { DOT }
  | ";"     { SEMICOLON }
  | ";;"    { SEMISEMI }
  | "->"    { ARROW }
  | "="     { EQUAL }
  | ","     { COMMA }
  | "'"     { QUOTE }
  | ":"     { COLON }
  | "*"     { STAR }
  | "+"     { PLUS }
  | "-"     { MINUS }
  | "/"     { SLASH }
  | "=="    { EQUALEQUAL }
  | "<>"    { LESSGREATER }
  | "<"     { LESS }
  | ">"     { GREATER }
  | "<="    { LESSEQUAL }
  | ">="    { GREATEREQUAL }
  | eof     { EOF }

  | _       { raise(Lexical_error "illegal character") }

and comment = parse
    "*)"
            { () }
  | "(*"
            { comment lexbuf; comment lexbuf }
  | eof
            { raise (Lexical_error "comment not terminated") }
  | _
            { comment lexbuf }

