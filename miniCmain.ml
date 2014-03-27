(*  A modular module system.
    The stand-alone type-checker for mini-C.

    Copyright 1999 Xavier Leroy.
    This file is distributed under the GNU Public Licence. *)

open Modules
open MiniC
open CTyping

let init_scope = ref Scope.empty
let init_env = ref CEnv.empty

let main() =
  let lexbuf = Lexing.from_channel stdin in
  try
    let prog = MiniCparser.implementation MiniClexer.token lexbuf in
    let scoped_prog = CModScoping.scope_module !init_scope prog in
    let mty = CModTyping.type_module !init_env scoped_prog in
    CPrint.print_modtype mty;
    Format.print_newline();
    exit 0
  with
    Error s ->
      prerr_string "Error: "; prerr_string s; prerr_newline(); exit 2
  | Parsing.Parse_error ->
      prerr_string "Syntax error at char ";
      prerr_int (Lexing.lexeme_start lexbuf);
      prerr_newline();
      exit 2
  | MiniClexer.Lexical_error msg ->
      prerr_string "Lexical error: "; prerr_string msg;
      prerr_string ", around character ";
      prerr_int (Lexing.lexeme_start lexbuf);
      prerr_newline();
      exit 2

let _ = main()
