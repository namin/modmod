(*  A modular module system.
    The stand-alone type-checker for mini-ML.

    Copyright 1999 Xavier Leroy.
    This file is distributed under the GNU Public Licence. *)

open Modules
open MiniML
open MLTyping

let init_scope = ref Scope.empty
let init_env = ref MLEnv.empty

let enter_type id decl =
  init_scope := Scope.enter_type id !init_scope;
  init_env := MLEnv.add_type id decl !init_env

let enter_val name ty =
  let id = Ident.create name in
  init_scope := Scope.enter_value id !init_scope;
  init_env := MLEnv.add_value id ty !init_env

let _ =
  let ident_bool = Ident.create "bool" in
  let path_bool = Pident ident_bool in
  let bool_type = ML.Typeconstr(path_bool, []) in
  enter_type ident_arrow {MLMod.kind = {ML.arity = 2}; MLMod.manifest = None};
  enter_type ident_star {MLMod.kind = {ML.arity = 2}; MLMod.manifest = None};
  enter_type ident_int {MLMod.kind = {ML.arity = 0}; MLMod.manifest = None};
  enter_type ident_bool {MLMod.kind = {ML.arity = 0}; MLMod.manifest = None};
  enter_val "false" { ML.quantif = []; ML.body = bool_type };
  enter_val "true" { ML.quantif = []; ML.body = bool_type };
  List.iter
    (fun name ->
        enter_val name
          { ML.quantif = [];
            ML.body = arrow_type int_type (arrow_type int_type bool_type)})
    ["+"; "-"; "*"; "/"; "=="; "<>"; "<"; "<="; ">"; ">="];
  let alpha = newvar() and beta = newvar() in
  let talpha = ML.Var alpha and tbeta = ML.Var beta in
  enter_val ","
    { ML.quantif = [alpha;beta];
      ML.body = arrow_type talpha (arrow_type tbeta
                  (ML.Typeconstr(path_star, [talpha; tbeta]))) };
  enter_val "fst"
    { ML.quantif = [alpha;beta];
      ML.body = arrow_type
                  (ML.Typeconstr(path_star, [talpha; tbeta])) talpha };
  enter_val "snd"
    { ML.quantif = [alpha;beta];
      ML.body = arrow_type
                  (ML.Typeconstr(path_star, [talpha; tbeta])) tbeta };
  enter_val "conditional"
    { ML.quantif = [alpha];
      ML.body = arrow_type bool_type
                          (arrow_type talpha (arrow_type talpha talpha)) }

let main() =
  let lexbuf = Lexing.from_channel stdin in
  try
    let prog = MiniMLparser.implementation MiniMLlexer.token lexbuf in
    let scoped_prog = MLModScoping.scope_module !init_scope prog in
    let mty = MLModTyping.type_module !init_env scoped_prog in
    MLPrint.print_modtype mty;
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
  | MiniMLlexer.Lexical_error msg ->
      prerr_string "Lexical error: "; prerr_string msg;
      prerr_string ", around character ";
      prerr_int (Lexing.lexeme_start lexbuf);
      prerr_newline();
      exit 2

let _ = main()
