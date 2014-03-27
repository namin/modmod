(*  A modular module system.
    The type-checker for core-C.

    Copyright 1999 Xavier Leroy.
    This file is distributed under the GNU Public Licence. *)

open Modules

(* Section 3.1: Core C *)

module C =
  struct
    type ctype =
        Void | Int | Float | Pointer of ctype
      | Function of ctype list * ctype
      | Typename of path
    type expr =
        Intconst of int                   (* integer constants *)
      | Floatconst of float               (* float constants *)
      | Variable of path                  (* var or mod.mod...var *)
      | Apply of expr * expr list         (* function call *)
      | Assign of expr * expr             (* var = expr *)
      | Unary_op of string * expr         (* *expr, !expr, etc *)
      | Binary_op of string * expr * expr (* expr + expr, etc *)
      | Cast of expr * ctype              (* (type)expr *)
    type statement =
        Expr of expr                      (* expr; *)
      | If of expr * statement * statement(* if (cond) stmt; else stmt; *)
      | For of expr * expr * expr * statement
                                          (* for (init; cond; step) stmt; *)
      | Return of expr                    (* return expr; *)
      | Block of (Ident.t * ctype) list * statement list
                                          (* { decls; stmts; } *)
    type term =
        Var_decl of ctype
      | Fun_def of (Ident.t * ctype) list * ctype * statement
    type val_type = ctype
    type def_type = ctype
    type kind = unit

    let rec subst_type subst = function
        Typename path -> Typename(Subst.path path subst)
      | Pointer ty -> Pointer(subst_type subst ty)
      | Function(args, res) ->
          Function(List.map (subst_type subst) args, subst_type subst res)
      | ty -> ty
    let subst_valtype vty subst = subst_type subst vty
    let subst_deftype dty subst = subst_type subst dty
    let subst_kind kind subst = kind
  end

module CMod = Mod_syntax(C)
module CEnv = Env(CMod)

module CTyping =
  struct
    module Core = C
    module Env = CEnv
    open CMod
    open C
    let rec check_valtype env = function
        Typename path -> ignore(CEnv.find_type path env)
      | Pointer ty -> check_valtype env ty
      | Function(args, res) ->
          List.iter (check_valtype env) args; check_valtype env res
      | _ -> ()
    let kind_deftype = check_valtype
    let check_kind env k = ()
    let deftype_of_path path kind = Typename path

    let rec valtype_match env ty1 ty2 =
      match (ty1, ty2) with
        (Void, Void) -> true
      | (Int, Int) -> true
      | (Float, Float) -> true
      | (Function(args1, res1), Function(args2, res2)) ->
          List.length args1 = List.length args2 &&
          List.for_all2 (valtype_match env) args1 args2 &&
          valtype_match env res1 res2
      | (Typename path1, Typename path2) ->
          path_equal path1 path2 ||
          begin match (CEnv.find_type path1 env,
                       CEnv.find_type path2 env) with
            ({manifest = Some def}, _) -> valtype_match env def ty2
          | (_, {manifest = Some def}) -> valtype_match env ty1 def
          | ({manifest = None}, {manifest = None}) -> false
          end
      | (Typename path1, _) ->
          begin match CEnv.find_type path1 env with
            {manifest = Some def} -> valtype_match env def ty2
          | {manifest = None} -> false
          end
      | (_, Typename path2) ->
          begin match CEnv.find_type path2 env with
            {manifest = Some def} -> valtype_match env ty1 def
          | {manifest = None} -> false
          end
      | (_, _) -> false
    let deftype_equiv env kind t1 t2 = valtype_match env t1 t2
    let kind_match env k1 k2 = true

    let rec scrape env = function
        Typename path ->
          begin match CEnv.find_type path env with
            {CMod.manifest = Some ty} -> scrape env ty
          | {CMod.manifest = None} -> Typename path
          end
      | ty -> ty

    let rec type_expr env = function
        Intconst n -> Int
      | Floatconst n -> Float
      | Variable path -> CEnv.find_value path env
      | Apply(funct, args) ->
          begin match type_expr env funct with
            Function(ty_args, ty_res) ->
              if List.length args <> List.length ty_args then
                error "wrong number of arguments";
              List.iter2 (check_type_expr env) args ty_args;
              ty_res
          | _ -> error "application of a non-function"
          end
      | Assign(arg1, arg2) ->
          begin match arg1 with
            Variable path -> ()
          | Unary_op("*", arg) -> ()
          | _ -> error "not a l-value"
          end;
          let ty = type_expr env arg1 in
          check_type_expr env arg2 ty;
          ty
      | Unary_op(op, arg) ->
          begin match (op, scrape env (type_expr env arg)) with
            ("*", Pointer ty) -> ty
          | ("-", Int) -> Int
          | ("-", Float) -> Float
          | ("!", Int) -> Int
          | (_, _) -> error "type mismatch"
          end
      | Binary_op(op, arg1, arg2) ->
          let ty1 = scrape env (type_expr env arg1) in
          let ty2 = scrape env (type_expr env arg2) in
          begin match op with
            "+" | "-" ->
              begin match (ty1, ty2) with
                (Pointer ty, Int) -> Pointer ty
              | (Int, Int) -> Int
              | ((Int|Float), (Int|Float)) -> Float
              | _ -> error "type mismatch"
              end
          | "*" | "/" ->
              begin match (ty1, ty2) with
                (Int, Int) -> Int
              | ((Int|Float), (Int|Float)) -> Float
              | _ -> error "type mismatch"
              end
          | "==" | "!=" | "<" | "<=" | ">" | ">=" ->
              begin match (ty1, ty2) with
                (Pointer ty1, Pointer ty2) when valtype_match env ty1 ty2 -> Int
              | ((Int|Float), (Int|Float)) -> Int
              | _ -> error "type mismatch"
              end
          end
      | Cast(expr, ty) ->
          ignore(type_expr env expr);
          check_valtype env ty;
          ty

    and check_type_expr env expr expected_type =
      let expr_type = type_expr env expr in
      match (scrape env expected_type, scrape env expr_type) with
      (* Allow implicit coercions between int and float *)
        (Int, Float) -> ()
      | (Float, Int) -> ()
      (* Allow implicit coercions between void * and other pointer types *)
      | (Pointer Void, Pointer ty) -> ()
      | (Pointer ty, Pointer Void) -> ()
      (* Otherwise, types must be equal *)
      | (ty1, ty2) -> if ty1 <> ty2 then error "type mismatch"

    let rec check_statement env ty_ret = function
        Expr e -> ignore(type_expr env e)
      | If(cond, ifso, ifnot) ->
          check_type_expr env cond Int;
          check_statement env ty_ret ifso;
          check_statement env ty_ret ifnot
      | For(init, test, incr, body) ->
          ignore(type_expr env init);
          check_type_expr env test Int;
          ignore(type_expr env incr);
          check_statement env ty_ret body
      | Return e ->
          check_type_expr env e ty_ret
      | Block(decls, stmts) ->
          let newenv = add_variables env decls in
          List.iter (check_statement newenv ty_ret) stmts

    and add_variables env decls =
      List.fold_left
        (fun env (id, ty) ->
          check_valtype env ty; CEnv.add_value id ty env)
        env decls

    let type_term env = function
        Var_decl ty ->
          check_valtype env ty; ty
      | Fun_def(params, ty_res, body) ->
          check_valtype env ty_res;
          check_statement (add_variables env params) ty_res body;
          Function(List.map snd params, ty_res)

    (* Elimination of dependencies on a given module identifier
       by repeated expansion of type paths rooted at that identifier.
       Those functions are used only with the relaxed typing rule
       for functor applications described in section 5.5 and implemented
       in the file modules.ml.extended *)

    let rec is_rooted_at id = function
        Pident id' -> Ident.equal id id'
      | Pdot(p, s) -> is_rooted_at id p

    let rec nondep_valtype env id = function
        Typename path ->
          if is_rooted_at id path then begin
            match CEnv.find_type path env with
              {manifest = None} -> raise Not_found (* cannot remove dependency *)
            | {manifest = Some ty} -> nondep_valtype env id ty
          end else
            Typename path
      | Pointer ty -> Pointer(nondep_valtype env id ty)        
      | Function(args, res) ->
          Function (List.map (nondep_valtype env id) args, nondep_valtype env id
 res)
      | ty -> ty

    let nondep_deftype = nondep_valtype
    let nondep_kind env id kind = ()

  end    

module CModTyping = Mod_typing(CMod)(CEnv)(CTyping)

(* Scoping pass for Core C *)

module CScoping =
  struct
    module Core = C
    open C
    let rec scope_valtype sc = function
        Typename path -> Typename(Scope.type_path path sc)
      | Pointer ty -> Pointer(scope_valtype sc ty)
      | Function(args, res) ->
          Function(List.map (scope_valtype sc) args, scope_valtype sc res)
      | ty -> ty
    let scope_deftype = scope_valtype
    let scope_kind sc kind = kind
    let rec scope_expr sc = function
        Intconst i -> Intconst i
      | Floatconst f -> Floatconst f
      | Variable p -> Variable(Scope.value_path p sc)
      | Apply(e1, el) -> Apply(scope_expr sc e1, List.map(scope_expr sc) el)
      | Assign(e1, e2) -> Assign(scope_expr sc e1, scope_expr sc e2)
      | Unary_op(op, e) -> Unary_op(op, scope_expr sc e)
      | Binary_op(op, e1, e2) ->
          Binary_op(op, scope_expr sc e1, scope_expr sc e2)
      | Cast(e, ty) -> Cast(scope_expr sc e, scope_valtype sc ty)
    let rec scope_statement sc = function
        Expr e -> Expr(scope_expr sc e)
      | If(cond, ifso, ifnot) ->
          If(scope_expr sc cond,
             scope_statement sc ifso, scope_statement sc ifnot)
      | For(init, cond, incr, body) ->
          For(scope_expr sc init, scope_expr sc cond, scope_expr sc incr,
              scope_statement sc body)
      | Return e -> Return(scope_expr sc e)
      | Block(decls, stmts) ->
          let (newsc, newdecls) = scope_decls sc decls in
          Block(newdecls, List.map (scope_statement newsc) stmts)
    and scope_decls sc = function
        [] -> (sc, [])
      | (id, ty) :: rem ->
          let sc' = Scope.enter_value id sc in
          let (newsc, newrem) = scope_decls sc' rem in
          (newsc, (id, scope_valtype sc ty) :: newrem)
    let scope_term sc = function
        Var_decl ty -> Var_decl(scope_valtype sc ty)
      | Fun_def(params, ty_res, body) ->
          let (newsc, newdecls) = scope_decls sc params in
          Fun_def(newdecls, scope_valtype sc ty_res,
                  scope_statement newsc body)
  end

module CModScoping = ModScoping(CMod)(CScoping)

(* Printing inferred types *)

module CPrint =
  struct
    open Format
    open C
    open CMod

    let rec print_path = function
        Pident id ->
          print_string (Ident.name id)
      | Pdot(root, field) ->
          print_path root; print_string "."; print_string field

    let rec print_type = function
        Void -> print_string "void"
      | Int -> print_string "int"
      | Float -> print_string "float"
      | Pointer p -> print_type p; print_string " *"
      | Function(args, res) ->
          print_string "("; print_type res; print_string " (";
          print_type_list args; print_string "))"
      | Typename path -> print_path path

    and print_type_list = function
        [] -> ()
      | ty1 :: tyl ->
          print_type ty1;
          List.iter(fun ty -> print_string ", "; print_type ty) tyl

    let print_name_type id = function
       Function(args, res) ->
          print_type res; print_string " "; print_string(Ident.name id);
          print_string "("; print_type_list args; print_string ")"
      | ty ->
          print_type ty; print_string " "; print_string(Ident.name id)  

    let rec print_modtype = function
        Signature sg ->
          open_hvbox 2;
          print_string "sig";
          List.iter
            (fun item -> print_space(); print_signature_item item) sg;
          print_break 1 (-2);
          print_string "end";
          close_box()
      | Functor_type(param, arg, body) ->
          open_hvbox 2;
          print_string "functor("; print_string(Ident.name param);
          print_string ": "; print_modtype arg; print_string ")";
          print_space(); print_modtype body;
          close_box()
    and print_signature_item = function
        Value_sig(id, vty) ->
          print_name_type id vty
      | Type_sig(id, {manifest = Some ty}) ->
          print_string "typedef "; print_name_type id ty
      | Type_sig(id, {manifest = None}) ->
          print_string "typedef "; print_string(Ident.name id)
      | Module_sig(id, mty) ->
          open_hvbox 2;
          print_string "module "; print_string(Ident.name id);
          print_string ":"; print_space(); print_modtype mty;
          close_box()
  end
    
