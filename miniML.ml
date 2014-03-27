(*  A modular module system.
    The type-checker for mini-ML.

    Copyright 1999 Xavier Leroy.
    This file is distributed under the GNU Public Licence. *)

open Modules

(* Section 3.2: Mini-ML *)

module ML =
  struct
    type term =
        Constant of int                        (* integer constants *)
      | Longident of path                      (* id or mod.mod...id *)
      | Function of Ident.t * term             (* fun id -> expr *)
      | Apply of term * term                   (* expr(expr) *)
      | Let of Ident.t * term * term           (* let id = expr in expr *)
    type simple_type =
        Var of type_variable                   (* 'a, 'b *)
      | Typeconstr of path * simple_type list  (* constructed type *)
    and type_variable =
      { mutable repres: simple_type option;
                                        (* representative, for union-find *)
              mutable level: int }   (* binding level, for generalization *)
    type val_type =
      { quantif: type_variable list;           (* quantified variables *)
        body: simple_type }                    (* body of type scheme *)
    type def_type =
      { params: type_variable list;            (* list of parameters *)
        defbody: simple_type }                 (* body of type definition *)
    type kind = { arity: int }

    let rec subst_type subst = function
        Var {repres = None} as ty -> ty
      | Var {repres = Some ty} -> subst_type subst ty
      | Typeconstr(p, tl) ->
          Typeconstr(Subst.path p subst, List.map (subst_type subst) tl)
    let subst_valtype vty subst =
      { quantif = vty.quantif;
        body = subst_type subst vty.body }
    let subst_deftype def subst =
      { params = def.params;
        defbody = subst_type subst def.defbody }
    let subst_kind kind subst = kind
  end

module MLMod = Mod_syntax(ML)
module MLEnv = Env(MLMod)

(* The type-checker for mini-ML (Hindley-Milner type inference) *)

module MLTyping =
  struct
    module Core = ML
    module Env = MLEnv
    open ML

    let rec typerepr = function
        Var({repres = Some ty} as var) ->
          let r = typerepr ty in var.repres <- Some r; r
      | ty -> ty

    let current_level = ref 0
    let begin_def() = incr current_level
    let end_def() = decr current_level
    let newvar() = {repres = None; level = !current_level}
    let unknown() = Var(newvar())

    let rec subst_vars subst ty =
      match typerepr ty with
        Var var as tyvar ->
          begin try List.assq var subst with Not_found -> tyvar end
      | Typeconstr(p, tl) -> Typeconstr(p, List.map (subst_vars subst) tl)

    exception Cannot_expand
    let expand_manifest env path args =
      match Env.find_type path env with
        {MLMod.manifest = None} ->
          raise Cannot_expand
      | {MLMod.manifest = Some def} ->
          subst_vars (List.combine def.params args) def.defbody

    (* Expand abbreviations in ty1 and ty2 until their top constructor match *)
    let rec scrape_types env ty1 ty2 =
      let repr1 = typerepr ty1 and repr2 = typerepr ty2 in
      match (repr1, repr2) with
        (Typeconstr(path1, args1), Typeconstr(path2, args2)) ->
          if path_equal path1 path2 then
            (repr1, repr2)
          else begin
            try
              scrape_types env (expand_manifest env path1 args1) repr2
            with Cannot_expand ->
              try
                scrape_types env repr1 (expand_manifest env path2 args2)
              with Cannot_expand ->
                (repr1, repr2)
          end
      | (Typeconstr(path, args), _) ->
          begin try
            scrape_types env (expand_manifest env path args) repr2
          with Cannot_expand ->
            (repr1, repr2)
          end
      | (_, Typeconstr(path, args)) ->
          begin try
            scrape_types env repr1 (expand_manifest env path args)
          with Cannot_expand ->
            (repr1, repr2)
          end
      | (_, _) -> (repr1, repr2)

    let rec occur_check var ty =
      match typerepr ty with
        Var var' -> if var == var' then error "cycle in unification"
      | Typeconstr(p, tl) -> List.iter (occur_check var) tl

    let rec update_levels level_max ty =
      match typerepr ty with
        Var v -> if v.level > level_max then v.level <- level_max
      | Typeconstr(p, tl) -> List.iter (update_levels level_max) tl

    let rec unify env t1 t2 =
      match scrape_types env t1 t2 with
          (r1, r2) when r1 == r2 -> ()
        | (Var v, r2) ->
            occur_check v r2;
            update_levels v.level r2;
            v.repres <- Some r2
        | (r1, Var v) ->
            occur_check v r1;
            update_levels v.level r1;
            v.repres <- Some r1
        | (Typeconstr(path1, args1), Typeconstr(path2, args2))
          when path1 = path2 ->
            List.iter2 (unify env) args1 args2
        | (_, _) ->
            error "type constructor mismatch in unification"

    let generalize ty =
      let rec gen_vars vars ty =
        match typerepr ty with
          Var v ->
            if v.level > !current_level & not (List.memq v vars)
            then v :: vars
            else vars
        | Typeconstr(path, tl) ->
            List.fold_left gen_vars vars tl in
      { quantif = gen_vars [] ty; body = ty }

    let trivial_scheme ty =
      { quantif = []; body = ty }

    let instance vty =
      match vty.quantif with
        [] -> vty.body
      | vars -> subst_vars (List.map (fun v -> (v, unknown())) vars) vty.body

    let ident_arrow = Ident.create "->"
    let path_arrow = Pident ident_arrow
    let arrow_type t1 t2 = Typeconstr(path_arrow, [t1;t2])
    let ident_int = Ident.create "int"
    let path_int = Pident ident_int
    let int_type = Typeconstr(path_int, [])
    let ident_star = Ident.create "*"
    let path_star = Pident ident_star

    let rec infer_type env = function
      Constant n -> int_type
    | Longident path -> instance (Env.find_value path env)
    | Function(param, body) ->
        let type_param = unknown() in
        let type_body =
          infer_type (Env.add_value param (trivial_scheme type_param) env) 
                     body in
        arrow_type type_param type_body
    | Apply(funct, arg) ->
        let type_funct = infer_type env funct in
        let type_arg = infer_type env arg in
        let type_result = unknown() in
        unify env type_funct (arrow_type type_arg type_result);
        type_result
    | Let(ident, arg, body) ->
        begin_def();
        let type_arg = infer_type env arg in
        end_def();
        infer_type (Env.add_value ident (generalize type_arg) env) body

    let rec check_simple_type env params ty =
      match typerepr ty with
        Var v ->
          if not (List.memq v params) then error "free type variable"
      | Typeconstr(path, tl) ->
          let arity = (Env.find_type path env).MLMod.kind.arity in
          if List.length tl <> arity then error "arity error";
          List.iter (check_simple_type env params) tl

    let kind_deftype env def =
      check_simple_type env def.params def.defbody;
      {arity = List.length def.params}

    let check_valtype env vty =
      check_simple_type env vty.quantif vty.body

    let check_kind env kind = ()

    let type_term env term =
      begin_def();
      let ty = infer_type env term in
      end_def();
      generalize ty

    let valtype_match env vty1 vty2 =
      let rec filter ty1 ty2 =
        match scrape_types env ty1 ty2 with
          (Var v, ty2) ->
            if List.memq v vty2.quantif
            then false
            else (v.repres <- Some ty2; true)
        | (Typeconstr(path1, tl1), Typeconstr(path2, tl2)) ->
            path1 = path2 & List.for_all2 filter tl1 tl2
        | (_, _) -> false in
      filter (instance vty1) vty2.body

    let deftype_equiv env kind def1 def2 =
      let rec equiv ty1 ty2 =
        match scrape_types env ty1 ty2 with
          (Var v1, Var v2) -> v1 == v2
        | (Typeconstr(path1, args1), Typeconstr(path2, args2)) ->
            path1 = path2 & List.for_all2 equiv args1 args2
        | (_, _) -> false in
      let subst =
        List.map2 (fun v1 v2 -> (v2, Var v1)) def1.params def2.params in
      equiv def1.defbody (subst_vars subst def2.defbody)

    let kind_match env kind1 kind2 =
      kind1.arity = kind2.arity

    let deftype_of_path path kind =
      let rec make_params n =
        if n <= 0 then [] else newvar() :: make_params (n-1) in
      let params = make_params kind.arity in
      { params = params;
        defbody = Typeconstr(path, List.map (fun v -> Var v) params) }

    (* Elimination of dependencies on a given module identifier
       by repeated expansion of type paths rooted at that identifier.
       Those functions are used only with the relaxed typing rule
       for functor applications described in section 5.5 and implemented
       in the file modules.ml.extended *)

    let rec is_rooted_at id = function
        Pident id' -> Ident.equal id id'
      | Pdot(p, s) -> is_rooted_at id p

    let rec nondep_type env id ty =
      match typerepr ty with
        Var v as tvar -> tvar
      | Typeconstr(path, args) ->
          if is_rooted_at id path then begin
            try
              nondep_type env id (expand_manifest env path args)
            with Cannot_expand ->
              raise Not_found
          end else
            Typeconstr(path, List.map (nondep_type env id) args)

    let nondep_valtype env id vty =
      { quantif = vty.quantif; body = nondep_type env id vty.body }
    let nondep_deftype env id def =
      { params = def.params; defbody = nondep_type env id def.defbody }
    let nondep_kind env id kind =
      kind
  end

module MLModTyping = Mod_typing(MLMod)(MLEnv)(MLTyping)

(* Scoping pass for mini-ML *)

module MLScoping =
  struct
    module Core = ML
    open ML
    let rec scope_term sc = function
        Constant n -> Constant n
      | Longident path -> Longident(Scope.value_path path sc)
      | Function(id, body) ->
          Function(id, scope_term (Scope.enter_value id sc) body)
      | Apply(t1, t2) -> Apply(scope_term sc t1, scope_term sc t2)
      | Let(id, t1, t2) ->
          Let(id, scope_term sc t1, scope_term (Scope.enter_value id sc) t2)
    let rec scope_simple_type sc = function
        Var v -> Var v
      | Typeconstr(path, args) ->
          Typeconstr(Scope.type_path path sc,
                     List.map (scope_simple_type sc) args)
    let scope_valtype sc vty =
      { quantif = vty.quantif; body = scope_simple_type sc vty.body }
    let scope_deftype sc def =
      { params = def.params; defbody = scope_simple_type sc def.defbody }
    let scope_kind sc kind = kind
  end

module MLModScoping = ModScoping(MLMod)(MLScoping)

(* Printing inferred types *)

module MLPrint =
  struct
    open Format
    open ML
    open MLMod

    let variable_names = ref ([] : (type_variable * string) list)

    let reset_names () = variable_names := []

    let rec print_path = function
        Pident id ->
          print_string (Ident.name id)
      | Pdot(root, field) ->
          print_path root; print_string "."; print_string field

    let rec print_simple_type ty =
      match MLTyping.typerepr ty with
        Var v ->
          let name =
            try
              List.assq v !variable_names
            with Not_found ->
              let n = List.length !variable_names + 1 in
              let s = String.make 1 (Char.chr(97 + n)) in
              variable_names := (v, s) :: !variable_names;
              s in
          print_string "'"; print_string name
      | Typeconstr(path, [t1;t2]) when path = MLTyping.path_arrow ->
          print_simple_type t1; print_string " -> ";
          print_simple_type t2
      | Typeconstr(path, [t1;t2]) when path = MLTyping.path_star ->
          print_simple_type t1; print_string " * ";
          print_simple_type t2
      | Typeconstr(path, []) ->
          print_path path
      | Typeconstr(path, [t]) ->
          print_simple_type t; print_string " "; print_path path
      | Typeconstr(path, t1::tl) ->
          print_string "(";
          print_simple_type t1;
          List.iter (fun t -> print_string ", "; print_simple_type t) tl;
          print_string ") "; print_path path

    let print_valtype vty =
      reset_names(); print_simple_type vty.body

    let print_deftype id dty =
      reset_names();
      print_simple_type
        (Typeconstr(Pident id, List.map (fun v -> Var v) dty.params));
      print_string " ="; print_space();
      print_simple_type dty.defbody

    let print_typedecl id decl =
      match decl.manifest with
        None ->
          reset_names();
          print_simple_type
            ((MLTyping.deftype_of_path (Pident id) decl.kind).defbody)
      | Some dty ->
          print_deftype id dty

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
          open_hvbox 2;
          print_string "val "; print_string(Ident.name id);
          print_string ":"; print_space(); print_valtype vty;
          close_box()
      | Type_sig(id, decl) ->
          open_hvbox 2;
          print_string "type "; print_typedecl id decl;
          close_box()
      | Module_sig(id, mty) ->
          open_hvbox 2;
          print_string "module "; print_string(Ident.name id);
          print_string ":"; print_space(); print_modtype mty;
          close_box()
  end
