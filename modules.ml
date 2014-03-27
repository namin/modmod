(*  A modular module system.
    The type-checker for the language-independent module system.

    Copyright 1999 Xavier Leroy.
    This file is distributed under the GNU Public Licence. *)

exception Error of string
let error s = raise(Error s)

(* Section 2.1: Identifiers *)

module type IDENT =
  sig
    type t
    val create: string -> t
    val name: t -> string
    val equal: t -> t -> bool
    type 'a tbl
    val emptytbl: 'a tbl
    val add: t -> 'a -> 'a tbl -> 'a tbl
    val find: t -> 'a tbl -> 'a
  end

module Ident : IDENT =
  struct
    type t = {name: string; stamp: int}
    let currstamp = ref 0
    let create s =
      currstamp := !currstamp + 1; {name = s; stamp = !currstamp}
    let name id = id.name
    let equal id1 id2 = (id1.stamp = id2.stamp)
    type 'a tbl = (t * 'a) list
    let emptytbl = []
    let add id data tbl = (id, data) :: tbl
    let rec find id1 = function
        [] -> raise Not_found
      | (id2, data) :: rem ->
          if equal id1 id2 then data else find id1 rem
  end

(* Section 2.2: Access paths *)

type path =
    Pident of Ident.t             (* identifier *)
  | Pdot of path * string         (* access to a module component *)

let rec path_equal p1 p2 =
  match (p1, p2) with
    (Pident id1, Pident id2) -> Ident.equal id1 id2
  | (Pdot(r1, field1), Pdot(r2, field2)) ->
      path_equal r1 r2 && field1 = field2
  | (_, _) -> false

(* Section 2.3: Substitutions *)

module type SUBST =
  sig
    type t
    val identity: t
    val add: Ident.t -> path -> t -> t
    val path: path -> t -> path
  end

module Subst : SUBST =
  struct
    type t = path Ident.tbl
    let identity = Ident.emptytbl
    let add = Ident.add
    let rec path p sub =
      match p with
        Pident id -> (try Ident.find id sub with Not_found -> p)
      | Pdot(root, field) -> Pdot(path root sub, field)
  end

(* Section 2.4: Abstract syntax for the base language *)

module type CORE_SYNTAX =
  sig
    type term
    type val_type
    type def_type
    type kind
    val subst_valtype: val_type -> Subst.t -> val_type
    val subst_deftype: def_type -> Subst.t -> def_type
    val subst_kind: kind -> Subst.t -> kind
  end

(* Section 2.5: Abstract syntax for the module language *)

module type MOD_SYNTAX =
  sig
    module Core: CORE_SYNTAX           (* the core syntax we started with *)
    type type_decl =
      { kind: Core.kind;
        manifest: Core.def_type option }          (* abstract or manifest *)
    type mod_type =
        Signature of signature                    (* sig ... end *)
      | Functor_type of Ident.t * mod_type * mod_type
                                                  (* functor(X: mty) mty *)
    and signature = specification list
    and specification =
        Value_sig of Ident.t * Core.val_type      (* val x: ty *)
      | Type_sig of Ident.t * type_decl           (* type t :: k [= ty] *)
      | Module_sig of Ident.t * mod_type          (* module X: mty *)
    type mod_term =
        Longident of path                         (* X or X.Y.Z *)
      | Structure of structure                    (* struct ... end *)
      | Functor of Ident.t * mod_type * mod_term 
                                                  (* functor (X: mty) mod *)
      | Apply of mod_term * mod_term              (* mod1(mod2) *)
      | Constraint of mod_term * mod_type         (* (mod : mty) *)
    and structure = definition list
    and definition =
        Value_str of Ident.t * Core.term          (* let x = expr *)
      | Type_str of Ident.t * Core.kind * Core.def_type
                                                  (* type t :: k = ty *)
      | Module_str of Ident.t * mod_term          (* module X = mod *)
    val subst_typedecl: type_decl -> Subst.t -> type_decl
    val subst_modtype: mod_type -> Subst.t -> mod_type
  end

module Mod_syntax(Core_syntax: CORE_SYNTAX) =
  struct
    module Core = Core_syntax

    type type_decl =
      { kind: Core.kind;
        manifest: Core.def_type option }          (* abstract or manifest *)
    type mod_type =
        Signature of signature                    (* sig ... end *)
      | Functor_type of Ident.t * mod_type * mod_type
                                                  (* functor(X: mty) mty *)
    and signature = specification list
    and specification =
        Value_sig of Ident.t * Core.val_type      (* val x: ty *)
      | Type_sig of Ident.t * type_decl           (* type t :: k [= ty] *)
      | Module_sig of Ident.t * mod_type          (* module X: mty *)
    type mod_term =
        Longident of path                         (* X or X.Y.Z *)
      | Structure of structure                    (* struct ... end *)
      | Functor of Ident.t * mod_type * mod_term 
                                                  (* functor (X: mty) mod *)
      | Apply of mod_term * mod_term              (* mod1(mod2) *)
      | Constraint of mod_term * mod_type         (* (mod : mty) *)
    and structure = definition list
    and definition =
        Value_str of Ident.t * Core.term          (* let x = expr *)
      | Type_str of Ident.t * Core.kind * Core.def_type
                                                  (* type t :: k = ty *)
      | Module_str of Ident.t * mod_term          (* module X = mod *)

    let subst_typedecl decl sub =
      { kind = Core.subst_kind decl.kind sub;
        manifest = match decl.manifest with
                     None -> None
                   | Some dty -> Some(Core.subst_deftype dty sub) }
    let rec subst_modtype mty sub =
      match mty with
        Signature sg -> Signature(List.map (subst_sig_item sub) sg)
      | Functor_type(id, mty1, mty2) ->
          Functor_type(id, subst_modtype mty1 sub, subst_modtype mty2 sub)
    and subst_sig_item sub = function
        Value_sig(id, vty) -> Value_sig(id, Core.subst_valtype vty sub)
      | Type_sig(id, decl) -> Type_sig(id, subst_typedecl decl sub)
      | Module_sig(id, mty) -> Module_sig(id, subst_modtype mty sub)
  end

(* Section 2.6: The environment structure *)

module type ENV =
  sig
    module Mod: MOD_SYNTAX
    type t
    val empty: t
    val add_value: Ident.t -> Mod.Core.val_type -> t -> t
    val add_type: Ident.t -> Mod.type_decl -> t -> t    
    val add_module: Ident.t -> Mod.mod_type -> t -> t    
    val add_spec: Mod.specification -> t -> t
    val add_signature: Mod.signature -> t -> t
    val find_value: path -> t -> Mod.Core.val_type
    val find_type: path -> t -> Mod.type_decl
    val find_module: path -> t -> Mod.mod_type
  end

module Env(Mod_syntax: MOD_SYNTAX) =
  struct
    module Mod = Mod_syntax
    type binding =
        Value of Mod.Core.val_type
      | Type of Mod.type_decl
      | Module of Mod.mod_type
    type t = binding Ident.tbl
    let empty = Ident.emptytbl
    let add_value id vty env = Ident.add id (Value vty) env
    let add_type id decl env = Ident.add id (Type decl) env
    let add_module id mty env = Ident.add id (Module mty) env
    let add_spec item env =
      match item with
        Mod.Value_sig(id, vty) -> add_value id vty env
      | Mod.Type_sig(id, decl) -> add_type id decl env
      | Mod.Module_sig(id, mty) -> add_module id mty env
    let add_signature = List.fold_right add_spec
    let rec find path env =
      match path with
        Pident id ->
          Ident.find id env
      | Pdot(root, field) ->
          match find_module root env with
            Mod.Signature sg -> find_field root field Subst.identity sg
          | _ -> error "structure expected in dot access"
    and find_field p field subst = function
        [] -> error "no such field in structure"
      | Mod.Value_sig(id, vty) :: rem ->
          if Ident.name id = field
          then Value(Mod.Core.subst_valtype vty subst)
          else find_field p field subst rem
      | Mod.Type_sig(id, decl) :: rem ->
          if Ident.name id = field
          then Type(Mod.subst_typedecl decl subst)
          else find_field p field
                 (Subst.add id (Pdot(p, Ident.name id)) subst) rem
      | Mod.Module_sig(id, mty) :: rem ->
          if Ident.name id = field
          then Module(Mod.subst_modtype mty subst)
          else find_field p field
                 (Subst.add id (Pdot(p, Ident.name id)) subst) rem
    and find_value path env =
      match find path env with
        Value vty -> vty | _ -> error "value field expected"   
    and find_type path env =
      match find path env with
        Type decl -> decl | _ -> error "type field expected"   
    and find_module path env =
      match find path env with
        Module mty -> mty | _ -> error "module field expected"   
  end

(* Section 2.7: Type-checking the base language *)

module type CORE_TYPING =
  sig
    module Core: CORE_SYNTAX
    module Env: ENV with module Mod.Core = Core
(* Typing functions *)
    val type_term: Env.t -> Core.term -> Core.val_type
    val kind_deftype: Env.t -> Core.def_type -> Core.kind
    val check_valtype: Env.t -> Core.val_type -> unit
    val check_kind: Env.t -> Core.kind -> unit
(* Type matching functions *)
    val valtype_match: Env.t -> Core.val_type -> Core.val_type -> bool
    val deftype_equiv:
          Env.t -> Core.kind -> Core.def_type -> Core.def_type -> bool
    val kind_match: Env.t -> Core.kind -> Core.kind -> bool
    val deftype_of_path: path -> Core.kind -> Core.def_type
  end

(* Section 2.8: Type-checking the module language *)

module type MOD_TYPING =
  sig
    module Mod: MOD_SYNTAX
    module Env: ENV with module Mod = Mod
    val type_module: Env.t -> Mod.mod_term -> Mod.mod_type
    val type_definition: Env.t -> Mod.definition -> Mod.specification
  end

module Mod_typing
    (TheMod: MOD_SYNTAX)
    (TheEnv: ENV with module Mod = TheMod)
    (CT: CORE_TYPING with module Core = TheMod.Core and module Env = TheEnv)
= struct
    module Mod = TheMod
    module Env = TheEnv
    open Mod                          (* Allows to omit the `Mod.' prefix *)

    (* Section 2.9: Matching between module types *)

    let rec modtype_match env mty1 mty2 =
      match (mty1, mty2) with
        (Signature sig1, Signature sig2) ->
          let (paired_components, subst) =
            pair_signature_components sig1 sig2 in
          let ext_env = Env.add_signature sig1 env in
          List.iter (specification_match ext_env subst) paired_components
      | (Functor_type(param1,arg1,res1), Functor_type(param2,arg2,res2)) ->
          let subst = Subst.add param1 (Pident param2) Subst.identity in
          let res1' = Mod.subst_modtype res1 subst in
          modtype_match env arg2 arg1;
          modtype_match (Env.add_module param2 arg2 env) res1' res2
      | (_, _) ->
          error "module type mismatch"
    and pair_signature_components sig1 sig2 =
      match sig2 with
        [] -> ([], Subst.identity)
      | item2 :: rem2 ->
          let rec find_matching_component = function
              [] -> error "unmatched signature component"
            | item1 :: rem1 ->
                match (item1, item2) with
                  (Value_sig(id1, _), Value_sig(id2, _))
                  when Ident.name id1 = Ident.name id2 ->
                    (id1, id2, item1)
                | (Type_sig(id1, _), Type_sig(id2, _))
                  when Ident.name id1 = Ident.name id2 ->
                    (id1, id2, item1)
                | (Module_sig(id1, _), Module_sig(id2, _))
                  when Ident.name id1 = Ident.name id2 ->
                    (id1, id2, item1)
                | _ -> find_matching_component rem1 in
          let (id1, id2, item1) = find_matching_component sig1 in
          let (pairs, subst) = pair_signature_components sig1 rem2 in
          ((item1, item2) :: pairs, Subst.add id2 (Pident id1) subst)
    and specification_match env subst = function
        (Value_sig(_, vty1), Value_sig(_, vty2)) ->
          if not (CT.valtype_match env vty1 (Core.subst_valtype vty2 subst))
          then error "value components do not match"
      | (Type_sig(id, decl1), Type_sig(_, decl2)) ->
          if not (typedecl_match env id decl1
                                 (Mod.subst_typedecl decl2 subst))
          then error "type components do not match"
      | (Module_sig(_, mty1), Module_sig(_, mty2)) ->
          modtype_match env mty1 (Mod.subst_modtype mty2 subst)
    and typedecl_match env id decl1 decl2 =
      CT.kind_match env decl1.kind decl2.kind &&
      (match (decl1.manifest, decl2.manifest) with
        (_, None) -> true
      | (Some typ1, Some typ2) ->
         CT.deftype_equiv env decl2.kind typ1 typ2
      | (None, Some typ2) ->
          CT.deftype_equiv env decl2.kind
                           (CT.deftype_of_path (Pident id) decl1.kind) typ2)

    (* Section 2.10: Strengthening of module types *)

    let rec strengthen_modtype path mty =
      match mty with
        Signature sg -> Signature(List.map (strengthen_spec path) sg)
      | Functor_type(_, _, _) -> mty
    and strengthen_spec path item =
      match item with
        Value_sig(id, vty) -> item
      | Type_sig(id, decl) ->
          let m = match decl.manifest with
              None -> Some(CT.deftype_of_path
                                 (Pdot(path, Ident.name id)) decl.kind)
            | Some ty -> Some ty in
          Type_sig(id, {kind = decl.kind; manifest = m})
      | Module_sig(id, mty) ->
          Module_sig(id, strengthen_modtype (Pdot(path, Ident.name id)) mty)

    (* Continuation of section 2.8: Type-checking the module language *)

    let rec check_modtype env = function
        Signature sg -> check_signature env [] sg
      | Functor_type(param, arg, res) ->
          check_modtype env arg;
          check_modtype (Env.add_module param arg env) res
    and check_signature env seen = function
        [] -> ()
      | Value_sig(id, vty) :: rem ->
          if List.mem (Ident.name id) seen
          then error "repeated value name";
          CT.check_valtype env vty;
          check_signature env (Ident.name id :: seen) rem
      | Type_sig(id, decl) :: rem ->
          if List.mem (Ident.name id) seen
          then error "repeated type name";
          CT.check_kind env decl.kind;
          begin match decl.manifest with
              None -> () 
            | Some typ ->
                if not (CT.kind_match env (CT.kind_deftype env typ)
                                          decl.kind)
                then error "kind mismatch in manifest type specification"
          end;
          check_signature (Env.add_type id decl env)
                          (Ident.name id :: seen) rem
      | Module_sig(id, mty) :: rem ->
          if List.mem (Ident.name id) seen 
          then error "repeated module name";
          check_modtype env mty;
          check_signature (Env.add_module id mty env) 
                          (Ident.name id :: seen) rem

    let rec type_module env = function
        Longident path ->
          strengthen_modtype path (Env.find_module path env)
      | Structure str ->
          Signature(type_structure env [] str)
      | Functor(param, mty, body) ->
          check_modtype env mty;
          Functor_type(param, mty,
              type_module (Env.add_module param mty env) body)
      | Apply(funct, (Longident path as arg)) ->
          (match type_module env funct with
            Functor_type(param, mty_param, mty_res) ->
              let mty_arg = type_module env arg in
              modtype_match env mty_arg mty_param;
              subst_modtype mty_res (Subst.add param path Subst.identity)
          | _ -> error "application of a non-functor")
      | Apply(funct, arg) ->
          error "application of a functor to a non-path"
      | Constraint(modl, mty) ->
          check_modtype env mty;
          modtype_match env (type_module env modl) mty;
          mty
    and type_structure env seen = function
        [] -> []
      | stritem :: rem ->
          let (sigitem, seen') = type_definition env seen stritem in
          sigitem :: type_structure (Env.add_spec sigitem env) seen' rem
    and type_definition env seen = function
        Value_str(id, term) ->
          if List.mem (Ident.name id) seen
          then error "repeated value name";
          (Value_sig(id, CT.type_term env term), Ident.name id :: seen)
      | Module_str(id, modl) ->
          if List.mem (Ident.name id) seen
          then error "repeated module name";
          (Module_sig(id, type_module env modl), Ident.name id :: seen)
      | Type_str(id, kind, typ) ->
          if List.mem (Ident.name id) seen
          then error "repeated type name";
          CT.check_kind env kind;
          if not (CT.kind_match env (CT.kind_deftype env typ) kind)
          then error "kind mismatch in type definition";
          (Type_sig(id, {kind = kind; manifest = Some typ}),
           Ident.name id :: seen)
  end

(* Generic ``scoping'' pass for the module language.
   This pass is not described in the article
   Scoping is the act of associating identifiers with their binding location.
   Here we assume that the parser generates fresh identifiers 
   (values of type Ident.t) each time it encounters an occurrence of a
   lexical identifier in the program, and stores those fresh identifiers
   in the abstract syntax tree it constructs.
   The scoping pass rewrites the abstract syntax tree to use identical
   identifiers at a binding site and at all its usage sites. *)

(* A scoping structure is a table recording (name, identifier) associations
   for value names, type names and module names. *)

module type SCOPE =
  sig
    type t
    val empty: t
    val enter_value: Ident.t -> t -> t
    val enter_type: Ident.t -> t -> t
    val enter_module: Ident.t -> t -> t
    val value_path: path -> t -> path
    val type_path: path -> t -> path
    val module_path: path -> t -> path
  end

module Scope : SCOPE =
  struct
    type t =
      { values: (string * Ident.t) list;
        types: (string * Ident.t) list;
        modules: (string * Ident.t) list }
    let empty = { values = []; types = []; modules = [] }
    let enter_value id sc =
      { values = (Ident.name id, id) :: sc.values;
        types = sc.types; modules = sc.modules }
    let enter_type id sc =
      { types = (Ident.name id, id) :: sc.types;
        values = sc.values; modules = sc.modules }
    let enter_module id sc =
      { modules = (Ident.name id, id) :: sc.modules;
        values = sc.values; types = sc.types }
    let scope_value id sc =
      try List.assoc (Ident.name id) sc.values
      with Not_found -> error("unbound value " ^ Ident.name id)
    let scope_type id sc =
      try List.assoc (Ident.name id) sc.types
      with Not_found -> error("unbound type " ^ Ident.name id)
    let scope_module id sc =
      try List.assoc (Ident.name id) sc.modules
      with Not_found -> error("unbound module " ^ Ident.name id)
    let rec scope_path scope_ident path sc =
      match path with
        Pident id -> Pident(scope_ident id sc)
      | Pdot(root, field) -> Pdot(scope_path scope_module root sc, field)
    let value_path = scope_path scope_value
    let type_path = scope_path scope_type
    let module_path = scope_path scope_module
  end

(* The scoping pass for the core language must conform to the following
   signature. *)

module type CORE_SCOPING =
  sig
    module Core: CORE_SYNTAX
    val scope_term: Scope.t -> Core.term -> Core.term
    val scope_valtype: Scope.t -> Core.val_type -> Core.val_type
    val scope_deftype: Scope.t -> Core.def_type -> Core.def_type
    val scope_kind: Scope.t -> Core.kind -> Core.kind
  end

(* The scoping pass for the module language is then as follows. *)

module ModScoping
    (Mod: MOD_SYNTAX)
    (CS: CORE_SCOPING with module Core = Mod.Core) =
  struct
    module Mod = Mod
    open Mod
    let scope_typedecl sc decl =
      { kind = CS.scope_kind sc decl.kind;
        manifest = match decl.manifest with
                     None -> None
                   | Some ty -> Some(CS.scope_deftype sc ty) }
    let rec scope_modtype sc = function
        Signature sg -> Signature(scope_signature sc sg)
      | Functor_type(id, arg, res) ->
          Functor_type(id, scope_modtype sc arg,
                       scope_modtype (Scope.enter_module id sc) res)
    and scope_signature sc = function
        [] -> []
      | Value_sig(id, vty) :: rem ->
          Value_sig(id, CS.scope_valtype sc vty) ::
          scope_signature (Scope.enter_value id sc) rem
      | Type_sig(id, decl) :: rem ->
          Type_sig(id, scope_typedecl sc decl) ::
          scope_signature (Scope.enter_type id sc) rem
      | Module_sig(id, mty) :: rem ->
          Module_sig(id, scope_modtype sc mty) ::
          scope_signature (Scope.enter_module id sc) rem
    let rec scope_module sc = function
        Longident path -> Longident(Scope.module_path path sc)
      | Structure str -> Structure(scope_structure sc str)
      | Functor(id, arg, body) ->
          Functor(id, scope_modtype sc arg,
                  scope_module (Scope.enter_module id sc) body)
      | Apply(m1, m2) -> Apply(scope_module sc m1, scope_module sc m2)
      | Constraint(m, mty) ->
          Constraint(scope_module sc m, scope_modtype sc mty)
    and scope_structure sc = function
        [] -> []
      | Value_str(id, v) :: rem ->
          Value_str(id, CS.scope_term sc v) ::
          scope_structure (Scope.enter_value id sc) rem
      | Type_str(id, kind, dty) :: rem ->
          Type_str(id, CS.scope_kind sc kind, CS.scope_deftype sc dty) ::
          scope_structure (Scope.enter_type id sc) rem
      | Module_str(id, m) :: rem ->
          Module_str(id, scope_module sc m) ::
          scope_structure (Scope.enter_module id sc) rem
  end
