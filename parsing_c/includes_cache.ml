(*
 * This file is part of Coccinelle, licensed under the terms of the GPL v2.
 * See copyright.txt in the Coccinelle source code for more information.
 * The Coccinelle source code can be obtained at http://coccinelle.lip6.fr
 *)

(* TODO: Better name for this module? *)

(* This module is kind of in a confusing place. It needs functions from
 * Parse_c and Type_annoter_c, but both of those modules depend on this
 * module. Thus I've had to pull a few messy stunts like in
 * get_type_from_name_cache. Maybe be more functional and resolve this
 * wretched circular dependency somehow. *)

open Common

(*****************************************************************************)
(* Wrappers *)
(*****************************************************************************)
let pr_inc s =
  if !Flag_parsing_c.verbose_includes
  then Common.pr2 s

(*****************************************************************************)
(* Graph types/modules *)
(*****************************************************************************)

(* We really just need the filenames as keys to check paths from file A
 * to file B. Might be subject to change later? *)
module Key : Set.OrderedType with type t = filename = struct
  type t = filename
  let compare = String.compare
end

module KeySet = Set.Make (Key)

module KeyMap = Map.Make (Key)

(* TODO: verify *)
module Node : Set.OrderedType with type t = unit = struct
  type t = unit
  let compare = compare
end

(* TODO: verify *)
module Edge : Set.OrderedType with type t = unit = struct
  type t = unit
  let compare = compare
end

module KeyEdgePair : Set.OrderedType with type t = Key.t * Edge.t =
struct
  type t = Key.t * Edge.t
  let compare = compare
end

module KeyEdgeSet = Set.Make (KeyEdgePair)

module G = Ograph_simple.Make
  (Key) (KeySet) (KeyMap) (Node) (Edge) (KeyEdgePair) (KeyEdgeSet)


(*****************************************************************************)
(* Includes dependency graph *)
(*****************************************************************************)

(* Header file includes dependency graph *)
let dependency_graph = ref (new G.ograph_mutable)

(* We really just need to check if a path exists between one node to another,
 * so the below works fine.
 * Ripped from dfs_iter in commons/ograph_extended.ml with minor changes.
 * Return true if g satisfies predicate f else false
 *)
let dfs_exists xi f g =
  let already = Hashtbl.create 101 in
  let rec aux_dfs xs =
    let h xi =
      if Hashtbl.mem already xi
      then false
      else begin
        Hashtbl.add already xi true;
        if f xi
        then true
        else begin
          let f' (key, _) keyset = KeySet.add key keyset in
          let newset =
            try KeyEdgeSet.fold f' (g#successors xi) KeySet.empty
            with Not_found -> KeySet.empty in
          aux_dfs newset
        end
      end in
    KeySet.exists h xs in
  aux_dfs (KeySet.singleton xi)

let add_to_dependency_graph parent file =
  let add_node a =
    if not (KeyMap.mem a !dependency_graph#nodes)
    then !dependency_graph#add_node a () in
  let add_arc (a, b) =
    add_node a;
    add_node b;
    !dependency_graph#add_arc (a, b) () in
  add_arc (parent, file)

let path_exists_dependency_graph filea fileb =
  dfs_exists filea (fun a -> a = fileb) !dependency_graph

let print_dependency_graph _ =
  G.print_ograph_generic
    ~str_of_key:(fun k -> "\"" ^ k ^ "\"")
    ~str_of_node:(fun k _ -> k)
    "/tmp/headers.dot"
    !dependency_graph


(*****************************************************************************)
(* Name cache *)
(*****************************************************************************)

(* Map construct name to list of files it is defined in *)
let name_cache : (string, filename list) Hashtbl.t ref =
  ref (Hashtbl.create 101)

(* If a file's AST has been used recently, it will probably be used again by
 * the type annoter. A better solution would be to use a LRU cache of size 5 or
 * so, but we all know how that turned out before. *)
let cur_file = ref None
let cur_files = ref None

let add_to_name_cache name file =
  let l =
    try Hashtbl.find !name_cache name
    with Not_found -> [] in
  Hashtbl.replace !name_cache name (l @ [file])

(* Two visitors, One to cache names and the other to get the type associated to
 * a name. *)
let cache_name_visitor file =
  let cache_struct_fields def =
    let _cache_field field =
      match (Ast_c.unwrap field) with
        Ast_c.Simple (name, _)
      | Ast_c.BitField (name, _, _, _) ->
          name +>
            do_option
              (fun n ->
                 add_to_name_cache (Ast_c.str_of_name n) file) in
    let _cache_struct_fields field =
      match field with
        Ast_c.DeclarationField(Ast_c.FieldDeclList(l)) ->
          List.iter _cache_field (Ast_c.unwrap l)
      | _ -> () in
    List.iter _cache_struct_fields def in
  let cache_enum_constants def =
    def +>
      List.iter
        (fun ec ->
           add_to_name_cache
             ((Ast_c.unwrap ec) +> fst +> Ast_c.str_of_name) file) in
  { Visitor_c.default_visitor_c with
    Visitor_c.ktoplevel = fun (k, bigf) p ->
      match p with
        Ast_c.Declaration
          (Ast_c.DeclList
            ([{Ast_c.v_namei = Some (name, _);
              Ast_c.v_type = typ}, _], _)) ->
                (* Storing whatever to the name cache. These are global and
                 * have a name, so they're all useful.
                 * TODO: Might be subject to change when we want to add the
                 * type of the construct to the name cache as well, as done in
                 * type_annoter_c with nameenv. Right now we're just blindly
                 * giving away the type associated with a name without checking
                 * whether this expression type was what we were looking for.
                 * *)
                add_to_name_cache (Ast_c.str_of_name name) file
      | Ast_c.Declaration
          (Ast_c.DeclList
            ([{Ast_c.v_namei = None;
              Ast_c.v_type = typ}, _], _)) ->
            (match (Ast_c.unwrap (snd typ)) with
              Ast_c.StructUnion (_, _, def) ->
                (* Cache field names *)
                cache_struct_fields def
            | Ast_c.Enum(_, def) ->
                (* Cache enumeration constants *)
                cache_enum_constants def
            | Ast_c.TypeName(_, def) ->
                (* TODO: might have to cross reference the current
                 * struct definitions and get the fields from there. *)
                k p
            | _ -> k p)
      | Ast_c.CppTop
          (Ast_c.Define (name, _)) ->
            add_to_name_cache (Ast_c.unwrap name) file
      | _ -> k p
  }


(* Bad hack for enumerator return types. Shows that this module needs
 * to be somewhere else. *)
let mk_fulltype bt str =
  Ast_c.mk_ty
   (Ast_c.BaseType bt)
   [Ast_c.al_info 0 (* al *)
    {Ast_c.pinfo =
     Ast_c.OriginTok
      {Common.str = str; Common.charpos = 0; Common.line = -1;
       Common.column = -1; Common.file = ""};
    Ast_c.cocci_tag =
     {contents = None};
    Ast_c.annots_tag = Token_annot.empty;
    Ast_c.comments_tag = {contents =
        {Ast_c.mbefore = []; Ast_c.mafter = [];
         Ast_c.mbefore2 = []; Ast_c.mafter2 = []
        }};
    Ast_c.danger = ref Ast_c.NoDanger;}]

let (int_type: Ast_c.fullType) =
  (* Lib_parsing_c.al_type   (Parse_c.type_of_string "int")*)
  mk_fulltype (Ast_c.IntType (Ast_c.Si (Ast_c.Signed, Ast_c.CInt))) "int"


(* Kind of a very minimized version of what TAC does. Just search
 * toplevel with the given name, and get the type for it. *)
let get_type_visitor file name l =
  let get_type typ =
    l := [(Some (typ, Ast_c.NotLocalVar), Ast_c.NotTest)] @ !l in
  let get_struct_fields def =
    let _get_field field =
      match (Ast_c.unwrap field) with
        Ast_c.Simple (n, ft)
      | Ast_c.BitField (n, ft, _, _) ->
          n +>
            do_option
              (fun na ->
                 if (Ast_c.str_of_name na) = name
                 then get_type ft) in
    let _get_struct_fields field =
      match field with
        Ast_c.DeclarationField(Ast_c.FieldDeclList(l)) ->
          List.iter _get_field (Ast_c.unwrap l)
      | _ -> () in
    List.iter _get_struct_fields def in
  let get_enum_constants def =
    def +>
      List.iter
        (fun ec ->
           let n = (Ast_c.unwrap ec) +> fst +> Ast_c.str_of_name in
           if n = name then get_type int_type) in
  { Visitor_c.default_visitor_c with
    Visitor_c.ktoplevel = fun (k, bigf) p ->
      match p with
        Ast_c.Declaration
          (Ast_c.DeclList
            ([{Ast_c.v_namei = Some (n, _);
              Ast_c.v_type = typ}, _], _))
            when (Ast_c.str_of_name n) = name ->
                get_type typ
      | Ast_c.Declaration
          (Ast_c.DeclList
            ([{Ast_c.v_namei = None;
              Ast_c.v_type = typ}, _], _)) ->
            (match (Ast_c.unwrap (snd typ)) with
              Ast_c.StructUnion (_, _, def) ->
                get_struct_fields def
            | Ast_c.Enum(_, def) ->
                get_enum_constants def
            | _ -> k p)
      | _ -> k p
  }

(* Use the visitor to extract funprotos, macros, typedefs and struct
 * names.
 * NOTE: could either do this or populate the environment from here. *)
let extract_names file ast =
  ignore (Visitor_c.vk_program (cache_name_visitor file) ast)

(* Use the visitor to get the type we need. *)
let get_type_from_name_cache file name parse_fn =
  let rec find_file l =
    match l with
      [] -> None
    | x::xs ->
        if path_exists_dependency_graph file x
        then Some x
        else find_file xs in
  let return_type l =
    if List.length l <> 1
    then None
    else Some (List.hd l) in
  let get_ast x =
    match !cur_files with
      Some (a, n) when n = file ->
        (try Hashtbl.find a x
        with Not_found ->
          (pr_inc
            (Printf.sprintf
              "INCLUDES CACHE: Parsing %s for %s" x name);
          let _ast = parse_fn x in
          Hashtbl.add a x _ast;
          _ast))
    | None
    | Some _ ->
        let a = Hashtbl.create 101 in
        pr_inc
          (Printf.sprintf
            "INCLUDES CACHE: Parsing %s for %s" x name);
        let _ast = parse_fn x in
        Hashtbl.add a x _ast;
        cur_files := Some (a, file);
        _ast in

  if Includes.is_header file
  then None
  else
  let file_list =
    try Hashtbl.find !name_cache name
    with Not_found -> [] in
  match (find_file file_list) with
    None -> None
  | Some x ->
      let ast = get_ast x in
      let type_list = ref [] in
      ignore
        (Visitor_c.vk_program
           (get_type_visitor file name type_list) ast);
      return_type !type_list

let print_hashtable _ =
  Hashtbl.iter
    (fun x y ->
       pr_no_nl (Printf.sprintf "%s -> " x);
       List.iter (fun z -> pr_no_nl (Printf.sprintf "%s " z)) y;
       pr_no_nl (Printf.sprintf "\n"))
    !name_cache


(*****************************************************************************)
(* Set of parsed files *)
(*****************************************************************************)

(* Probably no need for a set of parsed files. *)

module StringSet = Set.Make (String)

(* Set of files parsed *)
let seen_files = ref (StringSet.empty)

let has_been_parsed file =
  StringSet.mem file !seen_files

let add_to_parsed_files file =
  seen_files := StringSet.add file !seen_files
