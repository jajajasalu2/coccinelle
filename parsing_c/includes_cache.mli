(*
 * This file is part of Coccinelle, licensed under the terms of the GPL v2.
 * See copyright.txt in the Coccinelle source code for more information.
 * The Coccinelle source code can be obtained at http://coccinelle.lip6.fr
 *)

type cache_exp =
  | CacheField of string (* Name of the struct/union it is defined in *)
  | CacheEnumConst
  | CacheVarFunc
  | CacheTypedef

(*val print_hashtable : unit -> unit*)

val has_been_parsed : string -> bool

val add_to_parsed_files : string -> unit

val add_to_dependency_graph : string -> string -> unit

val path_exists_dependency_graph : Common.filename -> Common.filename -> bool

val extract_names : Common.filename -> Ast_c.program -> unit

val print_dependency_graph : unit -> unit

val get_type_from_name_cache :
  Common.filename ->
    string ->
    cache_exp ->
    (Common.filename -> Ast_c.program) ->
    Ast_c.exp_info option

