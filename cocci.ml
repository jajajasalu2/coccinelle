open Common open Commonop

module CCI = Ctlcocci_integration
module TAC = Type_annoter_c

(*****************************************************************************)
(* This file is a kind of driver. It gathers all the important functions 
 * from coccinelle in one place. The different entities in coccinelle are:
 *  - files
 *  - astc
 *  - astcocci
 *  - flow (contain nodes)
 *  - ctl  (contain rule_elems)
 * This file contains functions to transform one in another.
 *)
(*****************************************************************************)

(* --------------------------------------------------------------------- *)
(* C related *)
(* --------------------------------------------------------------------- *)
let cprogram_from_file file = 
  let (program2, _stat) = Parse_c.parse_print_error_heuristic file in
  program2 

let cfile_from_program program2_with_ppmethod outf = 
  Unparse_c.pp_program program2_with_ppmethod outf


  

let (cstatement_from_string: string -> Ast_c.statement) = fun s ->
  begin
    Common.write_file ("/tmp/__cocci.c") ("void main() { \n" ^ s ^ "\n}");
    let program = cprogram_from_file ("/tmp/__cocci.c") in
    program +> Common.find_some (fun (e,_) -> 
      match e with
      | Ast_c.Definition ((funcs, _, _, [st]),_) -> Some st
      | _ -> None
      )
  end

let (cexpression_from_string: string -> Ast_c.expression) = fun s ->
  begin
    Common.write_file ("/tmp/__cocci.c") ("void main() { \n" ^ s ^ ";\n}");
    let program = cprogram_from_file ("/tmp/__cocci.c") in
    program +> Common.find_some (fun (e,_) -> 
      match e with
      | Ast_c.Definition ((funcs, _, _, compound),_) -> 
          (match compound with
          | [(Ast_c.ExprStatement (Some e),ii)] -> Some e
          | _ -> None
          )
      | _ -> None
      )
  end
  

(* --------------------------------------------------------------------- *)
(* Cocci related *)
(* --------------------------------------------------------------------- *)
let sp_from_file file iso    = Parse_cocci.process file iso false

let (rule_elem_from_string: string -> filename option -> Ast_cocci.rule_elem) =
 fun s iso -> 
  begin
    Common.write_file ("/tmp/__cocci.cocci") (s);
    let (astcocci, _,_) = sp_from_file ("/tmp/__cocci.cocci") iso in
    let stmt =
      astcocci +> List.hd +> (function (_,_,x) -> List.hd x) +> (function x ->
	match Ast_cocci.unwrap x with
	| Ast_cocci.CODE stmt_dots -> Ast_cocci.undots stmt_dots +> List.hd
	| _ -> raise Not_found)
    in
    match Ast_cocci.unwrap stmt with
    | Ast_cocci.Atomic(re) -> re
    | _ -> failwith "only atomic patterns allowed"
  end


(* --------------------------------------------------------------------- *)
(* Flow related *)
(* --------------------------------------------------------------------- *)
let flows astc = 
  astc +> Common.map_filter (fun e -> 
    match e with
    | Ast_c.Definition (((funcs, _, _, c),_) as def) -> 
        let flow = Ast_to_flow.ast_to_control_flow def in
        let everythings_fine = 
          (try Ast_to_flow.deadcode_detection flow; true
           with Ast_to_flow.Error (Ast_to_flow.DeadCode x) -> 
             Ast_to_flow.report_error (Ast_to_flow.DeadCode x);
             false 
          )
        in
        if everythings_fine then Some flow else None
    | _ -> None
   )

let one_flow flows = List.hd flows

let print_flow flow = 
  Ograph_extended.print_ograph_extended flow "/tmp/test.dot" 

(* --------------------------------------------------------------------- *)
(* Ctl related *)
(* --------------------------------------------------------------------- *)
let ctls ast ua  =
  List.map2
    (function ast -> function ua ->
      List.combine
	(if !Flag.popl
	then Popl.popl ast
	else Asttoctl2.asttoctl ast ua)
	(Asttomember.asttomember ast ua))
    ast ua

let one_ctl ctls = List.hd (List.hd ctls)




(*****************************************************************************)
(* Some  debugging functions *)
(*****************************************************************************)

(* the inputs *)

let show_or_not_cfile2 cfile =
  if !Flag.show_c then begin
    Common.pr2_xxxxxxxxxxxxxxxxx ();
    pr2 ("processing C file: " ^ cfile);
    Common.pr2_xxxxxxxxxxxxxxxxx ();
    Common.command2 ("cat " ^ cfile);
  end
let show_or_not_cfile a = 
  Common.profile_code "show_xxx" (fun () -> show_or_not_cfile2 a)

let show_or_not_cocci2 coccifile isofile = 
  if !Flag.show_cocci then begin
    Common.pr2_xxxxxxxxxxxxxxxxx ();
    pr2 ("processing semantic patch file: " ^ coccifile);
    isofile +> Common.do_option (fun s -> pr2 ("with isos from: " ^ s));
    Common.pr2_xxxxxxxxxxxxxxxxx ();
    Common.command2 ("cat " ^ coccifile);
    pr2 "";
  end
let show_or_not_cocci a b = 
  Common.profile_code "show_xxx" (fun () -> show_or_not_cocci2 a b)


(* the output *)

let show_or_not_diff2 cfile outfile = 
  if !Flag.show_diff then begin
    (* may need --strip-trailing-cr under windows *)
    pr2 "diff = ";
    Common.command2 ("diff -u -b -B " ^ cfile ^ " " ^ outfile);
  end
let show_or_not_diff a b  = 
  Common.profile_code "show_xxx" (fun () -> show_or_not_diff2 a b)


(* the derived input *)

let show_or_not_ctl_tex2 astcocci ctls =
  if !Flag.show_ctl_tex then begin
    Ctltotex.totex ("/tmp/__cocci_ctl.tex") astcocci ctls;
    Common.command2 ("cd /tmp; latex __cocci_ctl.tex; " ^
              "dvips __cocci_ctl.dvi -o __cocci_ctl.ps;" ^
              "gv __cocci_ctl.ps &");
  end
let show_or_not_ctl_tex a b  = 
  Common.profile_code "show_xxx" (fun () -> show_or_not_ctl_tex2 a b)



let show_or_not_ctl_text2 ctl ast rulenb =
  if !Flag.show_ctl_text then begin

    Common.pr_xxxxxxxxxxxxxxxxx ();
    pr ("rule " ^ i_to_s rulenb ^ " = ");
    Common.pr_xxxxxxxxxxxxxxxxx ();
      adjust_pp_with_indent (fun () -> 
        Format.force_newline();
        Pretty_print_cocci.print_plus_flag := true;
        Pretty_print_cocci.print_minus_flag := true;
        Pretty_print_cocci.unparse ast;
      );

    pr "CTL = ";
    let (ctl,_) = ctl in
    adjust_pp_with_indent (fun () -> 
      Format.force_newline();
      Pretty_print_engine.pp_ctlcocci 
        !Flag.show_mcodekind_in_ctl !Flag.inline_let_ctl ctl;
    );
    pr "";
  end
let show_or_not_ctl_text a b c = 
  Common.profile_code "show_xxx" (fun () -> show_or_not_ctl_text2 a b c)



(* running information *)

let show_or_not_celem2 prelude celem = 
  if !Flag.show_misc then 
  (match celem with 
  | Ast_c.Definition ((funcs,_,_,_c),_) -> 
      pr2 (prelude ^ " function: " ^ funcs);
  | Ast_c.Declaration (Ast_c.DeclList ([(Some ((s, _),_), typ, sto), _], _)) ->
      pr2 (prelude ^ " variable " ^ s);
  | _ -> 
      pr2 (prelude ^ " something else");
  )
let show_or_not_celem a b  = 
  Common.profile_code "show_xxx" (fun () -> show_or_not_celem2 a b)


let show_or_not_trans_info2 trans_info = 
  if !Flag.show_transinfo then begin
    if null trans_info then pr2 "transformation info is empty"
    else begin
      pr2 "transformation info returned:";
      let trans_info =
        List.sort (function (i1,_,_) -> function (i2,_,_) -> compare i1 i2)
          trans_info 
      in
      indent_do (fun () -> 
        trans_info +> List.iter (fun (i, subst, re) -> 
          pr2 ("transform state: " ^ (Common.i_to_s i));
          indent_do (fun () -> 
            adjust_pp_with_indent_and_header "with rule_elem: " (fun () -> 
              Pretty_print_cocci.print_plus_flag := true;
              Pretty_print_cocci.print_minus_flag := true;
              Pretty_print_cocci.rule_elem "" re;
            );
            adjust_pp_with_indent_and_header "with binding: " (fun () -> 
              Pretty_print_c.pp_binding subst;
            );
          )
        );
      )
    end
  end
let show_or_not_trans_info a  = 
  Common.profile_code "show_xxx" (fun () -> show_or_not_trans_info2 a)



let show_or_not_binding2 s binding =
  if !Flag.show_binding_in_out then begin
    adjust_pp_with_indent_and_header ("binding " ^ s ^ " = ") (fun () -> 
      Pretty_print_c.pp_binding binding;
    )
  end
let show_or_not_binding a b  = 
  Common.profile_code "show_xxx" (fun () -> show_or_not_binding2 a b)



(*****************************************************************************)
(* Some  helpers functions *)
(*****************************************************************************)
let worth_trying cfile tokens = 
  if not !Flag.windows && not (null tokens)
  then
   (* could also modify the code in get_constants.ml *)
    let tokens = tokens +> List.map (fun s -> 
      match () with 
      | _ when s =~ "^[A-Za-z_][A-Za-z_0-9]*$" -> 
          "\\b" ^ s ^ "\\b"

      | _ when s =~ "^[A-Za-z_]" -> 
          "\\b" ^ s

      | _ when s =~ ".*[A-Za-z_]$" -> 
          s ^ "\\b"
      | _ -> s

    ) in
    (match Sys.command (sprintf "egrep -q '(%s)' %s" (join "|" tokens) cfile)
    with
    | 0 (* success *) -> true
    | _ (* failure *) -> false (* no match, so not worth trying *)
    )
  else true



let contain_loop top = 
  let res = ref false in
  top +> Visitor_c.vk_program { Visitor_c.default_visitor_c with
   Visitor_c.kstatement = (fun (k, bigf) stat -> 
     match stat with 
     | Ast_c.Iteration _, ii
     (* overapproximation cos a goto doesn't always lead to a loop *)
     | Ast_c.Jump (Ast_c.Goto _), ii -> 
         res := true
     | st -> k st
     )
     };
  !res

let sp_contain_typed_metavar toplevel_list_list = 
  let bind x y = x or y in
  let option_default = false in
  let mcode _ _ = option_default in
  let donothing r k e = k e in

  let expression r k e =
    match Ast_cocci.unwrap e with
    | (Ast_cocci.MetaExpr (_,_,Some t,_)| Ast_cocci.MetaConst (_,_,Some t,_)) 
      -> true
    | _ -> k e 
  in

  let combiner = 
    Visitor_ast.combiner bind option_default
      mcode mcode mcode mcode mcode mcode mcode mcode mcode mcode mcode mcode
      donothing donothing donothing donothing
      donothing expression donothing donothing donothing donothing donothing
      donothing donothing donothing donothing donothing 
  in
  toplevel_list_list +> 
    List.exists
    (function (nm,deps,rule) ->
      (List.exists combiner.Visitor_ast.combiner_top_level rule))
    

(* --------------------------------------------------------------------- *)
(* local includes and typing environment *)
(* --------------------------------------------------------------------- *)

let extract_local_includes cs = 
  cs +> Common.map_filter (fun (c,_info_item) -> 
    match c with
    | Ast_c.Include (s,_) -> 
        if s=~ "^\"\\(.*\\)\"$"
        then Some (matched1 s)
        else None
    | _ -> None
  )


(* --------------------------------------------------------------------- *)
(* Helpers for SpecialDeclMacro *)
(* --------------------------------------------------------------------- *)

let specialdeclmacro_to_stmt (s, args, ii) =
  let (iis, iiopar, iicpar, iiptvirg) = tuple_of_list4 ii in
  let ident = (Ast_c.Ident s, Ast_c.noType()), [iis] in
  let f = (Ast_c.FunCall (ident, args), Ast_c.noType()), [iiopar;iicpar] in
  let stmt = Ast_c.ExprStatement (Some f), [iiptvirg] in
  stmt,  (f, [iiptvirg])

let stmt_to_specialdeclmacro (e, ii) = 
  let _iiptvirg = tuple_of_list1 ii in
  match e with 
  | Some 
      (
        (Ast_c.FunCall 
            (((Ast_c.Ident s, _noType), [iis]), args), _noType2), 
        [iiopar;iicpar]
      )

      -> raise Todo
  | _ -> raise Impossible


(* --------------------------------------------------------------------- *)
(* Helpers for flow *)
(* --------------------------------------------------------------------- *)

let ast_to_flow_with_error_messages2 def =
  let flowopt = 
    try Some (Ast_to_flow.ast_to_control_flow def)
    with Ast_to_flow.Error x -> 
      Ast_to_flow.report_error x;
      None
  in
  flowopt +> do_option (fun flow -> 
    (* This time even if there is a deadcode, we still have a
     * flow graph, so I can try the transformation and hope the
     * deadcode will not bother us. 
     *)
    try Ast_to_flow.deadcode_detection flow
    with Ast_to_flow.Error (Ast_to_flow.DeadCode x) -> 
      Ast_to_flow.report_error (Ast_to_flow.DeadCode x);
  );
  flowopt
let ast_to_flow_with_error_messages a = 
  Common.profile_code "flow" (fun () -> ast_to_flow_with_error_messages2 a)



let flow_info e = 
  match e with 
  | Ast_c.Definition (((funcs, _, _, c),_) as def) -> 
      (* if !Flag.show_misc then pr2 ("build info function " ^ funcs); *)
      
      let flowopt = ast_to_flow_with_error_messages def in
      flowopt +> map_option (fun flow -> 
      
        (* remove the fake nodes for julia *)
        let fixed_flow = CCI.fix_flow_ctl flow in

        if !Flag.show_flow then print_flow fixed_flow;
        if !Flag.show_before_fixed_flow then print_flow flow;

        fixed_flow

      )
  | Ast_c.Declaration _ 
  | Ast_c.Include _ 
  | Ast_c.Define _  
  | Ast_c.SpecialMacro _
    -> 
      let (elem, str) = 
        match e with 
        | Ast_c.Declaration decl -> (Control_flow_c.Decl decl),  "decl"
        | Ast_c.Include x -> (Control_flow_c.Include x), "#include"
        | Ast_c.Define (x,body) -> (Control_flow_c.Define (x,body)), "#define"
        (* todo? still useful ? could consider as Decl instead *)
        | Ast_c.SpecialMacro (s, args, ii) -> 
            let (st, (e, ii)) = specialdeclmacro_to_stmt (s, args, ii) in
            (Control_flow_c.ExprStatement (st, (Some e, ii))), "macrotoplevel"


        | _ -> raise Impossible
      in
      let flow = Ast_to_flow.simple_cfg elem str  in
      let fixed_flow = CCI.fix_simple_flow_ctl flow in
      Some fixed_flow
  | _ -> None



(*****************************************************************************)
(* All the information needed around the C elements and Cocci rules *)
(*****************************************************************************)

type toplevel_c_info = { 
  ast_c: Ast_c.toplevel; (* contain refs so can be modified *)
  tokens_c: Parser_c.token list;
  fullstring: string;

  flow: Control_flow_c.cflow option; (* it's the "fixed" flow *)
  contain_loop: bool;
  
  env_typing_before: TAC.environment;
  env_typing_after:  TAC.environment;

  was_modified: bool ref;

  (* id: int *)
}

type toplevel_cocci_info = {
  ctl: Lib_engine.ctlcocci * (CCI.pred list * CCI.pred list);
  ast_rule: Ast_cocci.rule;

  rulename: string;
  dependencies: string list;
  used_after: Ast_cocci.meta_name list;

  ruleid: int;

  was_matched: bool ref;
}

type header_info = { 
  header_name : string;
  was_modified_once: bool ref;
  header_content: toplevel_c_info list;
  header_path : string;
}

let g_contain_typedmetavar = ref false 

let fake_env = TAC.initial_env



let last_env_toplevel_c_info xs =
  (Common.last xs).env_typing_after

let concat_headers_and_c hss cs = 
  (List.concat (hss +> List.map (fun x -> x.header_content))) ++ cs

(* --------------------------------------------------------------------- *)
let prepare_cocci ctls used_after_lists astcocci = 

  let gathered = Common.index_list_1 (zip (zip ctls astcocci) used_after_lists)
  in
  gathered +> List.map 
    (fun (((ctl_toplevel_list,ast),used_after_list),rulenb) -> 
      
      if not (List.length ctl_toplevel_list = 1)
      then failwith "not handling multiple minirules";

      let (rulename, dependencies, restast) = ast in
      { 
        ctl = List.hd ctl_toplevel_list;
        ast_rule = ast;
        rulename = rulename;
        dependencies = dependencies;
        used_after = List.hd used_after_list;
        ruleid = rulenb;
        was_matched = ref false;
      }
    )


(* --------------------------------------------------------------------- *)

let build_info_program cprogram env = 
  let (cs, parseinfos) = Common.unzip cprogram in
  let (cs, envs) = 
    if !g_contain_typedmetavar 
    then Common.unzip (TAC.annotate_program env cs)
    else Common.unzip (cs +> List.map (fun c -> c, (fake_env, fake_env)))
  in

  zip (zip cs parseinfos) envs +> List.map (fun ((c, parseinfo), (enva,envb))->
    let (fullstr, tokens) = parseinfo in

    {
      ast_c = c; (* contain refs so can be modified *)
      tokens_c =  tokens;
      fullstring = fullstr;

      flow = flow_info c; (* it's the "fixed" flow *)
      contain_loop = contain_loop c;
  
      env_typing_before = enva;
      env_typing_after = envb;

      was_modified = ref false;
    }
  )



(* Optimisation. Try not unparse/reparse the whole file when have modifs  *)
let rebuild_info_program cs = 
  cs +> List.map (fun c ->
    if !(c.was_modified)
    then begin
      let file = Common.new_temp_file "cocci_small_output" ".c" in
      cfile_from_program 
        [(c.ast_c, (c.fullstring, c.tokens_c)), Unparse_c.PPnormal] file;

      (* Common.command2 ("cat " ^ file); *)
      let cprogram = cprogram_from_file file in
      let xs = build_info_program cprogram c.env_typing_before in

      (* TODO: assert env has not changed,
       * if yes then must also reparse what follows even if not modified.
       * Do that only if contain_typedmetavar of course, so good opti.
       *)
      (* Common.list_init xs *) (* get rid of the FinalDef *)
      xs
    end
    else [c]
  ) +> List.concat


let rebuild_info_c_and_headers (cs, hss) = 

  hss +> List.iter (fun hi -> 
    if hi.header_content +> List.exists (fun c -> !(c.was_modified))
    then hi.was_modified_once := true;
  );
  let hss' = 
    hss +> List.map (fun hi -> 
      { hi with header_content = rebuild_info_program hi.header_content }
    )
  in
  let cs' = rebuild_info_program cs in
  cs', hss'




let prepare_c file = 
  let cprogram = cprogram_from_file file in
  let local_includes = extract_local_includes cprogram in
  let dir = (Common.dirname file) in

  let env = ref TAC.initial_env in

  let hss = local_includes +> Common.map_filter (fun h -> 
    let realh = Filename.concat dir h in 

    if not (Common.lfile_exists realh) 
    then begin pr2 ("TYPE: local header " ^ realh ^ " not found"); None end
    else 
      let h_cs = cprogram_from_file realh in
      let info_h_cs = build_info_program h_cs !env in
      env := 
        if null info_h_cs
        then !env
        else last_env_toplevel_c_info info_h_cs
      ;

      Some { 
        header_name = h;
        header_content = info_h_cs;
        was_modified_once = ref false;
        header_path = realh;
      }
  ) in
  build_info_program cprogram !env,
  hss


(*****************************************************************************)
(* Processing the ctls and toplevel C elements *)
(*****************************************************************************)

(* The main algorithm =~
 * The algorithm is roughly: 
 *  for_all ctl rules in SP
 *   for_all minirule in rule (no more)
 *    for_all binding (computed during previous phase)
 *      for_all C elements
 *         match control flow of function vs minirule 
 *         with the binding and update the set of possible 
 *         bindings, and returned the possibly modified function.
 *   pretty print modified C elements and reparse it.
 *
 * 
 * On ne prends que les newbinding ou returned_any_state est vrai.
 * Si ca ne donne rien, on prends ce qu'il y avait au depart.
 * Mais au nouveau depart de quoi ?  
 * - si ca donne rien apres avoir traité toutes les fonctions avec ce binding ?
 * - ou alors si ca donne rien, apres avoir traité toutes les fonctions 
 *   avec tous les bindings du round d'avant ?
 * 
 * Julia pense qu'il faut prendre la premiere solution.
 * Example: on a deux environnements candidats, E1 et E2 apres avoir traité
 * la regle ctl 1. On arrive sur la regle ctl 2.
 * E1 ne donne rien pour la regle 2, on garde quand meme E1 pour la regle 3.
 * E2 donne un match a un endroit et rend E2' alors on utilise ca pour
 * la regle 3.
 * 
 * I have not to look at used_after_list to decide to restart from
 * scratch. I just need to look if the binding list is empty.
 * Indeed, let's suppose that a SP have 3 regions/rules. If we
 * don't find a match for the first region, then if this first
 * region does not bind metavariable used after, that is if
 * used_after_list is empty, then mysat(), even if does not find a
 * match, will return a Left, with an empty transformation_info,
 * and so current_binding will grow. On the contrary if the first
 * region must bind some metavariables used after, and that we
 * dont find any such region, then mysat() will returns lots of
 * Right, and current_binding will not grow, and so we will have
 * an empty list of binding, and we will catch such a case. 
 *
 * opti: julia says that because the binding is
 * determined by the used_after_list, the items in the list
 * are kind of sorted, so could optimise the insert_set operations.
 *)


(* r(ule), c(element), e(nvironment) *)

let rec bigloop rs (cs,hss) = 
  let es = ref [Ast_c.emptyMetavarsBinding] in
  let cs = ref cs in
  let hss = ref hss in
  let rules_that_have_matched = ref [] in

  (* looping over the rules *)
  rs +> List.iter (fun r -> 
   show_or_not_ctl_text r.ctl r.ast_rule r.ruleid;

   if not (Common.include_set r.dependencies !rules_that_have_matched)
   then pr2 ("dependencies for rule " ^ r.rulename ^ " not satisfied")
   else begin

    let newes = ref [] in (* envs for next round/rule *)

    (* looping over the environments *)
    !es +> List.iter (fun e -> 
      show_or_not_binding "in" e;

      let children_e = ref [] in
      
      (* looping over the functions and toplevel elements in .h and .h *)
      concat_headers_and_c !hss !cs +> List.iter (fun c -> 
        if c.flow <> None 
        then
          (* does also some side effects on c and r *)
          match process_a_ctl_a_env_a_toplevel r e c with
          | None -> ()
          | Some newbindings -> 
              newbindings +> List.iter (fun newbinding -> 
                children_e := Common.insert_set newbinding !children_e;
              )
      ); (* end iter cs *)

      let children_e_final = 
        if not (null !children_e)
        then !children_e
        else begin
          if !Flag_ctl.partial_match
          then printf "Empty list of bindings, I will restart from old env";
          [e +> List.filter (fun (s,v) -> List.mem s r.used_after)]
        end
      in
          
      newes := Common.union_set !newes children_e_final;
      
    ); (* end iter es *)
    es := !newes;
    let (newcs, newhss) = rebuild_info_c_and_headers (!cs, !hss) in
    cs := newcs; hss := newhss;
    if !(r.was_matched) then Common.push2 r.rulename rules_that_have_matched
   end
  ); (* end iter rs *)

  !cs, !hss (* return final C asts *)





(* does side effects on C ast and on Cocci info rule *)
and process_a_ctl_a_env_a_toplevel2 r e c = 
 indent_do (fun () -> 

  let (trans_info, returned_any_states, newbindings) = 
    Common.save_excursion Flag_ctl.loop_in_src_code (fun () -> 
      Flag_ctl.loop_in_src_code := !Flag_ctl.loop_in_src_code||c.contain_loop;
      
      (***************************************)
      (* !Main point! The call to the engine *)
      (***************************************)
      let model_ctl  = CCI.model_for_ctl (Common.some c.flow) e in
      CCI.mysat model_ctl r.ctl (r.used_after, e)
    ) 
  in
  if not returned_any_states 
  then None
  else begin
    show_or_not_celem "found match in" c.ast_c;
    show_or_not_trans_info trans_info;
    List.iter (show_or_not_binding "out") newbindings;    

    r.was_matched := true;

    if not (null trans_info)
    then begin
      c.was_modified := true;
      (* modify ast via side effect *)
      ignore(Transformation3.transform trans_info (some c.flow));
    end;

    Some newbindings
  end
 )
   
and process_a_ctl_a_env_a_toplevel  a b c = 
  Common.profile_code "process_a_ctl_a_env_a_toplevel" 
    (fun () -> process_a_ctl_a_env_a_toplevel2 a b c)
   


(*****************************************************************************)
(* The main function *)
(*****************************************************************************)

(* Returns nothing. The output is in the file outfile *)
let full_engine2 cfile (coccifile, isofile) outfile = 

  show_or_not_cfile   cfile;
  show_or_not_cocci   coccifile isofile;

  let (astcocci,used_after_lists,toks) = sp_from_file coccifile isofile in
  let ctls = ctls astcocci used_after_lists in
  let contain_typedmetavar = sp_contain_typed_metavar astcocci in

  (* optimisation allowing to launch coccinelle on all the drivers *)
  if not (worth_trying cfile toks)
  then Common.command2 ("cp " ^ cfile ^ " " ^ outfile)
  else begin

    Common.pr_xxxxxxxxxxxxxxxxx();
    pr "let's go";
    Common.pr_xxxxxxxxxxxxxxxxx();

    g_contain_typedmetavar := contain_typedmetavar;
    let cocci_infos = prepare_cocci ctls used_after_lists astcocci in
    let (c_infos, hs_infos)     = prepare_c cfile in

    show_or_not_ctl_tex astcocci ctls;

    let (c_infos', hs_infos') = bigloop cocci_infos (c_infos, hs_infos) in

    Common.pr_xxxxxxxxxxxxxxxxx ();
    pr "Finished";
    Common.pr_xxxxxxxxxxxxxxxxx();

    (* and now unparse everything *)
    let for_unparser xs = xs +> List.map (fun x -> 
      (x.ast_c, (x.fullstring, x.tokens_c)), Unparse_c.PPviastr
    )
    in
    cfile_from_program (for_unparser c_infos') outfile;

    show_or_not_diff cfile outfile;

    hs_infos' +> List.iter (fun hi -> 
      let outheader = outfile ^ "." ^ hi.header_name ^ ".h" in
      if !(hi.was_modified_once)
      then begin
        pr2 ("a header file was modified: " ^ hi.header_name);
        cfile_from_program (for_unparser hi.header_content) outheader;
        show_or_not_diff hi.header_path outheader;
      end
    );
  end


let full_engine a b c = 
  Common.profile_code "full_engine" (fun () -> full_engine2 a b c)
