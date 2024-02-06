(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2022                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


open SmtMisc
open CoqTerms
open SmtTrace
open SmtAtom
open SmtBtype
open SmtCertif


(* let debug = false *)


(******************************************************************************)
(* Given a verit trace build the corresponding certif and theorem             *)
(******************************************************************************)
(* exception Import_trace of int *)

(* let get_val = function
 *     Some a -> a
 *   | None -> assert false *)

(* For debugging certif processing : <add_scertif> <select> <occur> <alloc> *)
(* let print_certif c where=
 *   let r = ref c in
 *   let out_channel = open_out where in
 *   let fmt = Format.formatter_of_out_channel out_channel in
 *   let continue = ref true in
 *   while !continue do
 *     let kind = to_string (!r.kind) in
 *     let id = !r.id in
 *     let pos = match !r.pos with
 *       | None -> "None"
 *       | Some p -> string_of_int p in
 *     let used = !r.used in
 *     Format.fprintf fmt "id:%i kind:%s pos:%s used:%i value:" id kind pos used;
 *     begin match !r.value with
 *     | None -> Format.fprintf fmt "None"
 *     | Some l -> List.iter (fun f -> Form.to_smt Atom.to_smt fmt f;
 *                                     Format.fprintf fmt " ") l end;
 *     Format.fprintf fmt "\n";
 *     match !r.next with
 *     | None -> continue := false
 *     | Some n -> r := n
 *   done;
 *   Format.fprintf fmt "@."; close_out out_channel *)

let import_trace ra_quant rf_quant filename first lsmt =
  let chan = open_in filename in
  let lexbuf = Lexing.from_channel chan in
  let confl_num = ref (-1) in
  let first_num = ref (-1) in
  let is_first = ref true in
  let line = ref 1 in
  (* let _ = Parsing.set_trace true in *)
  try
    while true do
      confl_num := VeritParser.line VeritLexer.token lexbuf;
      if !is_first then (
        is_first := false;
        first_num := !confl_num
      );
      incr line
    done;
    raise VeritLexer.Eof
  with
    | VeritLexer.Eof ->
       close_in chan;
       let cfirst = ref (VeritSyntax.get_clause !first_num) in
       let confl = ref (VeritSyntax.get_clause !confl_num) in
       let re_hash = Form.hash_hform (Atom.hash_hatom ra_quant) rf_quant in

       begin match first with
       | None -> ()
       | Some _ ->
          let init_index = VeritSyntax.init_index lsmt re_hash in
          let cf, lr = order_roots init_index !cfirst in
          cfirst := cf;

          (* Adding quantifier-free lemmas used as inputs in the final
             certificate, using the ForallInst rule (which simply proves
             lemma -> lemma) *)
          let to_add = VeritSyntax.qf_to_add (List.tl lr) in
          let to_add =
            (match first, !cfirst.value with
             | Some (root, l), Some [fl] when init_index fl = 1 && not (Form.equal l (re_hash fl)) ->
                 let cfirst_value = !cfirst.value in
                 !cfirst.value <- root.value;
                 [Other (ImmFlatten (root, fl)), cfirst_value, !cfirst]
             | _ -> []) @ to_add
          in
          match to_add with
            | [] -> ()
            | _  -> confl := add_scertifs to_add !cfirst
       end;

       select !confl;
       occur !confl;
       (alloc !cfirst, !confl)
    | Parsing.Parse_error -> failwith ("Z3.import_trace: parsing error line "^(string_of_int !line))


let clear_all () =
  SmtTrace.clear ();
  SmtMaps.clear ();
  VeritSyntax.clear ()


let import_all fsmt fproof =
  clear_all ();
  let rt = SmtBtype.create () in
  let ro = Op.create () in
  let ra = VeritSyntax.ra in
  let rf = VeritSyntax.rf in
  let ra_quant = VeritSyntax.ra_quant in
  let rf_quant = VeritSyntax.rf_quant in
  let roots = Smtlib2_genConstr.import_smtlib2 rt ro ra rf fsmt in
  let (max_id, confl) = import_trace ra_quant rf_quant fproof None [] in
  (rt, ro, ra, rf, roots, max_id, confl)


let parse_certif t_i t_func t_atom t_form root used_root trace fsmt fproof =
  SmtCommands.parse_certif t_i t_func t_atom t_form root used_root trace
    (import_all fsmt fproof)

let checker_debug fsmt fproof =
  SmtCommands.checker_debug (import_all fsmt fproof)

let theorem name fsmt fproof =
  SmtCommands.theorem name (import_all fsmt fproof)

let checker fsmt fproof =
  SmtCommands.checker (import_all fsmt fproof)



(******************************************************************************)
(** Given a Coq formula build the proof                                       *)
(******************************************************************************)

let export out_channel rt ro lsmt =
  let fmt = Format.formatter_of_out_channel out_channel in
  Format.fprintf fmt "(set-logic UFLIA)@.";

  List.iter (fun (i,t) ->
    let s = "Tindex_"^(string_of_int i) in
    SmtMaps.add_btype s (Tindex t);
    Format.fprintf fmt "(declare-sort %s 0)@." s
  ) (SmtBtype.to_list rt);

  (* declare the constants to represent the quantified variables *)
  List.iter (fun (i,dom,cod,op) ->
    let s = "op_"^(string_of_int i) in
    SmtMaps.add_fun s op;
    Format.fprintf fmt "(declare-fun %s (" s;
    let is_first = ref true in
    Array.iter (fun t -> if !is_first then is_first := false else Format.fprintf fmt " "; SmtBtype.to_smt fmt t) dom;
    Format.fprintf fmt ") ";
    SmtBtype.to_smt fmt cod;
    Format.fprintf fmt ")@."
  ) (Op.to_list ro);

  List.iter (fun u -> Format.fprintf fmt "(assert ";
                      Form.to_smt fmt u;
                      Format.fprintf fmt ")\n") lsmt;

  Format.fprintf fmt "(check-sat)\n(exit)@."

exception Unknown

let call_verit timeout _ _ rt ro ra_quant rf_quant first lsmt =
  let (filename, outchan) = Filename.open_temp_file "verit_coq" ".smt2" in
  export outchan rt ro lsmt;
  close_out outchan;
  let logfilename = Filename.chop_extension filename ^ ".vtlog" in
  let wname, woc = Filename.open_temp_file "warnings_verit" ".log" in
  close_out woc;
  let command = "veriT --proof-prune --proof-merge --proof-with-sharing --cnf-definitional --disable-ackermann --input=smtlib2 --proof=" ^ logfilename ^ " " ^ filename ^ " 2> " ^ wname in
  let command = 
    match timeout with
      | Some i -> "timeout "^(string_of_int i)^" "^command
      | None -> command
  in
  Format.eprintf "%s@." command;
  let t0 = Sys.time () in
  let exit_code = Sys.command command in
  let t1 = Sys.time () in
  Format.eprintf "Verit = %.5f@." (t1-.t0);

  let win = open_in wname in

  let raise_warnings_errors () =
    try
      while true do
        let l = input_line win in
        let n = String.length l in
        if l = "warning : proof_done: status is still open" then
          raise Unknown
        else if l = "Invalid memory reference" then
          CoqInterface.warning "verit-warning" ("veriT outputted the warning: " ^ l)
        else if n >= 7 && String.sub l 0 7 = "warning" then
          CoqInterface.warning "verit-warning" ("veriT outputted the warning: " ^ (String.sub l 7 (n-7)))
        else if n >= 8 && String.sub l 0 8 = "error : " then
          CoqInterface.error ("veriT failed with the error: " ^ (String.sub l 8 (n-8)))
        else
          CoqInterface.error ("veriT failed with the error: " ^ l)
      done
    with End_of_file -> () in
  if exit_code = 124 (*code for timeout*) then (close_in win; Sys.remove wname; let _ = CoqInterface.anomaly "veriT timed out" in ());
  try
    if exit_code <> 0 then CoqInterface.warning "verit-non-zero-exit-code" ("Verit.call_verit: command " ^ command ^ " exited with code " ^ string_of_int exit_code);
    raise_warnings_errors ();
    let res = import_trace ra_quant rf_quant logfilename (Some first) lsmt in
    close_in win; Sys.remove wname; res
  with x -> close_in win; Sys.remove wname;
            match x with
            | Unknown -> CoqInterface.error "veriT returns 'unknown'"
            | VeritSyntax.Sat -> CoqInterface.error "veriT found a counter-example"
            | _ -> raise x

let verit_logic =
  SL.of_list [LUF; LLia]

let tactic_gen vm_cast timeout lcpl lcepl =
  (* Transform the tuple of lemmas given by the user into a list *)
  let lcpl =
    let lcpl = EConstr.Unsafe.to_constr lcpl in
    let lcpl = CoqTerms.option_of_constr_option lcpl in
    match lcpl with
      | Some lcpl -> CoqTerms.list_of_constr_tuple lcpl
      | None -> []
  in

  (* Core tactic *)
  clear_all ();
  let rt = SmtBtype.create () in
  let ro = Op.create () in
  let ra = VeritSyntax.ra in
  let rf = VeritSyntax.rf in
  let ra_quant = VeritSyntax.ra_quant in
  let rf_quant = VeritSyntax.rf_quant in
  SmtCommands.tactic 0 (call_verit timeout) verit_logic rt ro ra rf ra_quant rf_quant vm_cast lcpl lcepl
let tactic = tactic_gen vm_cast_true
let tactic_no_check = tactic_gen (fun _ -> vm_cast_true_no_check)


(* ************* *)
(* Verify tactic *)
(* ************* *)

(*
let export_mock out_channel =
  let fmt = Format.formatter_of_out_channel out_channel in

  Format.fprintf fmt "(set-option :solver.proof.log proof_log.smt2)@.";
  Format.fprintf fmt "(set-option :produce-proofs true)@.";
  
  Format.fprintf fmt "(define-fun-rec append ((l (List Int)) (s (List Int))) (List Int)@.";
  Format.fprintf fmt "(ite (= nil l)@.";
  Format.fprintf fmt "s@.";
  Format.fprintf fmt "(insert (head l) (append (tail l) s))@.";
  Format.fprintf fmt "))@.";

  Format.fprintf fmt "(define-fun-rec reverse ((l (List Int))) (List Int)@.";
  Format.fprintf fmt "(ite (= nil l)@.";
  Format.fprintf fmt "l@.";
  Format.fprintf fmt "(append (reverse (tail l))@.";
  Format.fprintf fmt "(insert (head l) nil))@.";
	Format.fprintf fmt "))@.";

  Format.fprintf fmt "(declare-const l1 (List Int))@.";
  Format.fprintf fmt "(declare-const l2 (List Int))@.";
  Format.fprintf fmt "(assert (= (append (reverse l1) l2) nil))@.";
  Format.fprintf fmt "(assert (or (not (= l1 nil)) (not (= l2 nil))))@.";
  
  Format.fprintf fmt "(check-sat)\n(exit)@."
*)

(* return unit in case of success (unsat) or raises exception *)
let call_z3_verify timeout _ _ rt ro ra_quant rf_quant first lsmt : unit =
  let (filename, outchan) = Filename.open_temp_file "z3_coq" ".smt2" in
  (* export_mock outchan; *)
  export outchan rt ro lsmt;
  close_out outchan;
  (* let logfilename = Filename.chop_extension filename ^ ".vtlog" in *)
  (* let logfilename = "proof_log.smt2" in *)
  let wname, woc = Filename.open_temp_file "warnings_z3" ".log" in
  close_out woc;
  let command = "z3 " ^ filename ^ " > " ^ wname in
  Format.eprintf "%s@." command;
  let t0 = Sys.time () in
  let exit_code = Sys.command command in
  let t1 = Sys.time () in
  Format.eprintf "Verit = %.5f@." (t1-.t0);

  let win = open_in wname in

  let raise_warnings_errors () =
    let answer : Z3Syntax.z3answer option ref = ref None in
    try
      while true do
        let l = input_line win in
        let n = String.length l in
        if n >= 6 && String.sub l 0 6 = "(error" then
          answer := (match !answer with
                     | Some (Z3Syntax.Z3Errors es) ->  Some (Z3Syntax.Z3Errors (l :: es))
                     | _ -> Some (Z3Syntax.Z3Errors [l]))
        else if n >= 3 && String.sub l 0 3 = "sat" then
          match !answer with
          | Some (Z3Syntax.Z3Errors es) -> ()
          | _ -> answer := Some Z3Syntax.Z3Sat
        else if n >= 5 && String.sub l 0 5 = "unsat" then 
          match !answer with
          | Some (Z3Syntax.Z3Errors es) -> ()
          | _ -> answer := Some Z3Syntax.Z3Unsat
        else if n >= 7 && String.sub l 0 7 = "unknown" then 
          match !answer with
          | Some (Z3Syntax.Z3Errors es) -> ()
          | _ -> answer := Some Z3Syntax.Z3Unknown
        else
          CoqInterface.error ("z3 failed with the error: " ^ l)
      done;
      !answer
    with End_of_file -> !answer
  in
  if exit_code = 124 (*code for timeout*) then (close_in win; Sys.remove wname; let _ = CoqInterface.anomaly "z3 timed out" in ());
  (* TODO confirm the exit codes *)
  if exit_code <> 0 then CoqInterface.warning "z3-non-zero-exit-code" ("Z3.verify: command " ^ command ^ " exited with code " ^ string_of_int exit_code);
  let answer = raise_warnings_errors () in 
  (*let res = import_trace ra_quant rf_quant logfilename (Some first) lsmt in*)
  close_in win; 
    (* Sys.remove wname; *)
  (match answer with
    (* TODO change from warning to information *)
    | Some Z3Syntax.Z3Unsat -> CoqInterface.warning "z3" "z3 returned unsat" (*;  CoqInterface.tclIDTAC *)
    | Some Z3Syntax.Z3Sat -> CoqInterface.error ("z3 returned sat")
    | Some Z3Syntax.Z3Unknown -> CoqInterface.error ("z3 returned unknown")
    | Some Z3Syntax.Z3Errors l -> CoqInterface.error ("z3 returned errors:\n" ^ (String.concat "\n" l))
    | None -> CoqInterface.error ("z3 did not return a solution"))
  ;
  ()(*res*)

let tactic_gen' vm_cast timeout lcpl lcepl =
  (* Transform the tuple of lemmas given by the user into a list *)
  let lcpl =
    let lcpl = EConstr.Unsafe.to_constr lcpl in
    let lcpl = CoqTerms.option_of_constr_option lcpl in
    match lcpl with
      | Some lcpl -> CoqTerms.list_of_constr_tuple lcpl
      | None -> []
  in

  (* Core tactic *)
  clear_all ();
  let rt = SmtBtype.create () in
  let ro = Op.create () in
  let ra = VeritSyntax.ra in
  let rf = VeritSyntax.rf in
  let ra_quant = VeritSyntax.ra_quant in
  let rf_quant = VeritSyntax.rf_quant in
  SmtCommands.tactic' 0 (call_z3_verify timeout) verit_logic rt ro ra rf ra_quant rf_quant vm_cast lcpl lcepl
  (*call_z3_verify timeout verit_logic rt ro ra rf ra_quant rf_quant vm_cast lcpl lcepl*)

let tactic' = tactic_gen' vm_cast_true
(* let tactic_no_check' = tactic_gen (fun _ -> vm_cast_true_no_check) *)

(* use z3 logic instead of defining inductive types for trival aspects *)
module M = Map.Make (String)
let special_inductives = M.of_seq (List.to_seq [
  ("Coq.Init.Logic.eq", "=");
  ("Coq.Init.Logic.and", "and");
  ("Coq.Init.Logic.or", "or");
])

let special_funcs = M.of_seq (List.to_seq [
])

(* returns the type of a construction *)
let constr_type (c: Constr.t) 
                (e: Environ.env) 
                (sigma: Evd.evar_map) : Constr.types =
  EConstr.to_constr sigma (
    snd (Typing.type_of e sigma (EConstr.of_constr c)))

(* extract return type of a type, expects Sort, Ind, Arrow. App (e.g. list nat), not dependent type *)
let rec return_type (t: Constr.types) : Constr.types =
  match Constr.kind t with
  | Constr.Sort _ | Constr.Ind _ | Constr.App _ -> t
  | Constr.Prod (n, _, t2) -> 
      (*if Context.binder_name n = Names.Name.Anonymous then
        *)return_type t2 (*
      else
        failwith ("does not support dependent type")*)
  | _ -> failwith ("expected type with sort, arrow or ind")

(* invariants: 
   split_while f l = (l1, l2) -> l1 ++ l2 = l /\ f a for a in l1 and (l2 = [] or not f (hd l2))*)
let rec split_while (f: 'a -> bool) (l: 'a list) : ('a list) * ('a list) =
  match l with
  | [] -> ([], [])
  | h :: t -> if f h then let (r1, r2) = split_while f t in (h :: r1, r2) else ([], l) 

(* given an array of arguments of an app, return two arrays, 
   one with the first type arguments (for polymorphism; ignoring props) 
   and other with the remaining args (i.e. from the first non sort or prop on);
   if the remainig args have types (no prop) raises error*)
let remove_initial_types_non_props (args: Constr.t list)
                      (e: Environ.env) 
                      (sigma: Evd.evar_map) : 
                      (Constr.t list) = 
  let pred a = begin let ty = constr_type a e sigma in 
    Constr.isSort ty && (not (Constr.is_Prop ty)) end in
  let (_, r2) = split_while pred args in
  match List.find_opt pred r2 with
  | Some _ -> failwith "application of types (of non-polymorphic instantiation) not supported"
  | None -> r2
 
(* similiar to remove_initial but also removes Props and returns the also the removed*)
let split_inital_types (args: Constr.t list)
                     (e: Environ.env) 
                     (sigma: Evd.evar_map) : 
                     (Constr.t list) * (Constr.t list) = 
  let pred a = Constr.isSort (constr_type a e sigma) in 
  let (r1, r2) = split_while pred args in
  match List.find_opt pred r2 with
  | Some _ -> failwith "application of types (of non-polymorphic instantiation) not supported"
  | None -> (r1, r2)

let rec ty_to_str (t: Constr.t) : string = 
  match Constr.kind t with
  | Constr.Ind ((n, _), _) -> Names.MutInd.to_string n
  | Constr.Var id -> Names.Id.to_string id
  | Constr.Const (n, _) -> Names.Constant.to_string n
  | Constr.App (f, args) -> ty_to_str f ^ "_" ^ (String.concat "_" (List.map ty_to_str (Array.to_list args))) 
  | Constr.Sort s -> begin match s with
      | Sorts.SProp -> "SProp"
      | Sorts.Prop -> "Prop"
      | Sorts.Set -> "Set"
      | Sorts.Type _ -> "Type"
      end
  | Constr.Prod _ -> failwith "grounded types only instantiation of polymorphic type"
  | _ -> failwith "not expected construct for instantiation of polymorphic type"

let monomorphic_name (name: string) (tys: Constr.types list) : string =
  name ^ "_" ^ (String.concat "_" (List.map ty_to_str tys))

(* error if one of poly args is not Ind - to simplify things *)
(* let gen_mono_name (poly_name: string) (poly_args: Constr.t list) : string =
  poly_name ^ "_" ^ String.concat "_" (List.map ty_to_str poly_args) *)

let _constructor_name (e: Environ.env) (n: Names.inductive) (i: int) : string =
  let ind_info = snd (Inductive.lookup_mind_specif e n) in
  let name = (ind_info.Declarations.mind_consnames).(i) in
  Names.Id.to_string name

(* given a constr with with n nested lambdas as outer-most construction, return its arguments types *)
let rec extract_lambdas_types (n: int) (c: Constr.t) : Constr.types list =
if n = 0 then []
else match Constr.kind c with 
      | Constr.Lambda (_, tn, t1) -> tn :: extract_lambdas_types (n - 1) t1
      | _ -> failwith "extract_lambdas_types: expected a lambda"

(* we generate fresh vars for match *)
let next_match_id : int ref = ref 0

(* name of constant and list of types for monomorphization
   e.g. (app, [A]) -> get a version of app for A, called app_A *)
type pending_def = Names.Constant.t * (Constr.t list) 
let rec pending_defs (e: Environ.env) 
                     (sigma: Evd.evar_map)
                     (c: Constr.t)  : pending_def list =
  match Constr.kind c with
  | Constr.App (f, arr) -> 
    let f_ty = constr_type f e sigma in
      let f_ret_ty = return_type f_ty in
      let args = Array.to_list arr in
      let f_pending = begin
        if Constr.is_Prop f_ret_ty then
          (* we only support some built-in props - eq, and, or...*)
          begin match Constr.kind f with
          | Constr.Ind ((mutind, _), univ) -> 
            let name_str = Names.MutInd.to_string mutind in 
            begin match (M.find_opt name_str special_inductives) with
            | None -> failwith "User-defined props not yet supported"
            | Some _ -> []
            end
          | _ -> failwith "Expected inductive in the place of a Prop"
          end
        else if Constr.isInd f then []
        (* if f returns a type which is a Set, e.g. nat, list nat*)
        else 
          let (tys, _) = split_inital_types args e sigma in 
          match Constr.kind f with
          | Constr.Const (name, _) -> [(name, tys)]
          | _ -> pending_defs e sigma f
      end in f_pending @ List.concat_map (pending_defs e sigma) (Array.to_list arr)
  | Constr.Prod (_, t1, t2) ->
    (pending_defs e sigma t1) @ (pending_defs e sigma t2)
  | Constr.LetIn (_, t1, tn, t2) ->
    (pending_defs e sigma t1) @ (pending_defs e sigma t2) @ (pending_defs e sigma tn)
  | Constr.Lambda (_, tn, t1) ->
    (pending_defs e sigma t1) @ (pending_defs e sigma tn)
    | Constr.Case (_, _, _, scr, arr) -> 
      pending_defs e sigma scr @ List.concat_map (pending_defs e sigma) (Array.to_list arr)
  | _ -> []

let rec c2str (c: Constr.t) : string =
  match Constr.kind c with
  | Constr.Lambda (n, tn, t) -> 
    let n_str = 
      begin match (Context.binder_name n) with
      | Names.Name.Anonymous -> "_"
      | Names.Name.Name id -> Names.Id.to_string id
      end in "Lambda(" ^ n_str ^ ", " ^ c2str tn ^ ", " ^ c2str t ^ ")"
  | Constr.Prod (n, tn, t) -> 
    let n_str = 
      begin match (Context.binder_name n) with
      | Names.Name.Anonymous -> "_"
      | Names.Name.Name id -> Names.Id.to_string id
      end in "Prod(" ^ n_str ^ ", " ^ c2str tn ^ ", " ^ c2str t ^ ")" 
  | Constr.LetIn (n, v, tn, t) -> 
    let n_str = 
      begin match (Context.binder_name n) with
      | Names.Name.Anonymous -> "_"
      | Names.Name.Name id -> Names.Id.to_string id
      end in "LetIn(" ^ n_str ^ ", " ^ c2str tn ^ ", " ^ c2str v ^ ", " ^ c2str t ^ ")"

  | Constr.Var id -> Names.Id.to_string id
  | Constr.Ind ((mutind, _), univ) -> Names.MutInd.to_string mutind 
  | Constr.Const (name, univ) -> Names.Constant.to_string name
  | Constr.Construct (((mutind, _), index), _) -> Names.MutInd.to_string mutind ^ "_c" ^ string_of_int index
  | Constr.Rel i -> "Rel(" ^ string_of_int i ^ ")"
  | Constr.App (f, arr) -> "(" ^ c2str f ^ " " ^ String.concat " " (List.map c2str (Array.to_list arr)) ^ ")"
  | Constr.Case (_, _, _, scr, arr) -> "Match (" ^ c2str scr ^ ", (" ^ String.concat ", " (List.map c2str (Array.to_list arr)) ^ "))"
  | Constr.Meta _ | Constr.Evar _ | Constr.Sort _ -> "spec"
  | Constr.Fix _ -> "fix"
  | _ -> "other"


let declare_var (e: Environ.env) (id: Names.Id.t) (t: Constr.types) : Environ.env =  
  let ba = { Context.binder_name = id
          ; Context.binder_relevance = Sorts.Relevant} in
  let la = Context.Named.Declaration.LocalAssum (ba, t) in
  Environ.push_named la e

(* converts a constr to Z3 expression 
   * rels is the list of names of variables to replace de Brujin indices 
   * a name in position i - 1 should replace (Constr.Rel i)
   * returns a list of pending defs that have to be defined *)
let rec constr_to_z3 (c: Constr.t) 
                     (e: Environ.env) 
                     (rels: string list)
                     (sigma: Evd.evar_map) : string (* * (pending_def list) *)   =
  match Constr.kind c with
  (* TODO inspect App, to check if all cases are handled properly*)
  | Constr.App (f, arr) ->
      let f_ty = constr_type f e sigma in
      let f_ret_ty = return_type f_ty in
      let args = Array.to_list arr in
      (* if f return Prop (e.g. eq, and, or) *)
      if Constr.is_Prop f_ret_ty then 
        (* TODO support user defined propositions *)
        (* remove types e.g. eq nat n1 n2 -> eq n1 n2 *)
        let args_no_types = remove_initial_types_non_props args e sigma in
        begin match args_no_types with
        | [] -> constr_to_z3 f e rels sigma
        | _ :: _ -> 
            let args_str = String.concat " " 
              (List.map (fun c' -> constr_to_z3 c' e rels sigma) args_no_types) in
            "(" ^ constr_to_z3 f e rels sigma ^ " " ^ args_str ^ ")"
        end
      (* if it is an inductive and not of type prop, then it is a "computable" datatype
         so leave the types e.g. list nat - leave the nat *)
      else if Constr.isInd f then
        let args_str = String.concat " " 
          (List.map (fun c' -> constr_to_z3 c' e rels sigma) args) in
            "(" ^ constr_to_z3 f e rels sigma ^ " " ^ args_str ^ ")"
      (* if f returns a type which is a Set, e.g. nat, list nat*)
      else
        let (tys, args') = split_inital_types args e sigma in
        let f_str = begin match Constr.kind f with
                    | Constr.Const (name, _) -> 
                      monomorphic_name (Names.Constant.to_string name) tys
                    | _ -> constr_to_z3 f e rels sigma
                    end in
        begin match args' with
        | [] -> f_str
        | _ :: _ -> 
            let args_str = String.concat " " 
              (List.map (fun c' -> constr_to_z3 c' e rels sigma) args') in
            "(" ^ f_str ^ " " ^ args_str ^ ")"
        end
      
  | Constr.Prod (n, t1, t2) ->  
      begin match (Context.binder_name n) with
      (* the variable of forall is _, so treat as implication *)
      | Names.Name.Anonymous -> 
          "(implies " ^ constr_to_z3 t1 e rels sigma ^ " " ^ constr_to_z3 t2 e rels sigma ^ ")"
      (* the variable has a name *)
      | Names.Name.Name id ->
          (* z3 does not support quantification over props *)
          if Constr.is_Prop t1 
            then failwith "quantification over props is not supported"
            else 
              let name = Names.Id.to_string id in 
              let e' = declare_var e id t1 in
              let t1' = constr_to_z3 t1 e rels sigma in
              let t2' = constr_to_z3 t2 e' rels sigma in
              "(forall ((" ^ name ^ " " ^ t1' ^ ")) " ^ t2' ^ ")"
      end
  | Constr.LetIn (n, t1, tn, t2) ->
      begin match (Context.binder_name n) with  
      (* the variable of forall is _, so treat as implication *)
      | Names.Name.Anonymous -> failwith "let with anonymous binding"
      (* the variable has a name *)
      | Names.Name.Name id ->
          (* z3 does not support quantification over props *)
          if Constr.is_Prop t1 
            then failwith "let with prop is not supported"
            else 
              let name = Names.Id.to_string id in
              let e' = declare_var e id tn in
              let t1' = constr_to_z3 t1 e rels sigma in
              let t2' = constr_to_z3 t2 e' rels sigma in
              "(let ((" ^ name ^ " " ^ t1' ^ ")) " ^ t2' ^ ")" 
      end
  | Constr.Lambda (n, tn, t1) ->
      let name, e' = match (Context.binder_name n) with
                  | Names.Name.Anonymous ->  "_", e
                  | Names.Name.Name id -> 
                    Names.Id.to_string id, declare_var e id tn in
      let tn' = constr_to_z3 tn e rels sigma in
      let t1' = constr_to_z3 t1 e' rels sigma in 
      "(lambda ((" ^ name ^ " " ^ tn' ^ ")) " ^ t1' ^ ")"
  | Constr.Var id -> Names.Id.to_string id (* TODO if it is not a function, get its definition and return *)
  | Constr.Ind ((mutind, _), univ) -> 
      let name_str = Names.MutInd.to_string mutind in 
      Option.default name_str (M.find_opt name_str special_inductives)
  | Constr.Const (name, univ) -> 
      let name_str = Names.Constant.to_string name in
      begin match (Environ.lookup_constant name e).Declarations.const_body with
      | Declarations.Def d ->
          Option.default name_str (M.find_opt name_str special_funcs)
      | _ -> failwith ("definition for name " ^ name_str ^ " is not available")
      end
  | Constr.Construct (((mutind, _), index), univ) -> 
      (* TODO get name of constructor -> get the type, extract ind there *)
      Names.MutInd.to_string mutind ^ "_c" ^ string_of_int index
      (* let ty = constr_type c e sigma in
      let ind_name = fst (fst (Inductive.find_inductive e ty)) in
      constructor_name e ind_name index *)

  | Constr.Case (ci, constr, inv, scr, arr) -> 
    let ind_info = snd (Inductive.lookup_mind_specif e (ci.Constr.ci_ind)) in
    let ind_name = Names.MutInd.to_string (fst ci.Constr.ci_ind) in
    let scr_str = constr_to_z3 scr e rels sigma in 
    let branch_to_z3 (index: int) (body: Constr.t) : string =
      begin
        (* generate fresh id prefix*)
        let match_id = (next_match_id := !next_match_id + 1) ; !next_match_id in
        (* constructor arg count *)
        let args_count = (ind_info.Declarations.mind_consnrealargs).(index) in
        (* [1, 2, ..., arg count] *)
        let sels_indices = List.init args_count (fun x -> x + 1) in
        let c_name = ind_name ^ "_c" ^ string_of_int (index + 1) in
        let sels_names = List.map (fun i -> ("(" ^ c_name ^ "_s" ^ string_of_int i ^ " " ^ scr_str ^ ")")) sels_indices in
        (* generate variables for a let binding fresh variables to selector expressions *)
        let let_vars_names = List.map (fun c -> "mat" ^ string_of_int match_id ^ "_s" ^ string_of_int c) sels_indices in
        let let_bindings = List.map (fun (vn, sn) -> "(" ^ vn ^ " " ^ sn ^ ")") (List.combine let_vars_names sels_names) in
        let let_vars = List.map (fun n -> Constr.mkVar (Names.Id.of_string n)) let_vars_names in
        let body_no_lams = Reduction.beta_applist body let_vars in
        let types = extract_lambdas_types args_count body in
        let e' = List.fold_right 
                  (fun (v, t) r -> 
                    let ba = { Context.binder_name = Names.Id.of_string v
                             ; Context.binder_relevance = Sorts.Relevant} in
                    let la = Context.Named.Declaration.LocalAssum (ba, t) in
                    Environ.push_named la r)
                  (List.combine let_vars_names types)
                  e in
        let body_no_lams_str = constr_to_z3 body_no_lams e' rels sigma in
        let branch_let = "(let (" ^ String.concat "\n" let_bindings ^ ") " ^ body_no_lams_str ^ ")" in
        "(" ^ c_name ^ " " ^  branch_let  ^ ")"
      end
    in
    let brs_indices = List.init (Array.length arr) (fun x -> x) in
    let brs_strs = List.map (fun (a, b) -> branch_to_z3 a b) (List.combine brs_indices (Array.to_list arr)) in 
    "(match " ^ scr_str ^ " (" ^ String.concat "\n" brs_strs ^ "))"
  | Constr.Rel i -> List.nth rels (i - 1)
  | Constr.Fix _ -> failwith ("evaluation of apps of fixpoints not supported yet")
  | Constr.Sort _ -> "(sort)"
  | _ -> failwith "Conversion not supported"

(* given \x1:t1 -> ... \xn:tn -> b returns ([(x1, t1), ..., (xn, tn)], b) *)
let rec extract_lambdas_params (c: Constr.t) : ((Names.Name.t * Constr.types) list) * Constr.t =
  match Constr.kind c with (* TODO rule out dependent types, which cannot be enconded in Z3*)
  | Constr.Lambda (n, tn, t) -> 
    let n' = Context.binder_name n in
    let (l, b) = extract_lambdas_params t in ((n', tn) :: l, b)
  | _ -> ([], c)

let name_id_err (n: Names.Name.t) : Names.Id.t = 
  match n with
  | Names.Name.Name id -> id
  | Names.Name.Anonymous -> failwith "wildcard in fixpoint params not supported"
  
let z3_name (s: string) : string =
  String.concat "_" (String.split_on_char '.' s)

(* returns a def-fun-rec for a pending definition *)
let define_pending (e: Environ.env)
                   (sigma: Evd.evar_map)
                   (p: pending_def) : string =
  let (name, tys) = p in
  match (Environ.lookup_constant name e).Declarations.const_body with
  | Declarations.Def d -> 
    (* typically, a fixpoint definition is fun (A: Type) fun (p1: ty1) ... fix recname fun(p_k+1: ty)... def*)
    (* instantiate polymorphic parameters *)
    let d = Mod_subst.force_constr d in
    let mono_def = if List.length tys = 0 then d
                   else Reduction.beta_applist d tys in
    let fun_name = z3_name (Names.Constant.to_string name) in 
    let mono_name = monomorphic_name fun_name tys in
    CoqInterface.warning "Z3_NAME" mono_name ;
    (* now, we have fun (p1: ty1) ... fix recname fun(p_k+1: ty)... def *)
    (* extract params up to fix *)
    let (vars_types, body) = extract_lambdas_params mono_def in
    let vars = List.map (fun vt -> Constr.mkVar (name_id_err (fst vt))) vars_types in
    let e = List.fold_right 
              (fun (name, ty) r -> declare_var r (name_id_err name) ty)
              vars_types 
              e in
    let body_applied = Reduction.beta_applist mono_def vars in
    (* now, we have fix recname fun(p_k+1: ty)... def *)
    begin match Constr.kind body_applied with
    (* recursive function *)
    | Constr.Fix (_, (names, types, bodies)) -> 
      (* replace rel of the recursive def *)
      let body_fixvar_subst = 
        Reduction.beta_app 
          (Constr.mkLambda (names.(0), types.(0), bodies.(0)))
          (Constr.mkVar (Names.Id.of_string mono_name)) in
      let (vars_types, body) = extract_lambdas_params body_fixvar_subst in
      let vars = List.map (fun vt -> Constr.mkVar (name_id_err (fst vt))) vars_types  in
      let e = List.fold_right 
                (fun (name, ty) r -> declare_var r (name_id_err name) ty)
                (vars_types @ [((Names.Name.Name (Names.Id.of_string mono_name), types.(0)))])
                e in
      let _ = c2str types.(0) in
      let body_applied = Reduction.beta_applist body_fixvar_subst vars in
      (*CoqInterface.warning "body" (c2str bodies.(0)) ; *)
      CoqInterface.warning "body-applied'" (c2str body_applied) ;
      (* CoqInterface.warning "vars" ("There are " ^ string_of_int (List.length vars) ^ " variables") ;*)
      (*CoqInterface.warning "debug" (Pp.db_string_of_pp (Constr.debug_print body_applied));*)
      let binds_str = "" in
      "(define-fun-rec " ^ mono_name ^ " (" ^ binds_str ^ ") " ^ constr_to_z3 (return_type types.(0)) e [] sigma ^ " " ^ 
      constr_to_z3 body_applied e [] sigma ^ ")"
    | _ -> failwith "error"
    end
  | _ -> ""

let call_z3 (script: string) : Z3Syntax.z3answer =
    let (filename, outchan) = Filename.open_temp_file "z3_coq" ".smt2" in
    Printf.fprintf outchan "%s\n" script;  
    close_out outchan;

    (* let logfilename = Filename.chop_extension filename ^ ".vtlog" in *)
    (* let logfilename = "proof_log.smt2" in *)
    let wname, woc = Filename.open_temp_file "warnings_z3" ".log" in
    close_out woc;
    let command = "z3 " ^ filename ^ " > " ^ wname in
    Format.eprintf "%s@." command;
    let t0 = Sys.time () in
    let exit_code = Sys.command command in
    let t1 = Sys.time () in
    Format.eprintf "z3 = %.5f@." (t1-.t0);
  
    let win = open_in wname in
  
    let raise_warnings_errors () =
      let answer : Z3Syntax.z3answer option ref = ref None in
      try
        while true do
          let l = input_line win in
          let n = String.length l in
          if n >= 6 && String.sub l 0 6 = "(error" then
            answer := (match !answer with
                       | Some (Z3Syntax.Z3Errors es) ->  Some (Z3Syntax.Z3Errors (l :: es))
                       | _ -> Some (Z3Syntax.Z3Errors [l]))
          else if n >= 3 && String.sub l 0 3 = "sat" then
            match !answer with
            | Some (Z3Syntax.Z3Errors es) -> ()
            | _ -> answer := Some Z3Syntax.Z3Sat
          else if n >= 5 && String.sub l 0 5 = "unsat" then 
            match !answer with
            | Some (Z3Syntax.Z3Errors es) -> ()
            | _ -> answer := Some Z3Syntax.Z3Unsat
          else if n >= 7 && String.sub l 0 7 = "unknown" then 
            match !answer with
            | Some (Z3Syntax.Z3Errors es) -> ()
            | _ -> answer := Some Z3Syntax.Z3Unknown
          else
            CoqInterface.error ("z3 failed with the error: " ^ l)
        done;
        !answer
      with End_of_file -> !answer
    in
    (* TODO confirm the exit codes *)
    if exit_code <> 0 then CoqInterface.warning "z3-non-zero-exit-code" ("Z3.verify: command " ^ command ^ " exited with code " ^ string_of_int exit_code);
    let answer = raise_warnings_errors () in 
    (*let res = import_trace ra_quant rf_quant logfilename (Some first) lsmt in*)
    close_in win; 
      (* Sys.remove wname; *)
    match answer with
      | Some r -> r
      | None -> CoqInterface.error ("z3 did not return a solution")

let get_hyp_pending (sigma: Evd.evar_map)
                     (e: Environ.env)                     
                     hyp : pending_def list =
  match hyp with
  | Context.Named.Declaration.LocalAssum (hname, hyp_econstr) ->
      pending_defs e sigma (EConstr.to_constr sigma hyp_econstr)
  | Context.Named.Declaration.LocalDef _ -> failwith "LocalDef in hyps"

let hyp_to_z3_assert (sigma: Evd.evar_map)
                     (e: Environ.env)                     
                     hyp : string =
  match hyp with
  | Context.Named.Declaration.LocalAssum (hname, hyp_econstr) ->
      let hyp_ty = EConstr.to_constr sigma (snd (Typing.type_of e sigma hyp_econstr)) in
      let hyp_constr = EConstr.to_constr sigma hyp_econstr in
      let name_str = Names.Id.to_string (Context.binder_name hname) in
      
      if Constr.is_Prop hyp_ty then
        "(assert " ^ constr_to_z3 hyp_constr e [] sigma ^ ")"
      
      else if Constr.is_Set hyp_constr || Constr.is_Type hyp_constr then
        "(declare-sort " ^ name_str ^ ")"

      else
        "(declare-const " ^ name_str ^ " " ^ constr_to_z3 hyp_constr e [] sigma  ^ ")" 
      
  | Context.Named.Declaration.LocalDef _ -> failwith "LocalDef in hyps"

let types_and_funcs () =
  "(declare-datatypes (T) (\n" ^
    "(Coq.Init.Datatypes.list \n" ^
	    "Coq.Init.Datatypes.list_c1 \n"  ^ 
	    "(Coq.Init.Datatypes.list_c2 \n" ^
            "(head T) \n" ^
            "(tail Coq.Init.Datatypes.list)\n" ^
       ")\n" ^
    ")\n" ^
"))"

let print_type () = 
  Proofview.Goal.enter (fun gl ->
    
    (* envienvironment with global definitions, etc. *)
    let env = Proofview.Goal.env gl in
    
    (* existential variables (evars) map *)
    let sigma = Tacmach.New.project gl in
    
    (* conclusion of the goal *)
    let t = Proofview.Goal.concl gl in
    
    (* convert from EConstr (with evars) to Constr (no evars) *)
    let t = EConstr.to_constr sigma t in (* The goal should not contain uninstanciated evars *)

    (* get hypothesis *)
    let hyps = Proofview.Goal.hyps gl in 
    let pending_hyps = List.concat_map (get_hyp_pending sigma env) hyps in
    let pend = define_pending env sigma (List.hd pending_hyps) in
    CoqInterface.warning "pending" ("There are " ^ string_of_int (List.length pending_hyps) ^ " pending defs") ;
    let goal_z3 = "(assert " ^ constr_to_z3 t env [] sigma ^ ")" in 
    let hyps_z3 = String.concat "\n" (List.map (hyp_to_z3_assert sigma env) (List.rev hyps)) in
    let script = types_and_funcs () ^"\n" ^ pend ^ "\n" ^ hyps_z3 ^ "\n" ^ goal_z3 in

    match call_z3 script with
    | Z3Syntax.Z3Unsat -> CoqInterface.warning "z3" "z3 returned unsat" ;  CoqInterface.tclIDTAC
    | Z3Syntax.Z3Sat -> CoqInterface.error ("z3 returned sat")
    | Z3Syntax.Z3Unknown -> CoqInterface.error ("z3 returned unknown")
    | Z3Syntax.Z3Errors l -> CoqInterface.error ("z3 returned errors:\n" ^ (String.concat "\n" l))

    (* failwith ("Conversion: " ^ constr_to_z3 t env [] ^ "\nHyps: " ^ show_hyps hyps ^ "env " ^ show_env env) *)
  )