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

let show_hyps (hyps: EConstr.named_context) : string =
  "there are " ^ string_of_int (List.length hyps) ^ " hyps"

let show_env (env: Environ.env) : string = ""

(* converts a constr to Z3 expression 
   * rels is the list of names of variables to replace de Brujin indices 
   * a name in position i - 1 should replace (Constr.Rel i)*)
let rec constr_to_z3 (c: Constr.t) (e: Environ.env) (rels: string list) : string =
  match Constr.kind c with
  | Constr.App (c, arr) -> 
      let args_str = Array.fold_right (fun c r -> constr_to_z3 c e rels ^ " " ^ r) arr "" in
      "(" ^ constr_to_z3 c e rels ^ " " ^ args_str ^ ")"
  | Constr.Prod (n, t1, t2) ->  
      begin match (Context.binder_name n) with
      (* the variable of forall is _, so treat as implication *)
      | Names.Name.Anonymous -> 
          "(implies " ^ constr_to_z3 t1 e rels ^ " " ^ constr_to_z3 t2 e rels ^ ")"
      (* the variable has a name *)
      | Names.Name.Name id ->
          (* z3 does not support quantification over props *)
          if Constr.is_Prop t1 
            then failwith "quantification over props is not supported"
            else 
              let name = Names.Id.to_string id in 
              let t1' = constr_to_z3 t1 e rels in
              let t2' = constr_to_z3 t2 e (name :: rels) in
              "(forall ((" ^ name ^ " " ^ t1' ^ ")) " ^ t2' ^ ")"
      end
  | Constr.LetIn (n, t1, _, t2) ->
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
              let t1' = constr_to_z3 t1 e rels in
              let t2' = constr_to_z3 t2 e (name :: rels) in
              "(let ((" ^ name ^ " " ^ t1' ^ ")) " ^ t2' ^ ")" 
      end
  | Constr.Lambda (n, tn, t1) ->
      begin match (Context.binder_name n) with
      | Names.Name.Anonymous -> 
          let name = "_" in
          let tn' = constr_to_z3 tn e rels in
          let t1' = constr_to_z3 t1 e (name :: rels) in 
          "(lambda ((" ^ name ^ " " ^ tn' ^ ")) " ^ t1' ^ ")"
      | Names.Name.Name id ->
          let name = Names.Id.to_string id in
          let tn' = constr_to_z3 tn e rels in
          let t1' = constr_to_z3 t1 e (name :: rels) in 
          "(lambda ((" ^ name ^ " " ^ tn' ^ ")) " ^ t1' ^ ")"
      end
  | Constr.Var id -> Names.Id.to_string id
  | Constr.Ind ((mutind, _), univ) -> Names.MutInd.to_string mutind
  | Constr.Const (name, univ) -> 
      begin match (Environ.lookup_constant name e).Declarations.const_body with
      | Declarations.Def d -> Names.Constant.to_string name
      | _ -> failwith ("definition for name " ^ Names.Constant.to_string name ^ " is not available")
      end
  | Constr.Construct (((mutind, _), index), univ) -> 
      Names.MutInd.to_string mutind ^ "_c" ^ string_of_int index
  | Constr.Case (ci, constr, inv, constr2, arr) -> 
    let branch_str = Array.fold_right (fun c r -> constr_to_z3 c e rels ^ " ;; " ^ r) arr "" in
      "(match " ^ constr_to_z3 constr2 e rels ^  "with" ^ branch_str ^ ")"
  | Constr.Rel i -> List.nth rels (i - 1)
  | Constr.Fix _ -> "(fix)"
  | _ -> "(ERROR)"

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

    failwith ("Conversion: " ^ constr_to_z3 t env [] ^ "\nHyps: " ^ show_hyps hyps ^ "env " ^ show_env env)
  )