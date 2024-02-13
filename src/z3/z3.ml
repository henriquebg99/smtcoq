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
                (s: Evd.evar_map) : Constr.types =
  EConstr.to_constr s (
    snd (Typing.type_of e s (EConstr.of_constr c)))

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
                      (s: Evd.evar_map) : 
                      (Constr.t list) = 
  let pred a = begin let ty = constr_type a e s in 
    Constr.isSort ty && (not (Constr.is_Prop ty)) end in
  let (_, r2) = split_while pred args in
  match List.find_opt pred r2 with
  | Some _ -> failwith "application of types (of non-polymorphic instantiation) not supported"
  | None -> r2
 
(* similiar to remove_initial but also removes Props and returns the also the removed*)
let split_inital_types (args: Constr.t list)
                     (e: Environ.env) 
                     (s: Evd.evar_map) : 
                     (Constr.t list) * (Constr.t list) = 
  let pred a = Constr.isSort (constr_type a e s) in 
  let (r1, r2) = split_while pred args in
  match List.find_opt pred r2 with
  | Some _ -> failwith "application of types (of non-polymorphic instantiation) not supported"
  | None -> (r1, r2)

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


let monomorphic_name (name: string) (tys: Constr.types list) : string =
  let rec ty_to_str_usc (t: Constr.t) : string = begin
    match Constr.kind t with
    | Constr.Ind ((n, _), _) -> Names.MutInd.to_string n
    | Constr.Var id -> Names.Id.to_string id
    | Constr.Const (n, _) -> Names.Constant.to_string n
    | Constr.App (f, args) -> ty_to_str_usc f ^ "_" ^ (String.concat "_" (List.map ty_to_str_usc (Array.to_list args))) 
    | Constr.Sort s -> begin match s with
        | Sorts.SProp -> "SProp"
        | Sorts.Prop -> "Prop"
        | Sorts.Set -> "Set"
        | Sorts.Type _ -> "Type"
        end
    | Constr.Prod _ -> failwith ("grounded types only instantiation of polymorphic type: " ^ c2str t)
    | _ -> failwith "not expected construct for instantiation of polymorphic type" 
  end in
  name ^ "_" ^ (String.concat "_" (List.map ty_to_str_usc tys))


let _constructor_name (e: Environ.env) (n: Names.inductive) (i: int) : string =
  let ind_info = snd (Inductive.lookup_mind_specif e n) in
  let name = (ind_info.Declarations.mind_consnames).(i) in
  Names.Id.to_string name

(* given a constr with with n nested lambdas as outer-most construction, 
   return its arguments types and names *)
let rec extract_lambdas_types (n: int) 
                              (c: Constr.t) : (Names.Name.t * Constr.types) list =
if n = 0 then []
else match Constr.kind c with 
  | Constr.Lambda (name, tn, t1) -> 
    (Context.binder_name name, tn) :: extract_lambdas_types (n - 1) t1
  | _ -> failwith "extract_lambdas_types: expected a lambda"


(* name of constant and list of types for monomorphization
   e.g. (app, [A]) -> get a version of app for A, called app_A *)
type pending_def = | Funct of (Names.Constant.t * (Constr.t list))
                   | Indct of Names.inductive

let rec pending_defs (s: Evd.evar_map)
                     (e: Environ.env) 
                     (c: Constr.t)  : pending_def list =
  match Constr.kind c with
  | Constr.App (f, arr) -> 
    let f_ty = constr_type f e s in
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
        else 
          begin match Constr.kind f with
          (* if f returns a type which is a Set, e.g. nat, list nat*)
          | Constr.Ind (iname, _) -> [Indct iname]
          | _ ->  
            let (tys, _) = split_inital_types args e s in 
            begin match Constr.kind f with
            | Constr.Const (name, _) -> [Funct (name, tys)]
            | _ -> pending_defs s e f
            end
          end
        end in f_pending @ List.concat_map (pending_defs s e) (Array.to_list arr)
  | Constr.Prod (_, t1, t2) ->
    (pending_defs s e t1) @ (pending_defs s e t2)
  | Constr.LetIn (_, t1, tn, t2) ->
    (pending_defs s e t1) @ (pending_defs s e t2) @ (pending_defs s e tn)
  | Constr.Lambda (_, tn, t1) ->
    (pending_defs s e t1) @ (pending_defs s e tn)
    | Constr.Case (_, _, _, scr, arr) -> 
      pending_defs s e scr @ List.concat_map (pending_defs s e) (Array.to_list arr)
  | _ -> []

let declare_var (e: Environ.env) (id: Names.Id.t) (t: Constr.types) : Environ.env =  
  let ba = { Context.binder_name = id
           ; Context.binder_relevance = Sorts.Relevant} in
  let la = Context.Named.Declaration.LocalAssum (ba, t) in
  Environ.push_named la e

let z3_name (s: string) : string =
  String.concat "_" (String.split_on_char '.' s)

let name_to_str (n: Names.Name.t) : string = 
  match n with
  | Names.Name.Name id -> Names.Id.to_string id
  | Names.Name.Anonymous -> "_"

let name_id_err (n: Names.Name.t) : Names.Id.t = 
  match n with
  | Names.Name.Name id -> id
  | Names.Name.Anonymous -> 
    failwith "wildcard in fixpoint params not supported"

type z3script = { sorts : string list 
                ; vars : string list
                ; asserts : string list
                ; funs : string list
                ; types : string list}

(* converts a constr to Z3 expression *)
let rec constr_to_z3 (c: Constr.t) 
                     (e: Environ.env) 
                     (s: Evd.evar_map) : string (* * (pending_def list) *)   =
  match Constr.kind c with
  (* TODO inspect App, to check if all cases are handled properly*)
  | Constr.App (f, arr) ->
      let f_ty = constr_type f e s in
      let f_ret_ty = return_type f_ty in
      let args = Array.to_list arr in
      (* if f return Prop (e.g. eq, and, or) *)
      if Constr.is_Prop f_ret_ty then 
        (* TODO support user defined propositions *)
        (* remove types e.g. eq nat n1 n2 -> eq n1 n2 *)
        let args_no_types = remove_initial_types_non_props args e s in
        begin match args_no_types with
        | [] -> constr_to_z3 f e s
        | _ :: _ -> 
            let args_str = String.concat " " 
              (List.map (fun c' -> constr_to_z3 c' e  s) args_no_types) in
            "(" ^ constr_to_z3 f e  s ^ " " ^ args_str ^ ")"
        end
      (* if it is an inductive and not of type prop, then it is a "computable" datatype
         so leave the types e.g. list nat - leave the nat *)
      else if Constr.isInd f then
        let args_str = String.concat " " 
          (List.map (fun c' -> constr_to_z3 c' e  s) args) in
            "(" ^ constr_to_z3 f e  s ^ " " ^ args_str ^ ")"
      (* if f returns a type which is a Set, e.g. nat, list nat*)
      else
        let (tys, args') = split_inital_types args e s in
        let f_str = begin match Constr.kind f with
                    | Constr.Const (name, _) -> 
                      z3_name (monomorphic_name (Names.Constant.to_string name) tys)
                    | _ -> constr_to_z3 f e  s
                    end in
        begin match args' with
        | [] -> f_str
        | _ :: _ -> 
            let args_str = String.concat " " 
              (List.map (fun c' -> constr_to_z3 c' e  s) args') in
            "(" ^ f_str ^ " " ^ args_str ^ ")"
        end
      
  | Constr.Prod (n, t1, t2) ->  
      begin match (Context.binder_name n) with
      (* the variable of forall is _, so treat as implication *)
      | Names.Name.Anonymous -> 
          "(implies " ^ constr_to_z3 t1 e  s ^ " " ^ constr_to_z3 t2 e  s ^ ")"
      (* the variable has a name *)
      | Names.Name.Name id ->
          (* z3 does not support quantification over props *)
          if Constr.is_Prop t1 
            then failwith "quantification over props is not supported"
            else 
              let name = Names.Id.to_string id in 
              let e' = declare_var e id t1 in
              let t1' = constr_to_z3 t1 e  s in
              let t2' = constr_to_z3 t2 e'  s in
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
              let t1' = constr_to_z3 t1 e  s in
              let t2' = constr_to_z3 t2 e'  s in
              "(let ((" ^ name ^ " " ^ t1' ^ ")) " ^ t2' ^ ")" 
      end
  | Constr.Lambda (n, tn, t1) ->
      let name, e' = match (Context.binder_name n) with
                  | Names.Name.Anonymous ->  "_", e
                  | Names.Name.Name id -> 
                    Names.Id.to_string id, declare_var e id tn in
      let tn' = constr_to_z3 tn e  s in
      let t1' = constr_to_z3 t1 e'  s in 
      "(lambda ((" ^ name ^ " " ^ tn' ^ ")) " ^ t1' ^ ")"
  | Constr.Var id -> Names.Id.to_string id (* TODO if it is not a function, get its definition and return *)
  | Constr.Ind ((mutind, _), univ) -> 
      let name_str =  z3_name (Names.MutInd.to_string mutind) in 
      Option.default name_str (M.find_opt name_str special_inductives)
  | Constr.Const (name, univ) -> 
      let name_str = z3_name (Names.Constant.to_string name) in
      begin match (Environ.lookup_constant name e).Declarations.const_body with
      | Declarations.Def d ->
          Option.default name_str (M.find_opt name_str special_funcs)
      | _ -> failwith ("definition for name " ^ name_str ^ " is not available")
      end
  | Constr.Construct (((mutind, _), index), univ) -> 
      (* TODO get name of constructor -> get the type, extract ind there *)
      z3_name (Names.MutInd.to_string mutind) ^ "_c" ^ string_of_int index
      (* let ty = constr_type c e s in
      let ind_name = fst (fst (Inductive.find_inductive e ty)) in
      constructor_name e ind_name index *)
(* TODO remove warnings *)
  | Constr.Case (ci, constr, inv, scr, arr) -> 
    let ind_info = snd (Inductive.lookup_mind_specif e (ci.Constr.ci_ind)) in
    let ind_name = Names.MutInd.to_string (fst ci.Constr.ci_ind) in
    let scr_str = constr_to_z3 scr e  s in 
    let branch_to_z3 (index: int) (body: Constr.t) : string =
      begin
        (* constructor arg count and name *)
        let args_count = (ind_info.Declarations.mind_consnrealargs).(index) in
        let c_name = z3_name ind_name ^ "_c" ^ string_of_int (index + 1) in
        (* get pattern variables and types *)
        let names_types = extract_lambdas_types args_count body in
        (* wildcards are not expected in lambdas that define branches *)
        let pat_vars_names = List.map (fun p -> name_to_str (fst p)) names_types in
        let pat_vars = List.map (fun p -> Constr.mkVar (name_id_err (fst p))) names_types in
        let pattern = if args_count = 0 
          then c_name
          else "(" ^ c_name ^ " " ^ String.concat " " pat_vars_names ^ ")"
          in
        let body_no_lams = Reduction.beta_applist body pat_vars in
        let e' = List.fold_right 
                  (fun (v, t) r -> 
                    let ba = { Context.binder_name = name_id_err v
                             ; Context.binder_relevance = Sorts.Relevant} in
                    let la = Context.Named.Declaration.LocalAssum (ba, t) in
                    Environ.push_named la r)
                  names_types e in
        let body_no_lams_str = constr_to_z3 body_no_lams e' s in
        "(" ^ pattern ^ " " ^ body_no_lams_str ^ ")"
      end
    in
    let brs_indices = List.init (Array.length arr) (fun x -> x) in
    let brs_strs = List.map (fun (a, b) -> branch_to_z3 a b) (List.combine brs_indices (Array.to_list arr)) in 
    "(match " ^ scr_str ^ " (" ^ String.concat "\n" brs_strs ^ "))"
  | Constr.Rel i -> 
    begin match Environ.lookup_rel i e with
    | Context.Rel.Declaration.LocalAssum (bind, _) ->
      Names.Id.to_string (name_id_err (Context.binder_name bind))
    | Context.Rel.Declaration.LocalDef _ -> 
      failwith "local definitions in rel"
    end
  | Constr.Fix _ -> failwith ("evaluation of apps of fixpoints not supported yet")
  | Constr.Sort _ -> "(sort)"
  | _ -> failwith "Conversion not supported"

(* TODO remove body from extract_... return type *)
(* given \x1:t1 -> ... \xn:tn -> b returns ([(x1, t1), ..., (xn, tn)], b) *)
let rec extract_lambdas_params (c: Constr.t) : ((Names.Name.t * Constr.types) list) * Constr.t =
  match Constr.kind c with (* TODO rule out dependent types, which cannot be enconded in Z3*)
  | Constr.Lambda (n, tn, t) -> 
    let n' = Context.binder_name n in
    let (l, b) = extract_lambdas_params t in ((n', tn) :: l, b)
  | _ -> ([], c)

(* returns a def-fun-rec for a pending definition *)
let define_func (s: Evd.evar_map)
                (e: Environ.env)
                (sct: z3script)
                (name: Names.Constant.t)
                (tys: Constr.t list) : z3script =
  match (Environ.lookup_constant name e).Declarations.const_body with
  | Declarations.Def d -> 
    (* typically, a fixpoint definition is fun (A: Type) fun (p1: ty1) ... fix recname fun(p_k+1: ty)... def*)
    (* instantiate polymorphic parameters *)
    let d = Mod_subst.force_constr d in
    let mono_def = if List.length tys = 0 then d
                   else Reduction.beta_applist d tys in
    let fun_name = z3_name (Names.Constant.to_string name) in 
    let mono_name = monomorphic_name fun_name tys in
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
      let (vars_types', body) = extract_lambdas_params body_fixvar_subst in
      let vars = List.map (fun vt -> Constr.mkVar (name_id_err (fst vt))) vars_types' in
      let e = List.fold_right 
                (fun (name, ty) r -> declare_var r (name_id_err name) ty)
                (vars_types' @ [((Names.Name.Name (Names.Id.of_string mono_name), types.(0)))])
                e in
      let body_applied = Reduction.beta_applist body_fixvar_subst vars in
      let bind_lst = List.map 
        (fun (v, t) -> "(" ^ Names.Id.to_string (name_id_err v) ^ " " ^ constr_to_z3 t e s ^ ")")
        (vars_types @ vars_types') in
      let binds_str = String.concat " " bind_lst in
      let com = "(define-fun-rec " ^ mono_name ^ " (" ^ binds_str ^ ") " ^ constr_to_z3 (return_type types.(0)) e s ^ " " ^ 
        constr_to_z3 body_applied e s ^ ")" in
      {sct with funs = sct.funs @ [com]}
    | _ -> failwith "error"
    end
  | _ -> failwith "error 2"

(* TODO should receive the mind_specif *)
let extract_signature (s: Evd.evar_map)
                      (e: Environ.env)
                      (ind_name: string)
                      (rc: Constr.rel_context)
                      (t: Constr.types) : string list =
  let ind_id = Names.Id.of_string ind_name in
  let fake_id = Names.Id.of_string "fake_var" in
  let fake_name = Names.Name.Name fake_id in
  let fake_bind = { Context.binder_name = fake_name
                  ; Context.binder_relevance = Sorts.Relevant} in
  let _fake_var = Constr.mkVar fake_id in
  let fake_ty = Constr.mkSet in
  let rec skip_poly_prods (t: Constr.types): Constr.types = begin
    match Constr.kind t with
    | Constr.Prod (n, u, t') 
      when Constr.is_Type u || Constr.is_Set u ->
        begin match Context.binder_name n with
        | Names.Name.Anonymous -> skip_poly_prods t'
        | Names.Name.Name id -> 
          let replaced = Reduction.beta_app 
            (Constr.mkLambda (fake_bind, fake_ty, t')) 
            (Constr.mkVar id) in
          skip_poly_prods replaced
        end
    | _ -> t
  end in
  let rec ty_to_str (t: Constr.t) : string = begin
    match Constr.kind t with
    | Constr.Ind ((n, _), _) -> Names.MutInd.to_string n
    | Constr.Var id -> Names.Id.to_string id
    | Constr.Const (n, _) -> Names.Constant.to_string n
    | Constr.App (f, args) -> "(" ^ ty_to_str f ^ " " ^ (String.concat " " (List.map ty_to_str (Array.to_list args))) ^ ")"
    | Constr.Sort s -> begin match s with
        | Sorts.SProp -> "SProp"
        | Sorts.Prop -> "Prop"
        | Sorts.Set -> "Set"
        | Sorts.Type _ -> "Type"
        end
    | Constr.Prod _ -> failwith ("grounded types only instantiation of polymorphic type: " ^ c2str t)
    | _ -> failwith "not expected construct for instantiation of polymorphic type" 
  end in
  let rec decomp_arr (t: Constr.types) : string list = begin
    match Constr.kind t with
    | Constr.Prod (n, t1, t2) ->
      (* arrow *)
      if Names.Name.is_anonymous (Context.binder_name n) then
        ty_to_str t1 :: decomp_arr t2
      else
        failwith ("While extracting inductive type " ^ ind_name ^ ": not expected dependent type in constructor")
    | _ -> [ty_to_str t]
  end in 
  (* the type of a constructor has a free rel that represents the 
     recursive inductive type *)
  let ind_var = Constr.mkVar ind_id in
  let skipped = skip_poly_prods t in
  let t_replaced_ind_rel = 
    (* TODO use Environ.push_rel_context to avoid reducing lambdas;
       in the case of ind list, it has A *)
    Reduction.beta_app
      (Constr.mkLambda (fake_bind, fake_ty, skipped))
      ind_var in
  decomp_arr t_replaced_ind_rel

let define_ind (s: Evd.evar_map)
               (e: Environ.env)
               (sct: z3script)
               (name: Names.inductive) : z3script =
  let info = snd (Inductive.lookup_mind_specif e name) in
  let rc = info.Declarations.mind_arity_ctxt in
  let name_str = z3_name (Names.MutInd.to_string (fst name)) in
  let ncons = Array.length info.Declarations.mind_consnames in
  let construct_str (i: int) = begin
    let c_arity = info.Declarations.mind_consnrealargs.(i) in
    (* TODO remove variable c_name_str or change to constructors names *)
    let _c_name_str = Names.Id.to_string (info.Declarations.mind_consnames.(i)) in 
    if c_arity = 0 then
      Printf.sprintf "%s_c%d" name_str (i+1)
    else
      let ty = info.Declarations.mind_user_lc.(i) in
      let _ty2 = snd (info.Declarations.mind_nf_lc.(i)) in
      let _relc = fst (info.Declarations.mind_nf_lc.(i)) in
      let params = extract_signature s e name_str rc ty in
      (* that last element is the return type*)
      let params_inds = List.init (List.length params - 1) (fun x -> x) in
      let params_strs = List.map 
        (fun i' -> Printf.sprintf "(%s_c%d_s%d %s)" name_str (i+1) (i'+1) (List.nth params i'))
        params_inds in
      Printf.sprintf "(%s_c%d %s)" name_str (i+1) (String.concat " " params_strs)
  end in 
  let constrs_strs = List.map construct_str (List.init ncons (fun x -> x)) in
  let polys_names = List.map (fun x -> Names.Id.to_string (name_id_err (Context.Rel.Declaration.get_name x))) rc in
  let pars = String.concat " " polys_names in
  let com = Printf.sprintf "(declare-datatype %s (par (%s) (%s)))" 
    name_str pars (String.concat " " constrs_strs) in
  {sct with types = sct.types @ [com]}

let define_pending (s: Evd.evar_map)
                   (e: Environ.env)
                   (sct: z3script)
                   (p: pending_def) : z3script =
  match p with
  | Funct (name, tys) -> define_func s e sct name tys
  | Indct name -> define_ind s e sct name


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

let get_hyp_pending  (s: Evd.evar_map)
                     (e: Environ.env)                     
                     hyp : pending_def list =
  match hyp with
  | Context.Named.Declaration.LocalAssum (hname, hyp_econstr) ->
      pending_defs s e (EConstr.to_constr s hyp_econstr)
  | Context.Named.Declaration.LocalDef _ -> failwith "LocalDef in hyps"


let hyp_to_z3_assert (s: Evd.evar_map)
                     (e: Environ.env)
                     (sct: z3script)
                     hyp : z3script =
  match hyp with
  | Context.Named.Declaration.LocalAssum (hname, hyp_econstr) ->
      let hyp_ty = EConstr.to_constr s (snd (Typing.type_of e s hyp_econstr)) in
      let hyp_constr = EConstr.to_constr s hyp_econstr in
      let name_str = Names.Id.to_string (Context.binder_name hname) in
      
      if Constr.is_Prop hyp_ty then
        let com = "(assert " ^ constr_to_z3 hyp_constr e  s ^ ")" in
        {sct with asserts = sct.asserts @ [com]}
      
      else if Constr.is_Set hyp_constr || Constr.is_Type hyp_constr then
        let com = "(declare-sort " ^ name_str ^ ")" in
        {sct with sorts = sct.sorts @ [com]}

      else
        let com = "(declare-const " ^ name_str ^ " " ^ constr_to_z3 hyp_constr e  s  ^ ")" in
        {sct with vars = sct.vars @ [com]}
      
  | Context.Named.Declaration.LocalDef _ -> failwith "LocalDef in hyps"

let goal_to_z3_assert (s: Evd.evar_map)
                      (e: Environ.env)
                      (sct: z3script)
                      (c: Constr.t) : z3script =
  let com = "(assert (not " ^ constr_to_z3 c e s ^ "))" in 
  {sct with asserts = sct.asserts @ [com]}

module StringSet = Set.Make(String)

let script_str (s: z3script) : string =
  let dedup (l: string list) : string list = begin 
    StringSet.elements (StringSet.of_list l)
  end in
  (* sorts >> funs >> vars >> asserts *)  
  let sorts = String.concat "\n" (dedup s.sorts) in
  let funs = String.concat "\n" (dedup s.funs) in
  let vars = String.concat "\n" (dedup s.vars) in
  let asserts = String.concat "\n" (dedup s.asserts) in
  let types = String.concat "\n" (dedup s.types) in
  Printf.sprintf "%s\n%s\n%s\n%s\n%s\n(check-sat)" types sorts funs vars asserts 

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

    (* TODO define interleave pending funs and hyps *)
    (* get hypothesis *)
    let hyps = Proofview.Goal.hyps gl in 
    let pending_funs = List.concat_map (get_hyp_pending sigma env) hyps @ pending_defs sigma env t in
    
    let script : z3script = {asserts = []; vars = []; sorts = []; funs = []; types = []} in
    let script = List.fold_right (fun c r -> hyp_to_z3_assert sigma env r c) (List.rev hyps) script in
    let script = goal_to_z3_assert sigma env script t in
    let script = List.fold_right (fun c r -> define_pending sigma env r c) pending_funs script in

    match call_z3 (script_str script) with
    | Z3Syntax.Z3Unsat -> CoqInterface.warning "z3" "z3 returned unsat" ;  CoqInterface.tclIDTAC
    | Z3Syntax.Z3Sat -> CoqInterface.error ("z3 returned sat")
    | Z3Syntax.Z3Unknown -> CoqInterface.error ("z3 returned unknown")
    | Z3Syntax.Z3Errors l -> CoqInterface.error ("z3 returned errors:\n" ^ (String.concat "\n" l))

    (* failwith ("Conversion: " ^ constr_to_z3 t env [] ^ "\nHyps: " ^ show_hyps hyps ^ "env " ^ show_env env) *)
  )