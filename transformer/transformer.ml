open Calli

module CCM = Fla_analyzer.CCM
module CTG = Fla_analyzer.CTG

let llctx, llmem, llm = 
  let llctx = Llvm.global_context () in
  let llmem = Llvm.MemoryBuffer.of_file Sys.argv.(1) in
  let llm = Llvm_bitreader.parse_bitcode llctx llmem in
  llctx, llmem, llm

let ctg = ref CTG.CTG.empty

let ccm, ctg = 
  let _ = Fla_analyzer.analyze () in
  let _ = Fla_analyzer.CCM.pp' () in
  let _ = Fla_analyzer.CTG.pp () in
  let ccm = !Fla_analyzer.CCM.ccm' in
  let _ = ctg := !Fla_analyzer.CTG.ctg in
  ccm, !ctg


module Visit = Set.Make(struct type t = FlaCtxt2.t let compare = compare end)
let visit = ref Visit.empty

module Visit2 = Set.Make(struct type t = (FlaCtxt2.t * string) let compare = compare end)
let visit2 = ref Visit2.empty

module BBName = Map.Make(struct type t = (FlaCtxt2.t * string) let compare = compare end)
let bbname = ref BBName.empty

module BBCtxt = Map.Make(struct type t = Llvm.llbasicblock let compare = compare end)
let bb_ctxt : FlaCtxt2.t BBCtxt.t ref = ref BBCtxt.empty

module BBMap = Map.Make(struct type t = Llvm.llbasicblock let compare = compare end)
let bb_map  = ref BBMap.empty


module BBSet = Set.Make(struct type t = (FlaCtxt2.t * string) let compare = compare end)
module Pred = Map.Make(struct type t = (FlaCtxt2.t * string) let compare = compare end)
module Next = Map.Make(struct type t = (FlaCtxt2.t * string) let compare = compare end)
let pred = ref Pred.empty
let next = ref Next.empty

let get_empty_ctxt () = 
  FlaCtxt2.empty ()


let find_bb bb_name basicblocks = 
  let basicblocks = Array.to_list basicblocks in
  let bb = List.find 
    (fun bb -> 
     (Util.get_bbname (Llvm.value_of_block bb)) = bb_name)
    basicblocks
  in 
  bb  

let find_bb_opt bb_name basicblocks = 
  let basicblocks = Array.to_list basicblocks in
  let bb = List.find_opt
    (fun bb -> 
      (Llvm.value_name (Llvm.value_of_block bb)) = bb_name)
    basicblocks
  in 
  bb  

let get_entry ctxt = 
  let subcfg = CCM.find' ctxt !CCM.ccm' in
  let entry = Cfg.entry subcfg in
  BBName.find (ctxt, entry) !bbname


let exit = ref ""

let get_exit ctxt = 
  let _ = exit := "" in
  let subcfg = CCM.find' ctxt !CCM.ccm' in
  let entry = Cfg.entry subcfg in
  let _ = Cfg.iter_cfg (fun bb_name -> if Cfg.find bb_name subcfg = [] then let _ = exit := bb_name in () else ()) entry subcfg in 
  BBName.find (ctxt, !exit) !bbname




module Def = Set.Make(struct type t = Llvm.llvalue 
    let compare (v1 : t) (v2 : t) =
    if v1 == v2 then 0 else
      (* 포인터 비교 대신 임의의 순서 필요: 주소 캐스팅 또는 해시 등 *)
      Stdlib.compare (Obj.magic v1 : int) (Obj.magic v2 : int)
    end)
module Phi = Map.Make(struct type t = (Llvm.llvalue * BBMap.key) list  let compare=compare end)
let phi_map = ref Phi.empty

module InMap = Map.Make(struct type t = (FlaCtxt2.t * string) let compare = compare end)
let in_map = ref InMap.empty
module OutMap = Map.Make(struct type t = (FlaCtxt2.t * string) let compare = compare end)
let out_map = ref OutMap.empty

module GenMap = Map.Make(struct type t = (FlaCtxt2.t * string) let compare = compare end)
let gen_map = ref GenMap.empty
module KillMap = Map.Make(struct type t = (FlaCtxt2.t * string) let compare = compare end)
let kill_map = ref KillMap.empty

module AllDef = Map.Make(struct type t = Llvm.llvalue let compare = compare end)
module Defs = Map.Make(struct type t = (FlaCtxt2.t * string) let compare = compare end)
let defs = ref Defs.empty
let all_defs = ref AllDef.empty

module NewI = Map.Make(struct type t = (FlaCtxt2.t * string * Llvm.llvalue) let compare = compare end)
module OrigI = Map.Make(struct type t = (Llvm.llvalue) let compare = compare end)

let newI = ref NewI.empty
let origI = ref OrigI.empty

let clone_bb bb bb_name builder ctxt =
  let def = Llvm.fold_left_instrs
    (fun def i -> 
      let new_i = Llvm.instr_clone i in
      let num_operands = Llvm.num_operands new_i in
      let _ = Llvm.insert_into_builder new_i "" builder in
      (* basicblock * 기존 instruction -> 새로운 instruction *)
      let _ = newI := NewI.add (ctxt, bb_name, i) new_i !newI in
      let _ = origI := OrigI.add new_i i !origI in
      (* def 수집 *)
      let def  = (match Llvm.instr_opcode i with
        | Add 
        | FAdd
        | Sub
        | FSub
        | Mul
        | FMul
        | UDiv
        | SDiv
        | FDiv
        | URem
        | SRem
        | FRem
        | Shl 
  | LShr
  | AShr
  | And
  | Or
  | Xor

  | Alloca 
  | Load  | GetElementPtr
  | Trunc 
  | ZExt
  | SExt
  | FPToUI
  | FPToSI
  | UIToFP
  | SIToFP
  | FPTrunc
  | FPExt
  | PtrToInt
  | IntToPtr
  | BitCast

  | ICmp
  | FCmp
  | PHI
  | Call  | Select
 | ExtractElement
  | InsertElement  | ShuffleVector
  | ExtractValue
  | InsertValue -> 
      let def = Def.add new_i def in
      let def_set = 
        (match AllDef.find_opt i !all_defs with
        | Some s -> s
        | None -> Def.empty) in 
      let _ = all_defs := AllDef.add i (Def.add new_i def_set) !all_defs in
      def
  | _ -> def 
  ) in
      def
    )      
    Def.empty bb
  in
  let _ = gen_map := GenMap.add (ctxt, bb_name) def !gen_map in
  let _ = defs := Defs.add (ctxt, bb_name) def !defs in
  ()

let rec add_block ctxt (bb_name:string) f basicblocks =
  if Visit2.mem (ctxt, bb_name) !visit2 then ()
  else 
  let _ = visit2 := Visit2.add (ctxt, bb_name) !visit2 in
  let ctxt_str = Format.asprintf "%a" FlaCtxt2.pp ctxt in
  let new_bb = Llvm.append_block llctx (ctxt_str^bb_name) f in
  let _ = bbname := BBName.add (ctxt, bb_name) new_bb !bbname in
  let _ = bb_ctxt := BBCtxt.add new_bb ctxt !bb_ctxt in
  let builder = Llvm.builder_at_end llctx new_bb in
  let bb = find_bb bb_name basicblocks in
  let _ = clone_bb bb bb_name builder ctxt in
  let _ = bb_map := BBMap.add new_bb bb !bb_map in
  let term = (match Llvm.block_terminator bb with | Some t ->t | _ -> failwith "") in
  let _ = (match Llvm.instr_opcode term with 
    | Switch ->
      (match Fla_analyzer.CTG.find_opt ctxt ctg with
      | Some s -> 
        Fla_analyzer.CTG.CtxtSet.iter
        (fun ctxt' -> 
          let subcfg' = CCM.find' ctxt' !CCM.ccm' in
          let entry = Cfg.entry subcfg' in
          let next_set = (match Next.find_opt (ctxt, bb_name) !next with
            | Some s -> s
            | None -> BBSet.empty)
          in
          let next_set = BBSet.add (ctxt', entry) next_set in
          let _ = next := Next.add (ctxt, bb_name) next_set !next in 
          let pred_set = (match Pred.find_opt (ctxt', entry) !pred with
            | Some s -> s
            | None -> BBSet.empty)
          in
          let pred_set = BBSet.add (ctxt, bb_name) pred_set in
          let _ = pred := Pred.add (ctxt', entry) pred_set !pred in 
          add_block ctxt' entry f basicblocks
        ) s
      | None -> failwith "err1"
      )
    | Unreachable
    | Ret -> 
          let next_set = BBSet.empty in
          let _ = next := Next.add (ctxt, bb_name) next_set !next in ()
    | _ -> 
      let subcfg = CCM.find' ctxt !CCM.ccm' in
      let succs = Cfg.find bb_name subcfg in
      List.iter (fun succ -> 
          let next_set = (match Next.find_opt (ctxt, bb_name) !next with
            | Some s -> s
            | None -> BBSet.empty)
          in
          let next_set = BBSet.add (ctxt, succ) next_set in
          let _ = next := Next.add (ctxt, bb_name) next_set !next in 
          let pred_set = (match Pred.find_opt (ctxt, succ) !pred with
            | Some s -> s
            | None -> BBSet.empty)
          in
          let pred_set = BBSet.add (ctxt, bb_name) pred_set in
          let _ = pred := Pred.add (ctxt, succ) pred_set !pred in 
        add_block ctxt succ f basicblocks)
      succs
  )
  in ()

let rec make_gen_kill ctxt (bb_name:string) =
  if Visit2.mem (ctxt, bb_name) !visit2 then ()
  else 
  let _ = visit2 := Visit2.add (ctxt, bb_name) !visit2 in
  let ctxt_str = Format.asprintf "%a" FlaCtxt2.pp ctxt in
  let new_bb_name = (ctxt_str^bb_name) in
  let gen = GenMap.find (ctxt, bb_name) !gen_map in
  let kill = 
    Def.fold (fun new_i kill -> 
      let orig_i = OrigI.find new_i !origI in
      let all_defs = AllDef.find orig_i !all_defs in
      let kill' = Def.remove new_i all_defs in
      let kill = Def.union kill' kill in
      kill 
    ) gen Def.empty
  in
  let _ = kill_map := KillMap.add (ctxt, bb_name) kill !kill_map in
  let next_set = Next.find (ctxt, bb_name) !next in
  let _ = 
    BBSet.iter (fun (ctxt', bb_name') -> 
      make_gen_kill ctxt' bb_name' 
    ) next_set in
  ()


let rec make_in_out_init ctxt (bb_name:string) =
  if Visit2.mem (ctxt, bb_name) !visit2 then ()
  else 
  let _ = visit2 := Visit2.add (ctxt, bb_name) !visit2 in
  
  let _ = in_map := InMap.add (ctxt, bb_name) Def.empty !in_map in 
  let _ = out_map := OutMap.add (ctxt, bb_name) (GenMap.find (ctxt, bb_name) !gen_map) !out_map in

  let next_set = Next.find (ctxt, bb_name) !next in
  let _ = 
    BBSet.iter (fun (ctxt', bb_name') -> 
      make_in_out_init ctxt' bb_name' 
    ) next_set in
  ()


let flag = ref 0


let rec make_in_out ctxt (bb_name:string) =
  if Visit2.mem (ctxt, bb_name) !visit2 then ()
  else 
  let _ = visit2 := Visit2.add (ctxt, bb_name) !visit2 in
  
  let pred_set = match Pred.find_opt (ctxt, bb_name) !pred with
    | Some s -> s 
    | None -> BBSet.empty
  in
  
  let in_prev = InMap.find (ctxt, bb_name) !in_map in
  
  let in' = BBSet.fold (fun (ctxt', bb_name') in' ->
    let out_p = OutMap.find (ctxt', bb_name') !out_map in
    let in' = Def.union in' out_p in
    in'
    ) pred_set Def.empty
  in

  let out_prev = OutMap.find (ctxt, bb_name) !out_map in

  let gen = GenMap.find (ctxt, bb_name) !gen_map in
  let kill = KillMap.find (ctxt, bb_name) !kill_map in
  let set' = Def.diff in' kill in
  let out = Def.union gen set' in
  
  let _ =
    if not (Def.equal out_prev out) then
      flag := !flag + 1
  in
  
  let _ =
    if not (Def.equal in_prev in') then
      flag := !flag + 1
  in

  let _ = in_map := InMap.add (ctxt, bb_name) in' !in_map in
  let _ = out_map := OutMap.add (ctxt, bb_name) out !out_map in

  let next_set = Next.find (ctxt, bb_name) !next in
  let _ = 
    BBSet.iter (fun (ctxt', bb_name') -> 
      make_in_out ctxt' bb_name' 
    ) next_set in
  ()


let rec make_in_out_fixpoint empty_ctxt entry =
  
  let _ = visit2 := Visit2.empty in
  let _ = make_in_out_init empty_ctxt entry in
  
  let _ = visit2 := Visit2.empty in
  let _ = make_in_out empty_ctxt entry in

  while !flag != 0 do 
    let _ = flag := 0 in 
    let _ = visit2 := Visit2.empty in
    let _ = make_in_out empty_ctxt entry in
    ()
  done

let rec find_phi_loc (ctxt, bb_name) = 
  let preds = match Pred.find_opt (ctxt, bb_name) !pred with
    | Some s -> s  
    | None -> BBSet.empty
  in
  match BBSet.cardinal preds with
  | 1 -> find_phi_loc (BBSet.min_elt preds) 
  | _ -> (ctxt, bb_name)
  


let rec set_use ctxt (bb_name:string) =
  if Visit2.mem (ctxt, bb_name) !visit2 then ()
  else 
  let _ = visit2 := Visit2.add (ctxt, bb_name) !visit2 in
  
  let new_bb = BBName.find (ctxt, bb_name) !bbname in
  

  let in' = InMap.find (ctxt, bb_name) !in_map in

  let _ = Llvm.fold_left_instrs 
    (fun local_defs new_i ->
      let orig_i = OrigI.find new_i !origI in
      let num_operands = if Llvm.instr_opcode new_i = Switch then 1 else Llvm.num_operands new_i in
      match Llvm.instr_opcode new_i with
      | Alloca ->  (orig_i, new_i)::local_defs
      | _ -> 
      let _ =  for n = 0 to num_operands do
          let operand = Llvm.operand new_i n in
          (match List.find_opt (fun (orig_i', new_i') -> orig_i' = operand) local_defs with
           | Some (orig_i', new_i') -> 
             Llvm.set_operand new_i n new_i'
           | None ->
          let all_defs = 
            (match AllDef.find_opt (Llvm.operand new_i n) !all_defs with
            | Some s -> s
            | None -> Def.empty 
            )
          in
          let defs = 
            Def.filter (fun new_use -> 
              Def.mem new_use in'
            ) all_defs
          in
          (match Def.cardinal defs with
          | 0 -> ()
          | 1 ->
            Llvm.set_operand new_i n (Def.min_elt defs) 
          | n' ->
            
            if Llvm.is_constant operand || Llvm.value_is_block operand then () else
            let entry = get_entry ctxt in
            let phi_loc = find_phi_loc (ctxt, bb_name) in
            let phi_block = BBName.find phi_loc !bbname in
            let block_begin = Llvm.instr_begin phi_block in
            let phi_builder = Llvm.builder_at llctx block_begin in
            let pred_set = match Pred.find_opt phi_loc !pred with
              | Some s -> s 
              | None -> failwith "phi error 1"
            in
            let phi_lst = List.map
              (fun def ->
                let pred = List.find (fun pred -> 
                  let f, s = pred in
                  let out = OutMap.find pred !out_map in
                  Def.mem def out
                  ) (BBSet.elements pred_set) in
                let pred = BBName.find pred !bbname in
                (def, pred)
              ) (Def.elements defs)
            in
            let phi = Llvm.build_phi phi_lst "" phi_builder in
            let _ = Llvm.set_operand new_i n phi in 
            let _ = phi_map := Phi.add phi_lst phi !phi_map in
            ()
          )
          )
      done in
      let local_defs = (orig_i, new_i)::local_defs in local_defs
    ) [] new_bb
  in

  
  let next_set = Next.find (ctxt, bb_name) !next in
  let _ = 
    BBSet.iter (fun (ctxt', bb_name') -> 
      set_use ctxt' bb_name' 
    ) next_set 
  in
  ()

(*
let rec set_use' ctxt (bb_name:string) =
  if Visit2.mem (ctxt, bb_name) !visit2 then ()
  else 
  let _ = visit2 := Visit2.add (ctxt, bb_name) !visit2 in
  
  let new_bb = BBName.find (ctxt, bb_name) !bbname in

  let _ = Llvm.iter_instrs 
    (fun new_i ->
      let orig_i = OrigI.find new_i !origI in
      Llvm.replace_all_uses_with i orig_i
    ) new_bb
  in



  let next_set = Next.find (ctxt, bb_name) !next in
  let _ = 
    BBSet.iter (fun (ctxt', bb_name') -> 
      set_use' ctxt' bb_name' 
    ) next_set 
  in
  ()
*)


(*
let local_ctxt_operands bb ctxt =
  let _ = Llvm.iter_instrs 
    (fun i -> 
      let new_i = NMap.find (ctxt, bb, i) !nmap in
      let num_operands = Llvm.num_operands new_i in
      let block_begin = Llvm.instr_begin (Llvm.instr_parent new_i) in
      let builder = Llvm.builder_at llctx block_begin in
      let _ = 
        for n = 0 to num_operands do
            match NMap.find_opt (ctxt, bb, Llvm.operand i n) !nmap with
 
*)
module Condition = Map.Make(struct type t = FlaCtxt2.t let compare = compare end)
let condition = ref Condition.empty

let rec collect_condition ctxt f basicblocks = 
  let _ = visit := Visit.add ctxt !visit in
  let entry = get_exit ctxt in 
  let term = (match Llvm.block_terminator entry with | Some t ->t | _ -> failwith "") in
  let _ = (match Llvm.instr_opcode term with 
    | Switch -> 
      let cond_v = Llvm.instr_clone (Llvm.operand term 0) in 
      let _ = condition := Condition.add ctxt (Llvm.instr_clone term) !condition in ()
    | Br when (Llvm.is_conditional term) -> 
      let cond_v = Llvm.instr_clone (Llvm.operand term 0) in 
      let _ = condition := Condition.add ctxt (Llvm.instr_clone term) !condition in ()
    | _ -> ()) in
  let _ = 
    (match Fla_analyzer.CTG.find_opt ctxt ctg with
    | Some s -> 
      let _ = Fla_analyzer.CTG.CtxtSet.iter
        (fun ctxt' -> 
          if Visit.mem ctxt' !visit then ()
          else collect_condition ctxt' f basicblocks) s in
      ()
    | None -> ()) in () 

let rec set_terms ctxt f basicblocks = 
  let _ = visit := Visit.add ctxt !visit in
  let ctxt_str = Format.asprintf "%a" FlaCtxt2.pp ctxt in
  let sub_cfg : Cfg.t = CCM.find' ctxt !CCM.ccm' in
  let entry = Cfg.entry sub_cfg in
  let _ = Cfg.iter
    (fun bb_name succs -> 
      let cloned_bb = BBName.find (ctxt, bb_name) !bbname in
      let term = 
        match Llvm.block_terminator cloned_bb with
        | Some t -> t
        | None -> failwith "no terminator"
      in
      let builder = Llvm.builder_at_end llctx cloned_bb in
      let _ = (match List.length succs with
        (* zero successor in sub_cfg.
         A terminator is if or switch instruction.
         setting the terminator to be connected entrys in other contexts *)
        | 0 -> let _ = (match Llvm.instr_opcode term with
          | Ret -> ()
          (*condbr*)
(*          | Br -> 
            let s = 
              (match CTG.find_opt ctxt ctg with 
              | Some s -> s
              | None -> CTG.CtxtSet.empty)
            in
            let next_ctxts = CTG.CtxtSet.elements s in
            let _ = (match List.length next_ctxts with
            | 0 -> 
              let unreach = Llvm.insert_block llctx "" cloned_bb in
              let unreach_builder = Llvm.builder_at_end llctx unreach in
              let unreachable = Llvm.build_unreachable unreach_builder in
              let _ = Llvm.build_br unreach builder in
              let _ = Llvm.delete_instruction term in ()
            | 1 -> 
              let succ0 = get_entry (List.nth next_ctxts 0) in
              let _ = Llvm.build_br succ0 builder in
              let _ = Llvm.delete_instruction term in () 
            | 2 ->  
              let succ0 = 
                if FlaCtxt2.get_tf (List.nth next_ctxts 0) then
                  get_entry (List.nth next_ctxts 0) 
                else get_entry (List.nth next_ctxts 1) in
              let succ1 = 
                if FlaCtxt2.get_tf (List.nth next_ctxts 0) then
                  get_entry (List.nth next_ctxts 1) 
                else get_entry (List.nth next_ctxts 0) in
              let term' = Condition.find ctxt !condition in 
              let cond_v = Llvm.operand term' 0 in 
              let _ = Llvm.build_cond_br cond_v succ0 succ1 builder in
              let _ = Llvm.delete_instruction term in () 
            | n -> failwith "unreachable1") in ()
  *)          
          | Switch -> 
            let s = CTG.find ctxt ctg in
            let next_ctxts = CTG.CtxtSet.elements s in
            let _ = (match List.length next_ctxts with
            | 0 -> failwith "found no next context"
            | 1 -> 
              let succ0 = get_entry (List.nth next_ctxts 0) in
              let _ = Llvm.build_br succ0 builder in
              let _ = Llvm.delete_instruction term in () 
            | 2 ->  
              let succ0 = get_entry (List.nth next_ctxts 0) in
              let succ1 = get_entry (List.nth next_ctxts 1) in
              let term' = Condition.find ctxt !condition in 
              let cond_v = Llvm.operand term' 0 in 
              (*let _ = Llvm.insert_into_builder new_cond "" builder in*)
              let ty = Llvm.type_of cond_v in
              let cond_value = Llvm.const_int ty (FlaCtxt2.get_value (List.nth next_ctxts 0)) in
              let icmp = Llvm.build_icmp Eq cond_v cond_value "" builder in
              let _ = Llvm.build_cond_br icmp succ0 succ1 builder in
              let _ = Llvm.delete_instruction term in () 
            | n -> 
              let default_succ, next_ctxts  = 
                let default_opt = List.find_opt (fun c -> FlaCtxt2.is_default c) next_ctxts in 
                (match default_opt with
                | Some c -> (get_entry c, List.filter (fun c' -> c != c') next_ctxts)
                | None -> (get_entry (List.hd next_ctxts), List.tl next_ctxts))
              in
              let term' = Condition.find ctxt !condition in
              let cond_v = Llvm.operand term' 0 in
              let switch = Llvm.build_switch cond_v default_succ (n-1) builder in
              let _ = List.iter 
                (fun ctxt -> 
                  let succ = get_entry ctxt in
                  let ty = Llvm.type_of cond_v in
                  let cond_value = Llvm.const_int ty (FlaCtxt2.get_value ctxt) in
                  Llvm.add_case switch cond_value succ) 
                next_ctxts
              in
              let _ = Llvm.delete_instruction term in ()) in ()
          | _ -> ()) in ()
        (* connecting successor in subcfg *)
        | 1 -> 
          let succ = BBName.find (ctxt, (List.nth succs 0)) !bbname in
          let _ = Llvm.build_br succ builder in 
          let _ = Llvm.delete_instruction term in () 
        | 2 -> 
           let cond_v = Llvm.operand term 0 in
           let succ0 = BBName.find (ctxt, (List.nth succs 0)) !bbname in
           let succ1 = BBName.find (ctxt, (List.nth succs 1)) !bbname in
           let _ = Llvm.build_cond_br cond_v succ0 succ1 builder in
           let _ = Llvm.delete_instruction term in () 
        | n -> failwith "unreachablei3"
        ) in ()
    ) sub_cfg in
  let _ = 
    (match Fla_analyzer.CTG.find_opt ctxt ctg with
    | Some s -> 
      let _ = Fla_analyzer.CTG.CtxtSet.iter
        (fun ctxt' -> 
          if Visit.mem ctxt' !visit then ()
          else set_terms ctxt' f basicblocks) s in
      ()
    | None -> ()) in () 
  

let transform f = 
  let basicblocks = Llvm.basic_blocks f in
  let empty_ctxt = get_empty_ctxt () in
  let subcfg = CCM.find' empty_ctxt !CCM.ccm' in
  let entry = Cfg.entry subcfg in
  let _ = visit2 := Visit2.empty in
  let _ = add_block empty_ctxt entry f basicblocks in
  let _ = visit2 := Visit2.empty in
  let _ = make_gen_kill empty_ctxt entry in
  let _ = visit2 := Visit2.empty in
  let _ = make_in_out_fixpoint empty_ctxt entry in  
  let _ = visit2 := Visit2.empty in
  let _ = set_use empty_ctxt entry in
  
  let _ = collect_condition (get_empty_ctxt ()) f basicblocks in
  let _ = visit := Visit.empty in
  let _ = set_terms (get_empty_ctxt ()) f basicblocks in
  (*
  let _ = add_blocks empty_ctxt f basicblocks in
  let _ = visit := Visit.empty in
  let _ = set_operands_blocks' (get_empty_ctxt ()) f basicblocks 1 in
  let _ = visit := Visit.empty in
  let _ = set_operands_blocks' (get_empty_ctxt ()) f basicblocks 2 in
  let _ = visit := Visit.empty in
  let _ = set_uses' (get_empty_ctxt ()) f basicblocks in
  let _ = visit := Visit.empty in
  *)
  let _ =  
    Array.iter (fun bb -> Llvm.remove_block bb ) basicblocks in
  ()
  
let _ = 
  let f_name = Sys.argv.(2) in
  let f_target = 
    match Llvm.lookup_function f_name llm with
    | Some f -> f
    | None -> failwith "no target function exist."
  in
  let _ = transform f_target in 
  Llvm.print_module Sys.argv.(5) llm


  
