module F = Format
module Ctxt = FlaCtxt2

open Calli

let module_no_prune = ref Module.empty 
let bbpool_no_prune = ref Bbpool.empty 

let init str = 
  let m = Init.init () in 
  (* let _ = Init.loop_unroll 3 in *)
  (*let m = Init.transform_call () in
  *)let _ = module_no_prune := m.function_map in
  let _ = bbpool_no_prune := !Bbpool.pool in
 (* let _ = Init.transform_select () in
 *) let _ = Init.transform_prune () in
  let _ = Init.transform_fla str in
  let _ = Init.make_llm () in
  let _ = Init.make_call_graph () in ()


module States = States.Make (FlaCtxt2) (AbsMemory)
module Analyzer = LlvmAnalyzer.Make (AbsValue) (AbsMemory) (FlaCtxt2) (States) (TF)
module Summary = States
module CCM = Ccm.Make (AbsMemory) (States)
module CTG = Ctg.Make (States)


let analyze () = 

  let str = Sys.argv.(6) in
  let _ = FlaCtxt2.ctxt_val := Sys.argv.(6) in
  let _ = init str in
  let init_mem = Analyzer.init (Init.m ())  in 
  let target_f : Function.t = Module.find Sys.argv.(2) (Init.llmodule ()) in
  let target_f_no_prune : Function.t = Module.find Sys.argv.(2) !module_no_prune in
  (*let main : Function.t = Module.main (Init.llmodule ()) in
  let entry = Bbpool.find (main.entry) !Bbpool.pool in*)
  let entry = Bbpool.find (target_f.entry) !Bbpool.pool in
  (*  let _ = Dot.make target_f in
*)  (*let _ = FlaCtxt2.fname := "main(i64 %argc, i8** %argv)" in
  let _ = FlaCtxt2.fname := main.function_name in*)
  let _ = FlaCtxt2.fname := target_f.function_name in
  let _ = FlaCtxt2.size := Int64.to_int (Int64.of_string Sys.argv.(3)) in
  let _ = Analyzer.LoopCounter.set_max_count (Int64.to_int (Int64.of_string Sys.argv.(4))) in
  let init_states = States.update (entry, FlaCtxt2.empty ()) init_mem States.empty in
  (*let _ = Format.printf "analyze...\n" in*)
  let s = Analyzer.analyze entry init_states in
  let s = !Analyzer.summary in
  (*let _ = Format.printf "%a\n" States.pp s in
  let _ = Format.printf "ENV \n %a\n" Env.pp !Env.env in
  *)let _ = CCM.make target_f_no_prune target_f s !bbpool_no_prune  in
  let _ = CTG.make target_f_no_prune s in
  ()
