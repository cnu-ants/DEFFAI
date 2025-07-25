open Calli

module Make 
  (*(FlaCtxt2 : Context.S)*)
  (AbsMem : AbstractMemory.S)
  (Summary : States.S with type ctxtty = FlaCtxt2.t and type memty = AbsMem.t)  = struct
  

type summaryty = Summary.t

module S = Set.Make(struct type t = FlaCtxt2.t let compare = compare end)

let s = ref S.empty

let get_ctxts (f : Function.t) summary = 
  let _ = Cfg.iter 
  (fun bb_name _ -> 
    let bb : Basicblock.t = Bbpool.find_bb bb_name in
    match bb.term with
    | Switch _
    | CondBr _ -> ()
    | _ -> 
      if Summary.mem' bb summary then
      let ctxtM = Summary.find bb summary in
      let _ = Summary.CtxtM.iter
        (fun ctxt m ->
          if AbsMem.is_bot m then () else
          let _ = s := S.add ctxt !s in 
          let _ = Format.printf "%a@." FlaCtxt2.pp ctxt in
          ()
        ) ctxtM 
      in 
      ()
      else ()
  )
  f.cfg in
  let _ = s := S.add (FlaCtxt2.empty ()) !s in !s 

let ctxt_lst summary = 
  let _ = 
    Summary.iter
      (fun (bb : Basicblock.t) _ -> 
        let _ = 
          Summary.CtxtM.iter
          (fun ctxt m -> 
            if AbsMem.is_bot m then () else
            s := S.add ctxt !s)
          (Summary.find bb summary)
        in ()
      )
    summary
  in
  !s

module BBSet = Set.Make(String)
module CCM = Map.Make(struct type t = FlaCtxt2.t let compare = compare end)
module OrderedCCM = Map.Make(struct type t = FlaCtxt2.t let compare = compare end)

module CCM' = Map.Make(struct type t = FlaCtxt2.t let compare = compare end)
let ccm' : Cfg.t CCM'.t ref = ref CCM'.empty
let find' = CCM'.find

let ccm = ref CCM.empty
let orderedccm = ref OrderedCCM.empty

let find = CCM.find
let find_orderedccm = OrderedCCM.find

let pool = ref Bbpool.empty

let find_bb_with_ctxt (f : Function.t) (c : FlaCtxt2.t) summary = 
  let subcfg : Cfg.t = Cfg.empty in
  let subcfg : Cfg.t = Cfg.fold 
    (fun bb_name _ subcfg ->
      let bb = Bbpool.find_bb bb_name in
      let _ = Format.printf "Term %a@." Term.pp bb.term in
      let llvm_bb_name = bb.loc in
      if (Summary.mem' bb summary) && Summary.CtxtM.mem c (Summary.find bb summary) && 
      (Summary.CtxtM.find c (Summary.find bb summary)) <> AbsMem.bot &&  llvm_bb_name <> "" then
        let bb = Bbpool.find_bb_from_pool bb_name !pool in
        let bblist = OrderedCCM.find c !orderedccm in
        let bblist = 
          if List.mem llvm_bb_name bblist then bblist else bblist@[llvm_bb_name] in
        let _ = orderedccm := OrderedCCM.add c bblist !orderedccm in
        let bbset = CCM.find c !ccm in
        let bbset = BBSet.add llvm_bb_name bbset in
        let _ = ccm := CCM.add c bbset !ccm in
        let succs = (match bb.term with
          | CondBr {succ0; succ1; _} ->
            if FlaCtxt2.get_tf c then
              let true_succ = (Expr.typed_var_of_expr succ0).name in
              [(Bbpool.find_bb true_succ).loc]
            else 
              let false_succ = (Expr.typed_var_of_expr succ1).name in
              [(Bbpool.find_bb false_succ).loc]
          | Switch {succ; _} -> 
            let _ = Format.printf "jijijij@." in
            let case : int = FlaCtxt2.get_value c in
            List. filter_map (fun (expr, succ) -> 
              let i = (match (expr:Expr.t) with
                | ConstInt {value; _} -> Z.to_int value
                | _ -> failwith "unreachable?") in
              let _ = Format.printf "%d and %d" case i in
              if i = case then 
                let _ = Format.printf "succ %s@." ((Bbpool.find_bb (Expr.typed_var_of_expr succ).name).bb_name) in 
                Some ((Bbpool.find_bb (Expr.typed_var_of_expr succ).name).loc)
              else 
                let _ = Format.printf "False @."  in

                None) succ
          | _ -> 
            let succs = Cfg.find bb_name f.cfg in
            let succs = List.filter_map 
              (fun succ -> 
              let bb = Bbpool.find_bb succ in
              (match bb.term with
              | Switch _
              | CondBr _ -> None
              | _ -> Some bb.loc)
            ) succs in succs
          ) in
        Cfg.add llvm_bb_name succs subcfg
      else subcfg)
    f.cfg subcfg
  in 
  let _ = ccm' := CCM'.add c subcfg !ccm' in ()


let make_subcfg (f : Function.t) (c : FlaCtxt2.t) =
  let subcfg : Cfg.t = find' c !ccm' in
  let subcfg : Cfg.t = Cfg.map 
    (fun succs -> 
      let new_succs : string list = 
        List.filter
        (fun succ -> 
          Cfg.mem succ subcfg
        ) succs in new_succs
    ) subcfg
  in
  let _ = ccm' := CCM'.add c subcfg !ccm' in ()



let make_ccm (f : Function.t) f_prune summary = 
  let _ = 
    S.iter
    (fun c -> 
      let _ = ccm := CCM.add c (BBSet.empty) !ccm in
      let _ = orderedccm := OrderedCCM.add c [] !orderedccm in
      let _ = find_bb_with_ctxt f c summary in
      let _ = make_subcfg f c in
      let _ = 
        if OrderedCCM.find c !orderedccm = [] 
          then 
            let _ = ccm := CCM.remove c !ccm in
            let _ = orderedccm := OrderedCCM.remove c !orderedccm in ()
        else () in 
      ()
    ) 
    (get_ctxts f_prune summary)
  in
  ()


let make (f : Function.t) f_prune summary p = 
  let _ = pool := p in
  make_ccm f f_prune summary

let pp_bbset fmt s =
  let _ = Format.fprintf fmt "{" in
  let _ = BBSet.iter 
    (fun bb -> 
      Format.fprintf fmt "%s, " bb
    )
    s
  in
  let _ = Format.fprintf fmt "}" in
  ()

let pp_bblst fmt s =
  let _ = Format.fprintf fmt "{" in
  let _ = List.iter 
    (fun bb -> 
      Format.fprintf fmt "%s, " bb
    )
    s
  in
  let _ = Format.fprintf fmt "}" in
  ()

let pp' () =
  let _ = Format.printf "<CCM'>\n" in
  let _ = CCM'.iter 
    (fun c succs -> 
      let _ = Format.printf "%a : " FlaCtxt2.pp c in
      let _ = Format.printf "%a\n" Cfg.pp succs in
      ()
    )
    !ccm'
  in ()

let pp () =
  let _ = Format.printf "<CCM>\n" in
  let _ = CCM.iter 
    (fun c set -> 
      let _ = Format.printf "%a : " FlaCtxt2.pp c in
      let _ = Format.printf "%a\n" pp_bbset set in
      ()
    )
    !ccm
  in ()

let pp_orderedCCM () =
  let _ = Format.printf "<Ordered CCM>\n" in
  let _ = OrderedCCM.iter 
    (fun c set -> 
      let _ = Format.printf "%a : " FlaCtxt2.pp c in
      let _ = Format.printf "%a\n" pp_bblst set in
      ()
    )
    !orderedccm
  in ()
  

end
