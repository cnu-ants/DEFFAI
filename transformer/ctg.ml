open Calli

module Make 
  (* (FlaCtxt2 : Context.S) *)
  (Summary : States.S with type ctxtty = FlaCtxt2.t and type memty = FlaCtxt2.memty)  = struct  

type summaryty = Summary.t

module CtxtSet = Set.Make(struct type t = FlaCtxt2.t let compare = compare end)
module CTG = Map.Make(struct type t = FlaCtxt2.t let compare = compare end)


let ctg = ref CTG.empty
let contexts = ref CtxtSet.empty
let size = FlaCtxt2.size

let find = CTG.find
let find_opt = CTG.find_opt

let pp_ctxtset fmt s =
  let _ = Format.fprintf fmt "{" in
  let _ = CtxtSet.iter 
    (fun ctxt -> 
      Format.fprintf fmt "%a " FlaCtxt2.pp ctxt
    )
    s
  in
  let _ = Format.fprintf fmt "}" in
  ()

let pp () =
  let _ = Format.printf "<CTG>\n" in
  let _ = CTG.iter 
    (fun c set -> 
      let _ = Format.printf "%a : " FlaCtxt2.pp c in
      let _ = Format.printf "%a@." pp_ctxtset set in
      ()
    )
    !ctg
  in ()

let rec pop_back = function
  | [] -> []
  | [_] -> []
  | hd :: tl -> hd :: pop_back tl

let get_ctxts (f : Function.t) s = 
  let _ = Cfg.iter 
  (fun bb_name _ -> 
    let bb : Basicblock.t = Bbpool.find_bb bb_name in
    match bb.term with
    | _ -> 
      if Summary.mem' bb s then
      let ctxtM = Summary.find bb s in
      let _ = Summary.CtxtM.iter
        (fun ctxt m ->
          if AbsMemory.is_bot m then () else
          let _ = contexts := CtxtSet.add ctxt !contexts in 
          ()
        ) ctxtM 
      in 
      ()
      else ()
  )
  f.cfg in
  let _ = contexts := CtxtSet.add (FlaCtxt2.empty ()) !contexts in ()


let make_ctg () = 
  let _ = CtxtSet.iter
    (fun ctxt -> 
      let nexts = CtxtSet.fold
        (fun c s -> 
          if List.length ctxt < !size then
            (match c with
            | _ :: tl -> if tl =  ctxt then CtxtSet.add c s else s
            | [] -> s
            )
          else 
            (match c with
            | [] -> s
            | _  -> 
              if (pop_back ctxt) = (List.tl c) then
                CtxtSet.add c s
              else s
            )
        )
        !contexts CtxtSet.empty
      in
      if nexts = CtxtSet.empty then () else
      let _ = ctg := CTG.add ctxt nexts !ctg in ()
    )
    !contexts
  in ()

module Visit = Set.Make(struct type t = FlaCtxt2.t let compare = compare end)
let visit = ref Visit.empty

let rec add_blocks oc ctxt =
  let _ = visit := Visit.add ctxt !visit in
  let ctxt_str = Format.asprintf "%a" FlaCtxt2.pp ctxt in
  let _ = 
    match find_opt ctxt !ctg with
    | Some s -> 
      let _ = CtxtSet.iter
        (fun ctxt' -> 
            let ctxt_str' = Format.asprintf "%a" FlaCtxt2.pp ctxt' in
            let _ = Printf.fprintf oc "  \"%s\" -> \"%s\";\n" ctxt_str ctxt_str' in
            if Visit.mem ctxt' !visit then
              ()
            else
              add_blocks oc ctxt' 
        )
        s
      in
      ()
    | None -> ()
  in
  () 

let pred ctxt ctg = 
  CTG.fold (fun ctxt' set acc -> 
    if CtxtSet.mem ctxt set then
      ctxt'::acc
    else
      acc
  )
  ctg []

let ctg_to_dot () = 
  let filename = "ctg.dot" in
  let oc = open_out filename in
  let _= Printf.fprintf oc "digraph G {\n" in
  let _ = add_blocks oc (FlaCtxt2.empty ()) in
  let _ = Printf.fprintf oc "}\n" in
  close_out oc





let make (f : Function.t) s = 
  let _ = get_ctxts f s in
  let _ = make_ctg () in
  ctg_to_dot ()


end
