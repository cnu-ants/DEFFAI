open Calli
module F = Format


module M = Map.Make(String)

type memty = AbsMemory.t
type elt = Cond of string | Empty 
type t = elt M.t list

let fname = ref ""
let size = ref 2

let ctxt_val = ref ""

let empty () = []



module Label = Map.Make(String)
let label = ref Label.empty

let current = ref 1

let create_alphabet_generator () : string =
      let result = string_of_int !current in
      current := (!current + 1); (* 다음 문자로 이동 *)
      result


let pp (fmt : Format.formatter) (ctxt : t) =
  let _ = 
    List.iter
    (fun c -> 
      let _ =
        M.iter
        (fun str elt ->
          let n : string = if Label.mem str !label then Label.find str !label 
            else let _ = label := Label.add str (create_alphabet_generator ()) !label in Label.find str !label 
          in
          let _ = Format.fprintf fmt "(%s" n in
          match elt with
          | Empty -> F.fprintf fmt "empty)" 
          | Cond s -> Format.fprintf fmt ":%s)" s
        )
      c in
      Format.fprintf fmt "" 
    ) ctxt in
  ()


let pp_elt (fmt : Format.formatter) (elt:elt) = 
  match elt with
  | Empty -> F.fprintf fmt "  empty  " 
  | Cond s -> F.fprintf fmt "%s" s
  
let value = ref None

let get_tf ctxt =
  let _ = 
    M.iter
    (fun _ elt ->
      match elt with
      | Cond "t" -> value := Some true
      | Cond "f" -> value := Some false
      | Empty -> failwith "empty"
      | _ -> failwith "unreachable"
    )
    (List.hd ctxt)
  in
  match !value with
  | Some v -> v
  | None -> failwith "no value"


let value1 = ref None

let get_value ctxt : int =
  let _ = 
    M.iter
    (fun _ elt ->
      match elt with
      | Cond s -> value1 := Some (int_of_string s)
      | Empty -> failwith "empty"
    )
    (List.hd ctxt)
  in
  match !value1 with
  | Some v -> v
  | None -> failwith "no value"

let is_default ctxt =
    M.fold
    (fun _ elt b ->
      match elt with
      | Cond s -> String.ends_with s ~suffix:"default"
      | _ -> false 
    )
    (List.hd ctxt) false



let rec pop_back = function
  | [] -> []  
  | [_] -> [] 
  | hd :: tl -> hd :: pop_back tl


let push_back (s : elt M.t) (ctxt : t) = 
  if !size = 0 then []
  else
    if List.length ctxt = !size then
      s::(pop_back ctxt)
    else
      s::ctxt


let cartesian l1 l2 =
  List.concat (List.map (fun x -> List.map (fun y -> (x, y)) l2) l1)

let apply (bb : Basicblock.t) (next_bb_list : Basicblock.t list) ctxt mem =
  (* 분석 값으로 다음 ctxt 생성해 successor에 전달.*)
  (* cond가 ctxt_val과 관련있는 변수인지 확인할 필요가 없음 (transform4.ml 참고.) *) 
  match bb.term with
  | Switch {default_succ; succ; cond; _} -> 
    let succ_lst = List.filter_map (fun (case, succ) -> 
          (match (case : Expr.t) with
          | ConstInt {value; _;} -> 
            let a = Env.find (Expr.typed_var_of_expr cond).name !Env.env in
            let v = AbsMemory.find a mem in
(*            let filter_applying = 
              (match v with
              | AbsInt absint ->
                (match absint with
                | IntSet set ->
                  if AbsValue.AbsInt.S.mem value set then true else false
                | IntTop -> true
                | IntBot -> false
                )
              | AbsTop -> true
              | _ -> false
            ) in
            if not filter_applying then None
            else
*)            let z_case = Z.to_string value in
              Some (z_case, (Expr.typed_var_of_expr succ).name)
          | _ -> failwith "apply error1"
          ) ) succ in
    let succ_lst = ("default", (Expr.typed_var_of_expr default_succ).name)::succ_lst in
    List.filter_map (fun (next : Basicblock.t) -> 
        (match List.find_opt (fun (case, succ) -> succ = next.bb_name ) succ_lst with
        | Some (case, _) -> 
          let ctxt = 
            let e = M.add bb.bb_name (Cond case) M.empty in
            push_back e ctxt in
          Some (next, ctxt)
        | None -> None)
    ) next_bb_list
  (*| CondBr {succ0; succ1; _} -> 
    let ctxt_t =  
      let e = M.add bb.bb_name (Cond "t") M.empty in
      push_back e ctxt in
    let ctxt_f =  
      let e = M.add bb.bb_name (Cond "f") M.empty in
      push_back e ctxt in
    let true_succ_name = (Expr.typed_var_of_expr succ0).name in
    List.map (fun (succ : Basicblock.t) -> 
      if succ.bb_name = true_succ_name then 
      (succ, ctxt_t)
      else (succ, ctxt_f)
      ) next_bb_list
  *)(*| Switch {default_succ; succ; _} ->*)
  | _ -> List.map (fun bb -> (bb, ctxt)) next_bb_list
