module CF = Cerb_frontend
module BT = BaseTypes
module IT = IndexTerms

let ocaml_int_bt = BT.Bits (Signed, Sys.int_size + 1)

let names = ref []

let get_mangled_name (syms : Sym.t list) : Sym.t =
  let open Pp in
  match List.assoc_opt (List.equal Sym.equal) syms !names with
  | Some sym -> sym
  | None ->
    let doc = string "cn_gen_" ^^ separate_map underscore Sym.pp syms in
    let res_sym = Sym.fresh_named (CF.Pp_utils.to_plain_string doc) in
    names := (syms, res_sym) :: !names;
    res_sym


let get_lower_bound ((x, bt) : Sym.sym * BT.t) (it : IT.t) : IT.t =
  let min =
    match bt with
    | Bits (sign, sz) -> fst (BT.bits_range (sign, sz))
    | _ -> failwith "unsupported type for `each`"
  in
  let rec aux (it : IT.t) : IT.t option =
    match it with
    | IT (Binop (EQ, IT (Sym x', _, _), tm2), _, _)
    | IT (Binop (EQ, tm2, IT (Sym x', _, _)), _, _) ->
      if Sym.equal x x' then Some tm2 else None
    | IT (Binop (LE, it', IT (Sym x', _, _)), _, _) when Sym.equal x x' -> Some it'
    | IT (Binop (LT, it', IT (Sym x', _, _)), _, _) when Sym.equal x x' ->
      Some
        (IT
           ( Binop (Add, it', IT.num_lit_ Z.one bt Cerb_location.unknown),
             bt,
             Cerb_location.unknown ))
    | IT (Binop (And, tm1, tm2), _, _) ->
      (match (aux tm1, aux tm2) with
       | None, None -> None
       | None, it' | it', None -> it'
       | Some tm1, Some tm2 ->
         Some (IT (Binop (Max, tm1, tm2), bt, Cerb_location.unknown)))
    | IT (Binop (Or, tm1, tm2), _, _) ->
      (match (aux tm1, aux tm2) with
       | None, None | None, _ | _, None -> None
       | Some tm1, Some tm2 ->
         Some (IT (Binop (Min, tm1, tm2), bt, Cerb_location.unknown)))
    | _ -> None
  in
  aux it |> Option.value ~default:(IT.num_lit_ min bt Cerb_location.unknown)


let get_upper_bound ((x, bt) : Sym.sym * BT.t) (it : IT.t) : IT.t =
  let max =
    match bt with
    | Bits (sign, sz) -> snd (BT.bits_range (sign, sz))
    | _ -> failwith "unsupported type for `each`"
  in
  let rec aux (it : IT.t) : IT.t option =
    match it with
    | IT (Binop (EQ, IT (Sym x', _, _), tm2), _, _)
    | IT (Binop (EQ, tm2, IT (Sym x', _, _)), _, _) ->
      if Sym.equal x x' then Some tm2 else None
    | IT (Binop (LE, IT (Sym x', _, _), it'), _, _) when Sym.equal x x' -> Some it'
    | IT (Binop (LT, IT (Sym x', _, _), it'), _, _) when Sym.equal x x' ->
      Some
        (IT
           ( Binop (Sub, it', IT.num_lit_ Z.one bt Cerb_location.unknown),
             bt,
             Cerb_location.unknown ))
    | IT (Binop (And, tm1, tm2), _, _) ->
      (match (aux tm1, aux tm2) with
       | None, None -> None
       | None, it' | it', None -> it'
       | Some tm1, Some tm2 ->
         Some (IT (Binop (Min, tm1, tm2), bt, Cerb_location.unknown)))
    | IT (Binop (Or, tm1, tm2), _, _) ->
      (match (aux tm1, aux tm2) with
       | None, None | None, _ | _, None -> None
       | Some tm1, Some tm2 ->
         Some (IT (Binop (Max, tm1, tm2), bt, Cerb_location.unknown)))
    | _ -> None
  in
  aux it |> Option.value ~default:(IT.num_lit_ max bt Cerb_location.unknown)


let get_bounds ((x, bt) : Sym.sym * BT.t) (it : IT.t) : IT.t * IT.t =
  (get_lower_bound (x, bt) it, get_upper_bound (x, bt) it)
