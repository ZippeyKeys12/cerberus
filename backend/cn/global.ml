open Pp
(* open Resultat
 * open TypeErrors *)

module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)
module IdMap = Map.Make(Id)
module StringMap = Map.Make(String)
module CF = Cerb_frontend
module LC = LogicalConstraints
module RE = Resources
module IT = IndexTerms
module BT = BaseTypes
module LS = LogicalSorts
module LRT = LogicalReturnTypes
module RT = ReturnTypes
module LFT = ArgumentTypes.Make(LRT)
module FT = ArgumentTypes.Make(RT)



type predicate_definition = 
  { iargs : (Sym.t * LS.t) list;
    oargs : (Sym.t * LS.t) list;
    pack_functions : LFT.t list;
    unpack_functions : LFT.t list;
  }



let early = 
  let open Resources in
  let open BT in
  let open IT in
  let id = "EarlyAlloc" in
  let start_s = Sym.fresh () in
  let start_t = sym_ (Integer, start_s) in
  let end_s = Sym.fresh () in
  let end_t = sym_ (Integer, end_s) in
  let iargs = [(start_s, LS.Base Integer); (end_s, LS.Base Integer)] in
  let oargs = [] in
  let pred = 
    Predicate {
        name = Id id; 
        iargs = [start_t; end_t];
        oargs = [];
        unused = (* bool_ *) true;
      } 
  in
  let block = 
    Resources.region 
      (integerToPointerCast_ start_t)
      (add_ (sub_ (end_t, start_t), int_ 1))
      (q_ (1, 1))
  in
  let pack_functions =
    [LFT.Resource (block, 
     LFT.Constraint (LC (IT.good_pointer_it (integerToPointerCast_ start_t) (Sctypes.Sctype ([], Void))),
     LFT.Constraint (LC (IT.good_pointer_it (integerToPointerCast_ end_t) (Sctypes.Sctype ([], Void))),
     LFT.I (
     LRT.Resource (pred,
     LRT.I)))))] 
  in
  let unpack_functions =
    [LFT.Resource (pred,
     LFT.I (
     LRT.Resource (block,
     LRT.Constraint (LC (IT.good_pointer_it (integerToPointerCast_ start_t) (Sctypes.Sctype ([], Void))),
     LRT.Constraint (LC (IT.good_pointer_it (integerToPointerCast_ end_t) (Sctypes.Sctype ([], Void))),
     LRT.I)))))]
  in
  let predicate = {
      iargs; 
      oargs; 
      pack_functions; 
      unpack_functions
    } 
  in
  (id, predicate)



let zero_region = 
  let open Resources in
  let open BT in
  let open IT in
  let id = "ZeroRegion" in
  let pointer_s = Sym.fresh () in
  let pointer_t = sym_ (Loc, pointer_s) in
  let length_s = Sym.fresh () in
  let length_t = sym_ (Integer, length_s) in
  let iargs = [(pointer_s, LS.Base Loc); (length_s, LS.Base Integer)] in
  let oargs = [] in
  let pred = 
    Predicate {
        name = Id id; 
        iargs = [pointer_t; length_t];
        oargs = [];
        unused = (* bool_ *) true;
      } 
  in
  let array = 
    RE.array pointer_t length_t (Z.of_int 1)
      (fun q -> int_ 0) (q_ (1,1))
  in
  let pack_functions =
    [LFT.Resource (array, 
     LFT.Constraint (LC (IT.good_pointer_it pointer_t (Sctypes.Sctype ([], Void))),
     LFT.I (
     LRT.Resource (pred,
     LRT.I))))] 
  in
  let unpack_functions =
    [LFT.Resource (pred,
     LFT.I (
     LRT.Resource (array,
     LRT.Constraint (LC (IT.good_pointer_it pointer_t (Sctypes.Sctype ([], Void))),
     LRT.I))))]
  in
  let predicate = {
      iargs; 
      oargs; 
      pack_functions; 
      unpack_functions
    } 
  in
  (id, predicate)







let builtin_predicates_list = [
    early;
    zero_region;
  ]

let builtin_predicates =
  List.fold_left (fun acc (name,def) -> StringMap.add name def acc) 
    StringMap.empty builtin_predicates_list
  




(* Auxiliaries *)

module ImplMap = 
  Map.Make
    (struct 
      type t = CF.Implementation.implementation_constant
      let compare = CF.Implementation.implementation_constant_compare 
     end)




let impl_lookup (e: 'v ImplMap.t) i =
  match ImplMap.find_opt i e with
  | None ->
     Debug_ocaml.error
       ("Unbound implementation defined constant " ^
          (CF.Implementation.string_of_implementation_constant i))
  | Some v -> v


type stored_struct_predicate =
  { pointer : Sym.t;
    value : Sym.t;
    pack_function: LFT.t; 
    unpack_function: LFT.t; 
  }


type struct_piece = 
  { offset: Z.t;
    size: Z.t;
    member_or_padding: (BT.member * Sctypes.t) option }

type struct_member = 
  { offset: Z.t;
    size: Z.t;
    member: BT.member * Sctypes.t }

type struct_decl = 
  { layout: struct_piece list;
    stored_struct_predicate: stored_struct_predicate
  }

let members = 
  List.filter_map (fun {member_or_padding; offset; size} ->
      Option.bind member_or_padding (fun (member, sctype) ->
          Some {offset; size; member = (member, sctype)}
        )
    )

let member_types =
  List.filter_map (fun {member_or_padding; _} ->
      Option.bind member_or_padding (fun (member, sctype) ->
          Some (member, sctype)
        )
    )

type struct_decls = struct_decl SymMap.t



module BTMap = Map.Make(BT)


type t = 
  { struct_decls : struct_decls; 
    fun_decls : (Locations.t * FT.t) SymMap.t;
    impl_fun_decls : FT.t ImplMap.t;
    impl_constants : RT.t ImplMap.t;
    (* stdlib_funs : FT.t SymMap.t; *)
    resource_predicates : predicate_definition StringMap.t;
    bindings: VariableBindings.bound SymMap.t;
  } 

let empty = 
  { struct_decls = SymMap.empty; 
    fun_decls = SymMap.empty;
    impl_fun_decls = ImplMap.empty;
    impl_constants = ImplMap.empty;
    (* stdlib_funs = SymMap.empty; *)
    resource_predicates = builtin_predicates;
    bindings = SymMap.empty;
  }


let struct_decl_to_predicate_def tag decl = 
  let pred = decl.stored_struct_predicate in
  let iargs = [(pred.pointer, LS.Base Loc)] in
  let oargs = [(pred.value, LS.Base (Struct tag))] in
  let pack_functions = [(pred.pack_function)] in
  let unpack_functions = [(pred.unpack_function)] in
  {iargs; oargs; pack_functions; unpack_functions}


let get_predicate_def global predicate_name = 
  let open Resources in
  match predicate_name with
  | Id id -> 
     StringMap.find_opt id global.resource_predicates
  | Tag tag ->
     match SymMap.find_opt tag global.struct_decls with
     | None -> None
     | Some decl -> Some (struct_decl_to_predicate_def tag decl)

let get_fun_decl global sym = SymMap.find_opt sym global.fun_decls
let get_impl_fun_decl global i = impl_lookup global.impl_fun_decls i
let get_impl_constant global i = impl_lookup global.impl_constants i



let pp_struct_decl (tag,decl) = 
  item ("struct " ^ plain (Sym.pp tag) ^ " (raw)") 
       (separate_map hardline (fun {offset; size; member_or_padding} -> 
            item "offset" (Z.pp offset) ^^ comma ^^^
            item "size" (Z.pp size) ^^ comma ^^^
            item "content" 
              begin match member_or_padding with 
              | Some (member, sct) -> 
                 typ (Id.pp member) (Sctypes.pp sct)
              | None ->
                 parens (!^"padding" ^^^ Z.pp size)
              end
          ) decl.layout
       )
  ^/^
  (* item ("struct " ^ plain (Sym.pp tag) ^ " (closed stored)") 
   *      (RT.pp decl.closed_stored)
   * ^/^ *)
  item ("struct " ^ plain (Sym.pp tag) ^ " (packing function) at P") 
    (LFT.pp (decl.stored_struct_predicate.pack_function))
  ^/^
  item ("struct " ^ plain (Sym.pp tag) ^ " (unpacking function) at P") 
    (LFT.pp (decl.stored_struct_predicate.unpack_function))

let pp_struct_decls decls = Pp.list pp_struct_decl (SymMap.bindings decls) 

let pp_fun_decl (sym, (_, t)) = item (plain (Sym.pp sym)) (FT.pp t)
let pp_fun_decls decls = flow_map hardline pp_fun_decl (SymMap.bindings decls)

let pp global = 
  pp_struct_decls global.struct_decls ^^ hardline ^^
  pp_fun_decls global.fun_decls





