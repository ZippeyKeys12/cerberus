open Except
open PPrint
open Pp_tools


module StringMap = Map.Make(String)
module SymMap = Map.Make(Sym)

type t = 
  { sym_of_name : Sym.t StringMap.t;
    name_of_sym : string SymMap.t; 
    loc_of_sym : Location.t SymMap.t;
  }

let sym_of loc (string : string) (namemap : t) : (Sym.symbol,'e) m  = 
  match StringMap.find_opt string namemap.sym_of_name with
  | Some sym -> return sym
  | None -> 
     let err = !^ "Unbound name" ^^^ squotes (!^ string) in
     Except.fail loc err

let name_of loc (sym : Sym.t) (namemap : t) : (string,'e) m  = 
  match SymMap.find_opt sym namemap.name_of_sym with
  | Some name -> return name
  | None -> 
     let err = !^ "Unbound name" ^^^ squotes (Sym.pp sym) in
     Except.fail loc err

let loc_of loc (sym : Sym.t) (namemap : t) : (Location.t,'e) m  = 
  match SymMap.find_opt sym namemap.loc_of_sym with
  | Some loc -> return loc
  | None -> 
     let err = !^ "Unbound name" ^^^ squotes (Sym.pp sym) in
     Except.fail loc err


let all_names m = StringMap.bindings m.sym_of_name

let empty = 
  { sym_of_name = StringMap.empty;
    name_of_sym = SymMap.empty; 
    loc_of_sym = SymMap.empty;
  }

let record (loc : Location.t) (string : string) (sym : Sym.t) namemap = 
  { sym_of_name = StringMap.add string sym namemap.sym_of_name;
    name_of_sym = SymMap.add sym string namemap.name_of_sym;
    loc_of_sym  = SymMap.add sym loc namemap.loc_of_sym }


