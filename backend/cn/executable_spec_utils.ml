module CF=Cerb_frontend
module A=CF.AilSyntax
module C=CF.Ctype
module Cn=CF.Cn



let empty_qualifiers : C.qualifiers = {const = false; restrict = false; volatile = false}
let const_qualifiers : C.qualifiers = {const = true; restrict = false; volatile = false}

let empty_attributes = CF.Annot.Attrs []

let mk_ctype ctype_ = C.Ctype ([], ctype_)

let rm_ctype (C.Ctype (_, ctype_)) = ctype_

let mk_expr expr_ = 
  A.AnnotatedExpression (
    CF.GenTypes.GenLValueType (empty_qualifiers, mk_ctype C.Void, false),
     [], Cerb_location.unknown, expr_)

let mk_cn_expr cn_expr_ = 
  Cn.CNExpr (Cerb_location.unknown, cn_expr_)

let rm_cn_expr (Cn.CNExpr (_, cn_expr_))
  = cn_expr_


let mk_stmt stmt_ = 
  A.AnnotatedStatement (Cerb_location.unknown, CF.Annot.Attrs [], stmt_)

let rm_expr (A.AnnotatedExpression (_, _, _, expr_)) = expr_

let rm_stmt (A.AnnotatedStatement (_, _, stmt_)) = stmt_



let rec list_split_three = function 
  | [] -> ([], [], [])
  | (x, y, z) :: rest ->
    let (xs, ys, zs) = list_split_three rest in 
    (x::xs, y::ys, z::zs)


type cn_dependencies = CF.Symbol.sym list

type cn_dependency_graph = {
  cn_functions_with_dependencies : ( ((CF.Symbol.sym, C.ctype) Cn.cn_function)) list;
  
}

let compute_cn_dependencies ail_prog =
  ail_prog