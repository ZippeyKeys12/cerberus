open Mem_common

val pp_pure_memop: pure_memop -> PPrint.document
val pp_memop: memop -> PPrint.document

(*
val pp_pointer_value: pointer_value -> PPrint.document
val pp_integer_value: integer_value -> PPrint.document
val pp_integer_value_for_core: integer_value -> PPrint.document
val pp_mem_value: mem_value -> PPrint.document

val pp_pretty_pointer_value: pointer_value -> PPrint.document
val pp_pretty_integer_value: ?basis:Memory_model.basis -> use_upper:bool -> integer_value -> PPrint.document
val pp_pretty_mem_value: ?basis:Memory_model.basis -> use_upper:bool -> mem_value -> PPrint.document
*)

val pp_mem_constraint: ('a -> PPrint.document) -> 'a mem_constraint -> PPrint.document
