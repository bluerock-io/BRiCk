Require Import bedrock.lang.cpp.logic.mpred.
Require Import bedrock.lang.cpp.logic.pred2.
Require Import bedrock.lang.cpp.semantics.values2.

Require Import bedrock.lang.cpp.model.inductive_pointers2.
(* Stand-in for actual models.
Ensures that everything needed is properly functorized. *)
Import PTRS_IMPL.

Declare Module Import VALUES_DEFS_IMPL : VALUES_INTF_FUNCTOR PTRS_IMPL.

Module CPP_BASE <: CPP_LOGIC_CLASS.

End CPP_BASE.