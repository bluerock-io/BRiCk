(*
 * Copyright (C) 2023-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

type t = Pattern.constr_pattern

val subst : offset:int -> t -> t array -> t

val fold_with_binders : ('a -> int -> 'a) -> ('a -> 'b -> t -> 'b) -> 'a -> 'b -> t -> 'b

val term_of_pattern : Environ.env -> Evd.evar_map -> Pattern.constr_pattern -> Evd.evar_map * EConstr.t
