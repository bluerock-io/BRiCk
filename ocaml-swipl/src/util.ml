(* Copyright (C) 2023 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

exception Prolog of string

let clear_exception : unit -> unit = C.F.clear_exception
