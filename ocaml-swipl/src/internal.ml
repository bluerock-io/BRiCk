(* Copyright (C) 2023 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

open Util

let prolog_error msg =
  clear_exception ();
  raise (Prolog(msg))
