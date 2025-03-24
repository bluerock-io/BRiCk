(*
 * Copyright (C) 2024-2025 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import Ltac2.Ltac2.

Declare ML Module "ltac2-llm-plugin.plugin".

Module LLM.

  Ltac2 @ external query_gpt : string -> string :=
    "ltac2_llm" "query_gpt".

End LLM.
