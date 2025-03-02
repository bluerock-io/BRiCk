(*
 * Copyright (c) 2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require PArray.
Require Import PrimInt63.
Require Import bedrock.lang.cpp.parser.

#[local] Set Printing Universes.

Register parser.translation_unit.t as bedrock.lang.cpp.parser.translation_unit.t.
Register parser.translation_unit._skip as bedrock.lang.cpp.parser.translation_unit.skip.

(* NOTE: This is a hack to get a universe instance *)
Definition empty_array := PArray.make 0%uint63 parser.translation_unit._skip.
Register empty_array as bedrock.lang.cpp.parser.translation_unit.empty_array.

Definition abi_type := endian.
Register abi_type as bedrock.lang.cpp.parser.translation_unit.abi_type.

Register translation_unit.decls as bedrock.lang.cpp.parser.translation_unit.decls.

Definition result_type : Type := translation_unit * list name.
Register result_type as bedrock.lang.cpp.parser.translation_unit.result_type.

Declare ML Module "rocq-bluerock-brick.plugin".
