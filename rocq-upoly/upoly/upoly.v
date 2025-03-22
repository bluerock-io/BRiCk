(*
 * Copyright (C) BlueRock Security, Inc. 2024
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export bluerock.upoly.base.	(* base.v *)

(** Types *)

Require bluerock.upoly.UTypes.	(* UTypes.v *)
Require bluerock.upoly.prod.	(* prod.v *)
Require bluerock.upoly.sum.	(* sum.v *)
Require bluerock.upoly.option.	(* option.v *)
Require bluerock.upoly.list.	(* list.v *)

(** Monads *)

Require bluerock.upoly.id.	(* id.v *)
Require bluerock.upoly.trace.	(* trace.v *)
Require bluerock.upoly.reader.	(* reader.v *)
Require bluerock.upoly.writer.	(* writer.v *)
Require bluerock.upoly.state.	(* state.v *)

(** Monad transformers *)

Require bluerock.upoly.optionT.	(* optionT.v *)
Require bluerock.upoly.listT.	(* listT.v *)
Require bluerock.upoly.traceT.	(* traceT.v *)
Require bluerock.upoly.readerT.	(* readerT.v *)
Require bluerock.upoly.writerT.	(* writerT.v *)
Require bluerock.upoly.stateT.	(* stateT.v *)

Require Export bluerock.upoly.effects.	(* effects.v *)
