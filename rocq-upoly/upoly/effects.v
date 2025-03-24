(*
 * Copyright (C) 2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.upoly.prelude.
Require bluerock.upoly.list.
Require bluerock.upoly.id.
Require bluerock.upoly.reader.
Require bluerock.upoly.writer.
Require bluerock.upoly.state.
Require bluerock.upoly.optionT.
Require bluerock.upoly.listT.
Require bluerock.upoly.traceT.
Require bluerock.upoly.readerT.
Require bluerock.upoly.writerT.
Require bluerock.upoly.stateT.

Export list.Notations.

Add Printing Constructor id.M.
Add Printing Constructor reader.M.
Add Printing Constructor writer.M.
Add Printing Constructor state.M.
Add Printing Constructor optionT.M.
Add Printing Constructor listT.M.
Add Printing Constructor traceT.M.
Add Printing Constructor readerT.M.
Add Printing Constructor writerT.M.
Add Printing Constructor stateT.M.
