(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.lang.cpp.parser.prelude.
Require Import bluerock.lang.cpp.parser.lang.

(** * Derived names emitted by cpp2v *)

Module ParserName (Import Lang : PARSER_LANG).

  (* It is important that the argument types of names do not
     include <<const>> or <<volatile>> on argument types because
     overlapping declarations can differ on qualification here.
   *)
  Definition Nfunction qs nm ts :=
    Nfunction qs nm $ List.map (@normalize_arg_type parser_lang) ts.
  Definition Nctor ts :=
    Nctor $ List.map (@normalize_arg_type parser_lang) ts.
  Definition Nop q oo ts :=
    Nop q oo $ List.map (@normalize_arg_type parser_lang) ts.
  Definition Nop_lit fn ts :=
    Nop_lit fn $ List.map (@normalize_arg_type parser_lang) ts.

  Definition Nrecord_by_field (nm : ident) : atomic_name' parser_lang :=
    Nfirst_child nm.

  Definition Nenum_by_enumerator (nm : ident) : atomic_name' parser_lang :=
    Nfirst_child nm.

  Definition Nby_first_decl (nm : ident) : atomic_name' parser_lang :=
    Nfirst_decl nm.

  Definition Ndependent (t : type' parser_lang) : name' parser_lang :=
    match t with
    | Tnamed nm => nm
    | _ => Ndependent t
    end.

  Definition Nlocal (n : atomic_name' parser_lang) :=
    Nglobal n. (* TODO: this is incorrect *)

End ParserName.
