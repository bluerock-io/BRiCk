(*
 * Copyright (C) BlueRock Security, Inc. 2024-2025
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
open Ltac2_plugin
open Tac2ffi
open Tac2externals
(* open Unix *)

let delimiter = "\nEOF\n"

let print_chan channel =
  let rec loop () =
    let line = input_line channel in
    print_endline line;
    loop ()
  in
  try loop ()
  with End_of_file -> close_in channel

(* https://chatgpt.com/share/96582f44-4e71-46de-a7a6-c24e9dc11141 *)
let llmquery (s: string) : string =
  let (ocaml_stdout, ocaml_stdin, ocaml_stderr) = Unix.open_process_full "python3 /builds/bedrocksystems/bhv/fmdeps/cpp2v/ltac2-llm/llm_query.py" [||] in
  output_string ocaml_stdin s;
  output_string ocaml_stdin delimiter; (* Send delimiter to indicate end of input *)
  close_out ocaml_stdin;

  let buffer = Buffer.create 1024 in
  (try
     while true do
       Buffer.add_channel buffer ocaml_stdout 1
     done
   with End_of_file -> ());
  close_in ocaml_stdout;
  close_in ocaml_stderr;

  Buffer.contents buffer

let define s =
  define Tac2expr.{ mltac_plugin = "ltac2_llm"; mltac_tactic = s }

let bytes_fn_of_string (f: string->string) (b:bytes) :bytes =
  Bytes.of_string (f (Bytes.to_string b))

let _ =
  define "query_gpt" (bytes @-> ret bytes) @@ fun s ->
    bytes_fn_of_string llmquery s
