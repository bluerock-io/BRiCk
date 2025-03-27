Require Import accumulate_bug.accumulate1.
Require Import accumulate_bug.accumulate2.
(* Succeed Elpi Typecheck program. *)
(*
Used to throw the error below before it got fixed in coq-elpi:
Error:
File "ROOT/_build/default/fmdeps/cpp2v/elpi-extra/accumulate_bug/library.elpi", line 5, column 2, character 59:duplicate type abbreviation for cpp.bs. Previous declaration: File "ROOT/_build/default/fmdeps/cpp2v/elpi-extra/accumulate_bug/library.elpi", line 5, column 2, character 59:
*)
