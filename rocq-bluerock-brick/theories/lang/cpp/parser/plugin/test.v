Require Import bedrock.lang.cpp.parser.
Require Import bedrock.lang.cpp.parser.plugin.cpp2v.

cpp.tu module
  abi Little
  defns (parser.Dtype "align_val_t") (parser.Dtypedef "xx" (Tnamed "align_val_t")).

Print module.
