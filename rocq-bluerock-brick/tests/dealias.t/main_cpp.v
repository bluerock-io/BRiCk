Require Import bluerock.lang.cpp.parser.

#[local] Open Scope pstring_scope.

Require Import bluerock.lang.cpp.parser.plugin.cpp2v.
cpp.prog module
  abi Little
  defns
    (Dtypedef (Nglobal (Nid "__int128_t")) Tint128_t)
    (Dtypedef (Nglobal (Nid "__uint128_t")) Tuint128_t)
    (Dtypedef (Nglobal (Nid "__NSConstantString")) (Tnamed (Nglobal (Nid "__NSConstantString_tag"))))
    (Dtypedef (Nglobal (Nid "__builtin_ms_va_list")) (Tptr Tchar))
    (Dtypedef (Nglobal (Nid "__builtin_va_list")) (Tarray (Tnamed (Nglobal (Nid "__va_list_tag"))) 1))
    (Dtypedef (Nglobal (Nid "Tr")) (Tref Tint))
    (Dtypedef (Nglobal (Nid "Trr")) (Trv_ref Tint))
    (Dtypedef (Nglobal (Nid "Tr_r")) (Tref Tint))
    (Dtypedef (Nglobal (Nid "Tr_rr")) (Tref Tint))
    (Dtypedef (Nglobal (Nid "Trr_r")) (Tref Tint))
    (Dtypedef (Nglobal (Nid "Trr_rr")) (Trv_ref Tint))
    (Dtypedef (Nglobal (Nid "cTr")) (Tref (Qconst Tint)))
    (Dtypedef (Nglobal (Nid "cTrr")) (Trv_ref (Qconst Tint)))
    (Dtypedef (Nglobal (Nid "cTr_r")) (Tref Tint))
    (Dtypedef (Nglobal (Nid "cTr_rr")) (Tref Tint))
    (Dtypedef (Nglobal (Nid "cTrr_r")) (Tref Tint))
    (Dtypedef (Nglobal (Nid "cTrr_rr")) (Trv_ref Tint)).

Require Import bluerock.lang.cpp.syntax.dealias.

Notation TEST input output :=
  (eq_refl : trace.runO (resolveN tu input) = Some output).

Succeed Example _1 := TEST "test(int)" "test(int)".
