(*
 * Copyright (c) 2022 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From bedrock.lang.cpp Require Import ast notations.

Section TestTypeNotations.
  Context (ty rty aty1 aty2 : type) (n : N) (nm : bs).

  #[local] Definition Notation_Tptr_1 : Tptr Tbool = {(t: ptr<bool>)}%cpp_type := eq_refl.
  #[local] Definition Notation_Tptr_2 : Tptr ty = {(t: ptr<{(coq: ty)}>)}%cpp_type := eq_refl.
  Print Notation_Tptr_1. Print Notation_Tptr_2.

  #[local] Definition Notation_Tref_1 : Tref Tbool = {(t: ref&<bool>)}%cpp_type := eq_refl.
  #[local] Definition Notation_Tref_2 : Tref ty = {(t: ref&<{(coq: ty)}>)}%cpp_type := eq_refl.
  Print Notation_Tref_1. Print Notation_Tref_2.

  #[local] Definition Notation_Trv_ref_1 : Trv_ref Tbool = {(t: ref&&<bool>)}%cpp_type := eq_refl.
  #[local] Definition Notation_Trv_ref_2 : Trv_ref ty = {(t: ref&&<{(coq: ty)}>)}%cpp_type := eq_refl.
  Print Notation_Trv_ref_1. Print Notation_Trv_ref_2.

  #[local] Definition Notation_Tref_Trv_ref : Tref (Trv_ref ty) = {(t: ref&<ref&&<{(coq: ty)}>>)}%cpp_type := eq_refl.
  #[local] Definition Notation_Trv_ref_Tref : Trv_ref (Tref ty) = {(t: ref&&<ref&<{(coq: ty)}>>)}%cpp_type := eq_refl.
  Print Notation_Tref_Trv_ref. Print Notation_Trv_ref_Tref.

  #[local] Definition Notation_void : Tvoid = {(t: void)}%cpp_type := eq_refl.
  Print Notation_void.

  #[local] Definition Notation_Tarray_1 : Tarray Tnullptr 100 = {(t: nullptr_t[100])}%cpp_type := eq_refl.
  #[local] Definition Notation_Tarray_2 : Tarray ty n = {(t: {(coq: ty)}[n])}%cpp_type := eq_refl.
  Print Notation_Tarray_1. Print Notation_Tarray_2.

  #[local] Definition Notation_Tnamed_1 : Tnamed "foobarbaz" = {(t: "foobarbaz")}%cpp_type := eq_refl.
  #[local] Definition Notation_Tnamed_2 : Tnamed nm = {(t: nm)}%cpp_type := eq_refl.
  Print Notation_Tnamed_1. Print Notation_Tnamed_2.

  #[local] Definition Notation_Tfunction_novariadic_noargs_1 : Tfunction Tvoid nil = {(t: extern CC_C ???() -> void)}%cpp_type := eq_refl.
  #[local] Definition Notation_Tfunction_novariadic_noargs_2 : Tfunction rty nil = {(t: extern CC_C ???() -> {(coq: rty)})}%cpp_type := eq_refl.
  Print Notation_Tfunction_novariadic_noargs_1. Print Notation_Tfunction_novariadic_noargs_2.

  #[local] Definition Notation_Tfunction_novariadic_args_nowrap_1 : Tfunction Tvoid (cons Tbool (cons Tnullptr nil)) = {(t: extern CC_C ???(bool, nullptr_t) -> void)}%cpp_type := eq_refl.
  #[local] Definition Notation_Tfunction_novariadic_args_nowrap_2 :
    Tfunction rty (cons aty1 (cons Tvoid (cons aty2 nil))) = {(t: extern CC_C ???({(coq: aty1)}, void, {(coq: aty2)}) -> {(coq: rty)})}%cpp_type := eq_refl.
  Print Notation_Tfunction_novariadic_args_nowrap_1.
  Print Notation_Tfunction_novariadic_args_nowrap_2.

  #[local] Definition Notation_Tfunction_novariadic_args_wrap :
    Tfunction Tvoid (cons (Tnamed "askldjfo;lasjdlkfj;aklsdjg;blkajl;ksdjfl;aksdjf;lkasjdf;lkajsd;lfkjas;dlkfj;alskdjf;kalsdjf;lk")
                          (cons (Tnamed "askldjflk;ajsdkl;gjasdklgjakl;sdjgl;kasdjfl;kjasdlfhajklsdgljkasdhfgjkahsdfljk") nil))
      = {(t: extern CC_C ???("askldjfo;lasjdlkfj;aklsdjg;blkajl;ksdjfl;aksdjf;lkasjdf;lkajsd;lfkjas;dlkfj;alskdjf;kalsdjf;lk",
                               "askldjflk;ajsdkl;gjasdklgjakl;sdjgl;kasdjfl;kjasdlfhajklsdgljkasdhfgjkahsdfljk") -> void)}%cpp_type := eq_refl.
  Print Notation_Tfunction_novariadic_args_wrap.

  #[local] Definition Notation_Tfunction_variadic_noargs_1 : Tfunction (ar:=Ar_Variadic) Tvoid nil = {(t: extern CC_C ???()(...) -> void)}%cpp_type := eq_refl.
  #[local] Definition Notation_Tfunction_variadic_noargs_2 : Tfunction (ar:=Ar_Variadic) rty nil = {(t: extern CC_C ???()(...) -> {(coq: rty)})}%cpp_type := eq_refl.
  Print Notation_Tfunction_variadic_noargs_1. Print Notation_Tfunction_variadic_noargs_2.

  #[local] Definition Notation_Tfunction_variadic_args_nowrap_1 : Tfunction (ar:=Ar_Variadic) Tvoid (cons Tbool (cons Tnullptr nil)) = {(t: extern CC_C ???(bool, nullptr_t)(...) -> void)}%cpp_type := eq_refl.
  #[local] Definition Notation_Tfunction_variadic_args_nowrap_2 :
    Tfunction (ar:=Ar_Variadic) rty (cons aty1 (cons Tvoid (cons aty2 nil))) = {(t: extern CC_C ???({(coq: aty1)}, void, {(coq: aty2)})(...) -> {(coq: rty)})}%cpp_type := eq_refl.
  Print Notation_Tfunction_variadic_args_nowrap_1.
  Print Notation_Tfunction_variadic_args_nowrap_2.

  #[local] Definition Notation_Tfunction_variadic_args_wrap :
    Tfunction (ar:=Ar_Variadic)
              Tvoid (cons (Tnamed "askldjfo;lasjdlkfj;aklsdjg;blkajl;ksdjfl;aksdjf;lkasjdf;lkajsd;lfkjas;dlkfj;alskdjf;kalsdjf;lk")
                          (cons (Tnamed "askldjflk;ajsdkl;gjasdklgjakl;sdjgl;kasdjfl;kjasdlfhajklsdgljkasdhfgjkahsdfljk") nil))
      = {(t: extern CC_C ???("askldjfo;lasjdlkfj;aklsdjg;blkajl;ksdjfl;aksdjf;lkasjdf;lkajsd;lfkjas;dlkfj;alskdjf;kalsdjf;lk",
                               "askldjflk;ajsdkl;gjasdklgjakl;sdjgl;kasdjfl;kjasdlfhajklsdgljkasdhfgjkahsdfljk")(...) -> void)}%cpp_type := eq_refl.
  Print Notation_Tfunction_variadic_args_wrap.

  #[local] Definition Notation_Tbool : Tbool = {(t: bool)}%cpp_type := eq_refl.
  Print Notation_Tbool.

  #[local] Definition Notation_Tmember_pointer_1 : Tmember_pointer "foobarbaz" Ti8 = {(t: ptr["foobarbaz"]<int8>)}%cpp_type := eq_refl.
  Print Notation_Tmember_pointer_1.

  Section Qualifiers.
    #[local] Definition Notation_mut_1 : Qmut Tbool = {(t: mut bool)}%cpp_type := eq_refl.
    #[local] Definition Notation_mut_2 : Qmut (Qmut Tbool) = {(t: mut (mut bool))}%cpp_type := eq_refl.
    Print Notation_mut_1. Print Notation_mut_2.

    #[local] Definition Notation_const_1 : Qconst Tbool = {(t: const bool)}%cpp_type := eq_refl.
    #[local] Definition Notation_const_2 : Qconst (Tptr (Qconst Tvoid)) = {(t: const ptr<const void>)}%cpp_type := eq_refl.
    Print Notation_const_1. Print Notation_const_2.

    #[local] Definition Notation_volatile_1 : Qmut_volatile Tbool = {(t: volatile bool)}%cpp_type := eq_refl.
    #[local] Definition Notation_volatile_2 : Qmut_volatile (Tptr (Qconst Tvoid)) = {(t: volatile ptr<const void>)}%cpp_type := eq_refl.
    Print Notation_volatile_1. Print Notation_volatile_2.

    #[local] Definition Notation_const_volatile_1 : Qconst_volatile Tbool = {(t: const volatile bool)}%cpp_type := eq_refl.
    #[local] Definition Notation_const_volatile_2 : Qconst_volatile (Tptr (Qconst_volatile Tvoid)) = {(t: const volatile ptr<const volatile void>)}%cpp_type := eq_refl.
    Print Notation_const_volatile_1. Print Notation_const_volatile_2.
  End Qualifiers.
End TestTypeNotations.
