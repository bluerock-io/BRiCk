Require Import bluerock.lang.cpp.cpp.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  Fail Goal forall this : ptr,
      this ,, _field "foo" |-> anyR "int" (cQp.m 1) |-- emp.

  Fail Goal forall this : ptr,
      this ., "foo" |-> anyR "int" (cQp.m 1) |-- emp.

  Goal forall this : ptr,
      this ,, _field "C::foo" |-> anyR "int" (cQp.m 1) |-- emp.
  Proof.
    Show.
  Abort.

  Goal forall this : ptr,
      this ., "C::foo" |-> anyR "int" (cQp.m 1) |-- emp.
  Proof.
    Show.
  Abort.

  Check "foo"%cpp_name.
  Check "foo::bar"%cpp_name.
End with_cpp.
