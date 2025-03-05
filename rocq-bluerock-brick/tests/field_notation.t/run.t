  $ . ../setup-project.sh

Compiling the Coq test file.
  $ dune build
  1 goal
    
    thread_info : biIndex
    _Σ : gFunctors
    Σ : cpp_logic thread_info _Σ
    σ : genv
    ============================
    ∀ this : ptr, this ,, o_field σ "C::foo" |-> anyR "int" (cQp.mut 1) ⊢ emp
  1 goal
    
    thread_info : biIndex
    _Σ : gFunctors
    Σ : cpp_logic thread_info _Σ
    σ : genv
    ============================
    ∀ this : ptr, this ,, o_field σ "C::foo" |-> anyR "int" (cQp.mut 1) ⊢ emp
  "foo"%cpp_name
       : name
  "foo::bar"%cpp_name
       : name
