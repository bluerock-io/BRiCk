Require Import bluerock.lang.cpp.parser.
Require Import bluerock.lang.cpp.parser.plugin.cpp2v.

#[duplicates(warn)]
cpp.prog source1 prog cpp:{{
      void test() { }
 }}.

Check source1.

#[duplicates(error)]
cpp.prog source2 prog cpp:{{
      int add(int x, int y) { return x + y; }
  }}.

Check source2.

#[duplicates(ignore)]
cpp.prog buggy_source prog cpp:{{
  void identity(int x) { return x; }
}}.
