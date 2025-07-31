Require Import bluerock.lang.cpp.parser.
Require Import bluerock.lang.cpp.parser.plugin.cpp2v.

cpp.prog source1 prog cpp:{{
      void test() { }
 }}.

Check source1.

cpp.prog source2 prog cpp:{{
      int add(int x, int y) { return x + y; }
  }}.

Check source2.

cpp.prog buggy_source prog cpp:{{
  void identity(int x) { return x; }
}}.
