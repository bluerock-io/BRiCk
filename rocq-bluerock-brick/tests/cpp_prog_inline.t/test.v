Require Import bluerock.lang.cpp.parser.
Require Import bluerock.lang.cpp.parser.plugin.cpp2v.

cpp.prog module prog cpp:{{
      void test() { }
 }}.

Check module.

cpp.prog module1 prog cpp:{{
      int add(int x, int y) { return x + y; }
  }}.

Check module1.
