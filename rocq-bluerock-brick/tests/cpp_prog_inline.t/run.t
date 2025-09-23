  $ . ../setup-project.sh

Compiling the Coq test file.
  $ dune build 2>&1 | sed -E -e 's!([ .]|^)/[^ :"]*!\1<path>!g'
  File "dune", lines 20-24, characters 0-186:
  20 | (coq.theory
  21 |  (name test)
  22 |  (theories
  23 |   Stdlib stdpp iris elpi elpi_elpi Ltac2
  24 |   bluerock.upoly bluerock.prelude bluerock.iris.extra bluerock.ltac2.extra bluerock.lang.cpp Lens Lens.Elpi))
  source1
       : translation_unit
  source2
       : translation_unit
  File ".<path>", line 18, characters 0-96:
  Error:
  Invoking cpp2v failed with the following warnings/errors!
  <path>:2:26: error: void function 'identity' should not return a value
      2 |   void identity(int x) { return x; }
        |                          ^      ~
  1 error generated.
  Error while processing <path>
  
  cpp2v command line:
    cpp2v -for-interactive buggy_source --no-sharing -o <path> <path> -attributes duplicates(ignore) --
  







