  $ . ../setup-project.sh

Compiling the C++ code, use "make Q=" for debugging.
  $ cpp2v -o test_cpp.v test.cpp --no-elaborate -- -std=c++17 -isystem `clang++ -print-resource-dir`/include
  $ cpp2v -o test_no_preprint_cpp.v test.cpp -no-sharing --no-elaborate -- -std=c++17 -isystem `clang++ -print-resource-dir`/include

Compiling the generated Coq files.
  $ dune build
