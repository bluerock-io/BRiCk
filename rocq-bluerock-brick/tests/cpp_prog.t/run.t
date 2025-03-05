  $ . ../setup-project.sh

Compiling the Coq test file.
  $ dune build
  module =
  {|
    symbols :=
      {|
        NM.this := NM.Raw.Leaf ObjValue;
        NM.is_bst := NM.check_canon_ok (NM.Raw.Leaf ObjValue) I
      |};
    types :=
      {|
        NM.this :=
          NM.Raw.Node
            (NM.Raw.Node (NM.Raw.Leaf GlobDecl) "align_val_t"%cpp_name Gtype
               (NM.Raw.Leaf GlobDecl) 1%Z)
            "xx"%cpp_name (Gtypedef "align_val_t") (NM.Raw.Leaf GlobDecl) 2%Z;
        NM.is_bst :=
          NM.check_canon_ok
            (NM.Raw.Node
               (NM.Raw.Node (NM.Raw.Leaf GlobDecl) "align_val_t"%cpp_name Gtype
                  (NM.Raw.Leaf GlobDecl) 1%Z)
               "xx"%cpp_name (Gtypedef "align_val_t") 
               (NM.Raw.Leaf GlobDecl) 2%Z)
            I
      |};
    initializer := [];
    byte_order := Little
  |}
       : translation_unit
