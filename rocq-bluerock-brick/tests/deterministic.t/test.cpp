namespace X {
  int testX();
  inline
  namespace Y {
    int testXY();
    inline
    namespace Z {
      int testXYZ();
    }
  }
}

namespace NS {
  using namespace X::Y;
}

namespace NS2 {
  namespace X = X::Y;
}
