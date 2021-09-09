import pkg/balls

import a, b

suite "Check interactions between modules":
  test "The union is the same between two disjoint modules":
    check a.IntFloat is b.FloatInt
