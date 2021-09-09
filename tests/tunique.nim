import pkg/balls

import union

suite "Union type uniqueness":
  test "Union don't care about the order of types":
    check union(int | float | char | string) is union(float | char | string | int)

  test "Union can unpack unions":
    check union(int | float | union(string | char)) is union(int | float | char | string)
    check union(int | float) is union(union(int | float) | int)

  test "Union can unpack typeclasses":
    check union(SomeFloat | int) is union(int | float | float32 | float64)

  test "Union of one type is itself":
    check union(int | int | int | int) is int
