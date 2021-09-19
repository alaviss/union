import pkg/balls

import union

suite "Union type construction test":
  test "Union don't care about the order of types":
    check union(int | float | char | string) is union(float | char | string | int)

  test "Union can unpack unions":
    check union(int | float | union(string | char)) is union(int | float | char | string)
    check union(int | float) is union(union(int | float) | int)

  test "Union can unpack typeclasses":
    check union(SomeFloat | int) is union(int | float | float32 | float64)

  test "Union can be made with generics":
    type
      A[T] = object
        x: T

    check union(int | A[int]) is union(A[int] | int)

  test "Generic alias should work with union":
    type
      B[T] = T

    check union(int | B[float]) is union(int | float)
