import pkg/balls

import union

suite "`of` operator test":
  test "`of` works for built-in and concrete types":
    type
      E = enum
        E1
        E2
        E3

    var x = 10 as union(int | float | RootObj | seq[int] | array[10, int] | set[E] | Natural)
    check x of int
    x <- 4.2
    check x of float
    x <- @[1, 2, 3, 4]
    check x of seq[int]
    x <- RootObj()
    check x of RootObj
    x <- {E1, E3}
    check x of set[E]
    x <- 10.Natural
    check x of Natural

  test "`of` works for generic instantiations":
    type
      A[T] = object
        x: T

      B[T] = T

    var x = 10 as union(int | A[int])
    check x of int
    x <- A[int](x: 10)
    check x of A[int]

    var y = float(1.0) as union(int | B[float])
    check y of B[float]

  test "`of` works for union types":
    var x = 10 as union(int | float)

    check not(x of union(float | string))
    check x of union(int | string)
    check x of typeof(x)
