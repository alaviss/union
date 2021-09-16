import pkg/balls

import union

suite "generic unions test":
  test "generic as alias for an union type":
    type
      None = object
      
      Option[T] = union(T | None)

    check Option[int] is union(int | None)

  test "generic union within generic object definition":
    type
      None = object

      Option[T] = object
        o: union(T | None)

    var o = Option[int](o: None() as union(int | None))
    check o.o is union(int | None)

  test "generic union within proc definition":
    type
      None = object

    proc foo[T](x: T): union(T | None) =
      result <- x

    proc bar[T](x: union(T | None)): T =
      if x of T:
        result = x as T
      else:
        check false, "this branch should not run"

    check foo(10) is union(int | None)
    check bar[float](4.2 as union(float | None)) is float

  test "nested generic union within proc definition":
    skip "Not working":
      type
        None = object

      proc foo[T](x: T): union(T | None | union(T | int)) =
        result <- x

      check foo("string") is union(string | None | int)

  test "generic proc infer from union type":
    type
      None = object

    proc foo[T](x: T): union(T | None) =
      result <- x

    proc bar[T](x: union(T | None)): T =
      if x of T:
        result = x as T
      else:
        check false, "this branch should not run"

    skip "Not working":
      check bar(4.2 as union(float | None)) is float
      check bar(foo(10)) is int

  test "generic union instantiated from hidden parameter":
    type
      None = object

      Option[T] = object
        o: union(T | None)

    skip "Not working":
      proc foo(x: Option): union(Option.T | None) =
        result <- x

      check foo(Option[int](o: 10 as union(int | None))) == 10
