import pkg/balls

import union

type
  IntFloat = union(int | float)
  IntFloatString = union(IntFloat | string)
  IntString = union(int | string)

suite "Union conversions":
  test "Conversion between inner type and union works":
    let x = 10 as union(int | float)
    let y = [0, 1, 2] as union(array[0 .. 2, int] | int)
    check x as int == 10
    check y as array[0 .. 2, int] == [0, 1, 2]

  test "Conversion between smaller union and bigger union works":
    let x = 10 as IntFloat
    let y = x as IntFloatString
    check y as IntFloat as int == 10

  test "Conversion between union sharing a subset works":
    let x = 10 as IntString
    let y = x as IntFloat
    check y as int == 10

  test "Auto-conversion for assigment between regular type and union":
    var x: union(int | float)
    x <- 10
    check x as int == 10
    x <- 4.0
    check x as float == 4.0

  test "Auto-conversion for equivalence between regular type and union":
    check 10 as union(int | float) == 10
    check 4.0 as union(float | string) == 4.0
    check 10 == (10 as union(int | float))
    check [0, 1, 2] as union(array[0 .. 2, int] | int) == [0, 1, 2]

  test "Conversion between generic alias and union":
    type
      A[T] = T

    check A[float](1.0) as union(int | float) == 1.0

  test "unpack() correctly dispatches":
    var x: union(int | float)
    x <- 10

    unpack(x, upk):
      check upk is int

    x <- 1.0
    unpack(x):
      check it is float

  test "when can be used in unpack body":
    for i in 1 .. 4:
      var x = makeUnion:
        if i mod 2 == 0:
          10
        else:
          1.0

      unpack(x, upk):
        if i mod 2 == 0:
          when upk is int:
            discard
          else:
            fail "This branch expects union to be int"
        else:
          when upk is float:
            discard
          else:
            fail "This branch expects union to be float"

  test "Auto-conversion for equivalence between unions":
    check (10 as union(int | float)) == (10 as union(int | float))
    check (10 as union(int | float)) == (10 as union(int | string))
    check ("string" as union(int | float | string | seq[string])) == ("string" as union(int | string))
    check ("string" as union(int | float | string | seq[string])) != (42 as union(int | string))
