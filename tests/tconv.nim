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
