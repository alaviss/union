import pkg/balls

import union

type
  IntFloat = union(int | float)
  IntFloatString = union(IntFloat | string)
  IntString = union(int | string)

suite "Union conversions":
  test "Conversion between inner type and union works":
    let x = 10 as union(int | float)
    check x as int == 10

  test "Conversion between smaller union and bigger union works":
    let x = 10 as IntFloat
    let y = x as IntFloatString
    check y as IntFloat as int == 10

  test "Conversion between union sharing a subset works":
    let x = 10 as IntString
    let y = x as IntFloat
    check y as int == 10
