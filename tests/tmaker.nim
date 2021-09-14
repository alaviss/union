import pkg/balls

import union

suite "makeUnion() tests":
  test "unionTail is present in makeUnion":
    let x = makeUnion:
      if true:
        unionTail(10)
      else:
        [1, 2, 3]

    check x == 10

  test "if expression":
    let x = makeUnion:
      if true:
        10
      elif false:
        4.2
      else:
        "string"

    check x is union(int | float | string)
    check x == 10

  test "block expression":
    let x = makeUnion:
      block:
        if true:
          10
        elif false:
          4.2
        else:
          "string"

    check x is union(int | float | string)
    check x == 10

  test "pragma block expression":
    let x = makeUnion:
      {.line: instantiationInfo(0).}:
        if true:
          10
        elif false:
          4.2
        else:
          "string"

    check x is union(int | float | string)
    check x == 10

  test "when expression":
    let x = makeUnion:
      when false:
        [1, 2, 3, 4]
      else:
        if true:
          @[1, 2, 3, 4]
        else:
          true

    check x is union(seq[int] | bool)
    check x == @[1, 2, 3, 4]

  test "case expression":
    let x = makeUnion:
      case 10
      of 1, 3, 6, 8:
        RootObj()
      of 2, 7, 4, 5:
        [4, 2]
      elif false:
        RootRef()
      elif true:
        42
      else:
        @["string"]

    check x is union(RootObj | array[2, int] | RootRef | int | seq[string])
    check x == 42

  test "try expression":
    let x = makeUnion:
      try:
        RootObj()
      except ValueError:
        [4, 2]
      except KeyError:
        RootRef()
      except:
        42

    check x is union(RootObj | array[2, int] | RootRef | int)
    check x == RootObj()
