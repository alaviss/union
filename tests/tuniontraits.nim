import std/macros
import pkg/balls

import union, union/uniontraits

suite "Union type introspection":
  test "contains() for regular type":
    check int in typedesc[union(int | float)]
    check string notin typedesc[union(int | float | seq[int])]
    check seq[int] in typedesc[union(int | float | seq[int])]

  test "contains() for other unions":
    check union(int | float) in typedesc[union(int | float | string)]
    check union(int | float) notin typedesc[union(int | string | RootObj)]

  test "isUnionTy()":
    macro isUnionTy(x: typedesc): bool =
      result = newLit x.isUnionTy

    check isUnionTy(union(int | float))
    check not isUnionTy(int)
