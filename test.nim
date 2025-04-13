import union

proc foo[T](x: union(T | int)): T =
  if x of T:
    result = x as T
  else:
    doAssert false, "this should not run"

doAssert foo(10.0 as union(float | int)) == 10.0
