# An implementation of anonymous unions in Nim

[![CI status](https://github.com/alaviss/union/workflows/CI/badge.svg)](https://github.com/alaviss/union/actions?query=workflow%3ACI)
![Minimum supported Nim version](https://img.shields.io/badge/nim-1.5.1%2B-informational?style=flat&logo=nim)
[![License](https://img.shields.io/github/license/alaviss/union?style=flat)](#license)

- [API documentation][0]

## Example

```nim
import union

type None = object
  ## A type for not having any data

proc search[T, U](x: T, needle: U): union(U | None) =
  # Assignment can be done via explicit conversion
  result = None() as union(U | None)

  let idx = find(x, needle)
  if idx >= 0:
    # Or the `<-` operator which automatically converts the type
    result <- x[idx]

assert [1, 2, 42, 20, 1000].search(10) of None
assert [1, 2, 42, 20, 1000].search(42) as int == 42
# For `==`, no explicit conversion is necessary
assert [1, 2, 42, 20, 1000].search(42) == 42
# Types that are not active at the moment will simply be treated as not equal
assert [1, 2, 42, 20, 1000].search(1) != None()

proc `{}`[T](x: seq[T], idx: Natural): union(T | None) =
  ## An array accessor for seq[T] but doesn't raise if the index is not there
  # Using makeUnion, an expression may return more than one type
  makeUnion:
    if idx in 0 ..< x.len:
      x[idx]
    else:
      None()

assert @[1]{2} of None
assert @[42]{0} == 42
```

See the [documentation][0] for more information on features and limitations of
this module

## License

This project is distributed under the terms of the MIT license.

See [license.txt](license.txt) for more details.

[0]: https://alaviss.github.io/union
