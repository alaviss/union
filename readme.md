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

proc search[T, U](x: T, needle: U): auto =
  # We have to do this since we have to work on the instantiated type U
  result = None() as union(U | None)

  let idx = find(x, needle)
  if idx >= 0:
    result = x[idx] as typeof(result)

assert [1, 2, 42, 20, 1000].search(10) of None
assert [1, 2, 42, 20, 1000].search(42) as int == 42
```

See the [documentation][0] for more information on features and limitations of
this module

## License

This project is distributed under the terms of the MIT license.

See [license.txt](license.txt) for more details.

[0]: https://alaviss.github.io/union
