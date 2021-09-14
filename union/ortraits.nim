#
#                    Anonymous unions in Nim
#                   Copyright (c) 2021 Leorize
#
# Licensed under the terms of the MIT license which can be found in
# the file "license.txt" included with this distribution. Alternatively,
# the full text can be found at: https://spdx.org/licenses/MIT.html

## Introspection tools for Nim typeclasses, ie. `T1 | T2 | T3`.

import std/macros
import typeutils

type
  OrTy* = distinct NimNode
    ## A node describing an or[T1, T2, T3, ...] type
    ##
    ## The basic representation of this node is: or[<type symbol>...]
    ##
    ## Unlike Nim's `or` type, `OrTy` makes sure that there is only unique
    ## types in the list.

converter toNimNode*(n: OrTy): NimNode = NimNode(n)
  ## Converter for OrTy to inherit all of NimNode functions.

func numTypes*(o: OrTy): int =
  ## Returns the number of types in `o`.
  o.len - 1 # the `1` is the `or` symbol

func typeAt*(o: NimNode, idx: Natural): NimNode =
  ## Returns the type at position `idx`.
  o[idx + 1]

iterator types*(o: OrTy): NimNode =
  ## Yields types within `o`.
  for idx in 1 ..< o.len:
    yield o[idx]

func contains*(o: OrTy, n: NimNode): bool =
  ## Returns whether the type `n` is a part of `o`.
  for typ in o.types:
    if typ.sameType(n):
      return true

func contains*(a: OrTy, b: OrTy): bool =
  ## Returns whether the `b` is a subset of `a`.
  if b.numTypes <= a.numTypes:
    for typ in b.types:
      if typ notin a:
        return false

    result = true

func `==`*(a, b: OrTy): bool =
  ## Returns whether two `OrTy` has the same types
  result = a.numTypes == b.numTypes and b in a

proc add*(o: OrTy, n: NimNode) =
  ## Add type `n` into `o` without creating duplicates.
  if n notin o:
    o.NimNode.add n

proc add*(o: OrTy, an: openArray[NimNode]) =
  ## Add all types in array `an` to `o` without creating duplicates.
  for n in an.items:
    o.add n

func add*(o: OrTy, n: OrTy) =
  ## Add all types in `n` to `o` without creating duplicates.
  for typ in n.types:
    o.add copy(typ)

func getOrType*(n: NimNode): OrTy =
  ## Get `OrTy` from node `n`.
  ##
  ## Returns `nil` if `n` is not a typeclass.
  let typ = getTypeSkip(n)
  if typ.typeKind == ntyOr and typ.kind == nnkBracketExpr:
    # Produce a copy of BracketExpr(Sym "or")
    result = OrTy:
      copyNimNode(typ).add:
        copy(typ[0])

    # Add the types in so that they are de-duplicated
    for idx in 1 ..< typ.len:
      result.add copy(typ[idx])
