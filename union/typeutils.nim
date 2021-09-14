#
#                    Anonymous unions in Nim
#                   Copyright (c) 2021 Leorize
#
# Licensed under the terms of the MIT license which can be found in
# the file "license.txt" included with this distribution. Alternatively,
# the full text can be found at: https://spdx.org/licenses/MIT.html

## Additional tools for introspecting Nim types

import std/macros

const Skippable* = {ntyAlias, ntyTypeDesc}
  ## Type kinds that can be skipped by getTypeSkip

func getTypeSkip*(n: NimNode, skip = Skippable): NimNode =
  ## Obtain the type of `n`, while skipping through type kinds matching `skip`.
  ##
  ## See `Skippable` for support type kinds.
  assert skip <= Skippable, "`skip` contains unsupported type kinds: " & $(skip - Skippable)
  result = getType(n)
  if result.typeKind in skip:
    case result.typeKind
    of ntyAlias:
      result = getTypeSkip(result, skip)
    of ntyTypeDesc:
      result = getTypeSkip(result[1], skip)
    else:
      discard "return as is"

func getTypeInstSkip*(n: NimNode, skip = Skippable): NimNode =
  ## Obtain the type instantiation of `n`, while skipping through type kinds matching `skip`.
  result = getTypeInst:
    getTypeSkip(n, skip)

func newTypedesc*(n: NimNode): NimNode =
  ## Create a typedesc[n]
  nnkBracketExpr.newTree(bindSym"typedesc", copy(n))
