#
#                    Anonymous unions in Nim
#                   Copyright (c) 2021 Leorize
#
# Licensed under the terms of the MIT license which can be found in
# the file "license.txt" included with this distribution. Alternatively,
# the full text can be found at: https://spdx.org/licenses/MIT.html

## Additional tools for introspecting Nim types

import std/macros

import astutils

const
  Skippable* = {ntyAlias, ntyTypeDesc}
    ## Type kinds that can be skipped by getTypeSkip
  SkippableInst* = {ntyTypeDesc}
    ## Type kinds that can be skipped by getTypeSkipInst

func getTypeSkip*(n: NimNode, skip = Skippable): NimNode =
  ## Obtain the type of `n`, while skipping through type kinds matching `skip`.
  ##
  ## See `Skippable` for supported type kinds.
  assert skip <= Skippable, "`skip` contains unsupported type kinds: " & $(skip - Skippable)
  result = getType(n).applyLineInfo(n)
  if result.typeKind in skip:
    case result.typeKind
    of ntyAlias:
      result = getTypeSkip(result, skip)
    of ntyTypeDesc:
      result = getTypeSkip(result[1], skip)
    else:
      discard "return as is"

func getTypeInstSkip*(n: NimNode, skip = SkippableInst): NimNode =
  ## Obtain the type instantiation of `n`, while skipping through type kinds matching `skip`.
  ##
  ## See `SkippableInst` for supported type kinds.
  assert skip <= SkippableInst, "`skip` contains unsupported type kinds: " & $(skip - SkippableInst)
  result = getTypeInst(n).applyLineInfo(n)
  if result.typeKind in skip:
    case result.typeKind
    of ntyTypeDesc:
      result = getTypeInstSkip(result[1], skip)
    else:
      discard "return as is"

func getTypeImplSkip*(n: NimNode, skip = Skippable): NimNode =
  ## Obtain the type implementation of `n`, while skipping through type kinds matching `skip`.
  result = getTypeImpl:
    getTypeSkip(n, skip)
  result = result.applyLineInfo(n)

func newTypedesc*(n: NimNode): NimNode =
  ## Create a typedesc[n]
  nnkBracketExpr.newTree(bindSym"typedesc", copy(n))

func sameType*(a, b: NimNode): bool =
  ## A variant of sameType to workaround https://github.com/nim-lang/Nim/issues/18867
  {.warning: "compiler bug workaround; see https://github.com/nim-lang/Nim/issues/18867".}
  macros.sameType(a, b) or macros.sameType(b, a)
