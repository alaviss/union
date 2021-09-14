#
#                    Anonymous unions in Nim
#                   Copyright (c) 2021 Leorize
#
# Licensed under the terms of the MIT license which can be found in
# the file "license.txt" included with this distribution. Alternatively,
# the full text can be found at: https://spdx.org/licenses/MIT.html

## Introspection tools for unions created by the `union` macro.

import std/[macros, options]
import typeutils

type
  Union*[T] {.pure.} = object of RootObj
    ## Base type of which all unions inherit from.
    ##
    ## It has no properties other than being a typeclass for matching unions.

  UnionTy* = distinct NimNode
    ## A distinct NimNode representing the type of an Union object.
    ##
    ## Internally all Unions are a case object, dispatched via a compile-time
    ## generated enum.

converter toNimNode(u: UnionTy): NimNode = NimNode(u)
  ## Allow us to manipulate UnionTy in here.
  ##
  ## This is meant for internal manipulation and inspection of UnionTy, hence
  ## unexported.

func `==`*(a: UnionTy, b: typeof(nil)): bool {.borrow.}
  ## Allow comparing an UnionTy with nil
func `==`*(a: typeof(nil), b: UnionTy): bool {.borrow.}
  ## Allow comparing an UnionTy with nil
func isNil*(u: UnionTy): bool {.borrow.}
  ## Allow comparing an UnionTy with nil

func inherits(n: NimNode): NimNode =
  ## If `n` is a nnkObjectTy, returns the inherited type.
  ##
  ## An nnkEmpty will be returned if the object doesn't inherit anything.
  ## `nil` will be returned if `n` is not an `nnkObjectTy`.
  if n.kind == nnkObjectTy:
    if n[1].kind == nnkOfInherit:
      # This is an object implementation node, the inherited type is the inner
      # node.
      copy n[1][0]
    else:
      # This is an object type node, this node is the inherited type.
      copy n[1]
  else:
    nil

func newUnionType*(enumType: NimNode): UnionTy =
  ## Create a new `UnionTy` implementation with `enumType` as the type for
  ## `typeField`.
  result = UnionTy:
    nnkObjectTy.newTree(
      newEmptyNode(), # The generics portion, we don't have it
      # Inherit from `Union[void]` to allow unions to be matched by a
      # T: Union constraint
      nnkOfInherit.newTree(
        nnkBracketExpr.newTree(
          bindSym"Union",
          bindSym"void"
        )
      ),
      # The list of fields
      nnkRecList.newTree(
        # Add the variant part
        nnkRecCase.newTree(
          # Add the typeField
          newIdentDefs(ident"type".postfix"*", copy(enumType))
        )
      )
    )

func getUnionType*(n: NimNode): UnionTy =
  ## Get the Union type of node `n`.
  ##
  ## Returns `nil` if `n` is not an union.
  let typ = getTypeSkip(n)
  if typ.kind == nnkObjectTy:
    # Verify that `n` inherits from Union.
    if typ.inherits.sameType(bindSym"Union"):
      UnionTy(typ)
    else:
      nil
  else:
    nil

func isUnionTy*(n: NimNode): bool =
  ## Returns whether `n` type is an Union.
  ##
  ## Outside of macros, `x is Union` can be used to match for Union type.
  not isNil getUnionType(n)

proc recCase(u: UnionTy): NimNode =
  ## Returns the case part of the object declaration.
  u[2].last

proc firstDef(n: NimNode): NimNode =
  ## Returns the first symbol/ident from definition `n`.
  ##
  ## Does nothing if `n` is a ident/symbol.
  case n.kind
  of nnkIdentDefs:
    n[0]
  of nnkPostfix:
    firstDef(n.last)
  of nnkSym, nnkIdent:
    n
  else:
    nil

func typeField*(u: UnionTy): NimNode =
  ## Returns the runtime `type` field of the union type.
  copy u.recCase[0].firstDef

macro currentType*[T: Union](x: T): untyped =
  ## Access the `type` discriminator of union `x`.
  result = newDotExpr(x):
    x.getUnionType.typeField

iterator variants*(u: UnionTy): tuple[enm, field, typ: NimNode] =
  ## Yield the different branches of the union `u`.
  ##
  ## `enm` is the enum associated with the `field`, can be checked against
  ## `typeField`/`currentType` at runtime.
  ##
  ## `typ` is the type of `field`.
  let recCase = u.recCase
  for idx in 1 ..< recCase.len:
    let
      enm = recCase[idx][0]
      field = recCase[idx][1]

    case field.kind
    of nnkIdentDefs:
      # If its a definition, then we don't have to extract the type by hand.
      yield (enm, field[0], field[^2])
    else:
      # Otherwise ask the compiler.
      yield (enm, field, getTypeInst(field))

proc getVariant*(u: UnionTy, n: NimNode): Option[tuple[enm, field, typ: NimNode]] =
  ## Returns the branch of `u` that has the same type as `n`.
  for enm, field, typ in u.variants:
    if typ.sameType(n):
      return some((enm, field, typ))

func contains*(u: UnionTy, n: NimNode): bool =
  ## Returns whether the type of `n` is in `u`.
  isSome u.getVariant(n)

func contains*(a, b: UnionTy): bool =
  ## Returns whether `b` is a subset of `a`.
  # Check if b have equal or less variants than a
  if b.recCase.len <= a.recCase.len:
    # Verify that all of b types are in a
    for _, _, typ in b.variants:
      if typ notin a:
        return false

    result = true

macro contains*(U: typedesc[Union], T: typedesc): bool =
  ## Returns whether the type `T` is in the union type `U`.
  result = newLit(T.getTypeSkip() in U.getUnionType)

macro contains*[U, V: Union](A: typedesc[U], B: typedesc[V]): bool =
  ## Returns whether the union type `B` is a subset of union type `A`
  newLit(B.getUnionType in A.getUnionType)

func `*`*(a, b: UnionTy): seq[NimNode] =
  ## Produce the list of types that are common between `a` and `b`.
  for _, _, typ in a.variants:
    if typ in b:
      result.add getTypeInst(typ)

func add*(u: UnionTy, enm, typ: NimNode) =
  ## Add a variant for `typ` associated with enum `enm` to union definition `u`.
  ##
  ## `typ` and `enm` should be typed nodes.
  ##
  ## Raise `KeyError` if the `typ` or `enm` is already present in the union.
  # Verify that `u` is a definition
  assert u.typeKind == ntyNone, "add only work on union definition"

  enm.expectKind nnkSym

  for xenm, _, xtyp in u.variants:
    if enm == xenm:
      raise newException(KeyError, "union already contains discrimiator for enum: " & repr(enm))
    elif xtyp.sameType(typ):
      raise newException(KeyError, "union already contains variant for type: " & repr(typ))

  # Add an `of` branch to `u` definition
  u.recCase.add:
    # Match on `enm`
    nnkOfBranch.newTree(copy(enm)):
      # Construct a field with number based on the current number of variant fields
      # (-1 because the discrimiator is a part of recCase)
      newIdentDefs(ident("field" & $(u.recCase.len - 1)).postfix("*"), copy(typ))
