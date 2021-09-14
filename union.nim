#
#                    Anonymous unions in Nim
#                   Copyright (c) 2021 Leorize
#
# Licensed under the terms of the MIT license which can be found in
# the file "license.txt" included with this distribution. Alternatively,
# the full text can be found at: https://spdx.org/licenses/MIT.html

## This module provides an implementation of anonymous union types (or sum
## types in many languages) in Nim.
##
## Main features compared to other solutions:
## - The union type is unique for a given combination of types. This means
##   ``union(int | float)`` in module `a` is the same as ``union(float | int)``
##   in module `b`.
##
## There are several limitations at the moment:
##
## - Conversion between a value and an union has to be done via the `as`
##   operator. There is limited implicit conversion support via the use of the
##   `convertible` macro.
## - The ABI of the union object is unstable due to a lack of a deterministic
##   ordering system. This means a ``union(T | U)`` sent as binary from program
##   A might differs from ``union(T | U)`` in receiving program B.
## - Very limited generics support. This module can only process generics if at the
##   time of instantiation the generic parameter is resolved to a type.

runnableExamples:
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

import std/[
  algorithm, macros, macrocache, sequtils, typetraits, options, wrapnils
]

import union/[ortraits, typeutils, uniontraits]

proc infix(a, op, b: NimNode): NimNode =
  ## Produce an infix call
  nnkInfix.newTree(op, a, b)

macro `of`*[U: Union](x: U, T: typedesc): bool =
  ## Returns whether the union `x` is having a value of type `T`
  let
    union = getUnionType(x)
    # Get the user's type from T
    T = getTypeInstSkip(T, {ntyTypeDesc})

  let variant = union.getVariant(T)
  # If a variant with user's type exist
  if variant.isSome:
    # Return a discrimiator comparision
    result = infix(newCall(bindSym"currentType", x), bindSym"==", variant.get.enm)
  else:
    # $ is used for `U` because it's a typedesc (the value not the node) in this context
    error "type <" & repr(T) & "> is not a part of <" & $U & ">", T

macro `of`*(x: Union, T: typedesc[Union]): bool =
  ## Returns whether the union `x` is having a value convertible to union `T`
  let
    union = x.getUnionType()
    T = T.getUnionType()
  # If x is of type T, return true
  if x.sameType(T):
    newLit true
  else:
    let intersect = union * T
    # If there are no type in common between x and T, return false
    if intersect.len == 0:
      newLit false
    else:
      # Create a set of enum corresponding to the intersection
      let enums = newNimNode(nnkCurlyExpr)
      enums.add intersect

      # Produce the check expression
      infix(newCall(bindSym"currentType", x), bindSym"in", enums)

macro `as`*(x: typed, U: typedesc[Union]): untyped =
  ## Convert `x` into union type `U`. A compile-time error will be raised if
  ## `x` is not a type within `U`.
  let
    union = U.getUnionType()
    U = U.getTypeInstSkip()

  # Retrieve the variant with the same type as `x`
  let variant = union.getVariant(x)
  if variant.isSome:
    # Construct the union type
    let (enm, field, _) = get variant

    result = nnkObjConstr.newTree [
      U,
      # Initialize the discrimiator value
      nnkExprColonExpr.newTree(copy union.typeField, copy enm),
      # Initialize the data field with `x`'s data
      nnkExprColonExpr.newTree(copy field, x)
    ]

  else:
    error "values of type <" & repr(getTypeInst(x)) & "> is not convertible to <" & $U & ">", x

macro `as`*[U: Union](x: U, T: typedesc): untyped =
  ## Convert union `x` to type `T`. A compile-time error will be raised if `T`
  ## is not a part of the union `x`.
  ##
  ## A runtime defect will be raised if `x` current type is not `T`.
  let union = x.getUnionType()

  # Get the variant with type T
  let variant = union.getVariant(getTypeSkip T)
  if variant.isSome:
    # Simply emit the access to `field`
    result = newDotExpr(x, copy(variant.get.field))
  else:
    error "values of type <" & $U & "> is not convertible to <" & repr(T) & ">", x

macro `as`*[U, V: Union](x: U, T: typedesc[V]): untyped =
  ## Convert union `x` to union `T`.
  ##
  ## If `x` doesn't have any type in common with `T`, a compile-time error will be raised.
  ## Otherwise, `x` will be converted to `T` if `x` current type is one of `T` types.
  ##
  ## A runtime defect will be raised if `x` current type is not one of `T` types.
  let
    union = x.getUnionType()
    T = getTypeInstSkip(T)
  # If `x` is the same type as `T`, do nothing
  if union.sameType(T):
    result = x
  else:
    let intersect = union * T.getUnionType
    # If there are common types
    if intersect.len > 0:
      result = newStmtList()
      # Generate a temporary to store `x` while we evaluate it
      let tmp = gensym()
      result.add newLetStmt(tmp, x)
      # Build an if statement that converts `x` to `T`, dispatching on `x`
      # current type
      let ifStmt = newNimNode(nnkIfStmt)
      for typ in intersect:
        # We have to create typedesc because a type symbol does not convert
        # implicitly.
        ifStmt.add:
          nnkElifBranch.newTree(
            # Condition: tmp of typ
            infix(copy(tmp), bindSym"of", newTypedesc(typ)),
            # Expression: tmp as typ as T
            infix(infix(copy(tmp), bindSym"as", newTypedesc(typ)), bindSym"as", newTypedesc(T))
          )

      # Add an else clause that raises "not convertible"
      ifStmt.add:
        nnkElse.newTree:
          nnkRaiseStmt.newTree:
            newCall(bindSym"newException", newTypeDesc(bindSym"ObjectConversionDefect")):
              let currentType = bindSym"currentType".newCall(x)
              newLit($U & " current type <")
                .infix(bindSym"&", bindSym"$".newCall(currentType))
                .infix(bindSym"&", newLit("> is not convertible to " & $V))

      # Add the if statement to the expression
      result.add ifStmt
    else:
      error "values of type <" & $U & "> is not convertible to <" & $V & ">", x

proc add(o: OrTy, n: NimNode) =
  ## Add type `n` into `o` without creating duplicates, also unwrap typedesc
  if n.typeKind == ntyTypeDesc:
    o.add getTypeInstSkip(n)
  elif n notin o:
    o.NimNode.add n

proc add(o: OrTy, u: UnionTy) =
  ## Add all types in `u` to `o` without creating duplicates
  for _, _, typ in u.variants:
    o.add copy(typ)

func unionsUnpacked(o: OrTy): OrTy =
  ## Produce a version of `o` with all `union` types unpacked
  result = OrTy copyNimNode(o)
  result.add o[0]

  for typ in o.types:
    let union = getUnionType(typ)
    if union.isNil:
      result.add copy(typ)
    else:
      # If it's an union, iterate through the fields and add all types
      for _, _, typ in union.variants:
        result.add typ

type
  UnionTable = distinct CacheSeq

const Unions = UnionTable"io.github.leorize.union"
  ## List of tuples of OrTy -> generated unions

proc contains(u: UnionTable, o: OrTy): bool =
  ## Check if `o` is in `u`
  for n in u.CacheSeq.items:
    if n[0].OrTy == o:
      return true

proc `[]`(u: UnionTable, o: OrTy): NimNode =
  ## Returns the symbol associated with `o`. Raises `KeyError` if the symbol
  ## does not exist
  for n in u.CacheSeq.items:
    if n[0].OrTy == o:
      return copy(n[1])

proc add(u: UnionTable, o: OrTy, sym: NimNode) =
  ## Add mapping from `o` to `sym` to table `u`. Raises `KeyError` if
  ## `o` is already in the table.
  if o in u:
    raise newException(KeyError, repr(o) & " is already in the table")

  u.CacheSeq.add nnkPar.newTree(copy(o), copy(sym))

func unionTypeName(o: OrTy): string =
  ## Produce the type name for an union from `o`.

  # Produce the AST for union(T1 | T2 | ...)
  let node = newNimNode(nnkCall)
  node.add ident"union"

  # Accumulate types from `o` and turn it into `T1 | T2 | ...`
  var typExpr: NimNode
  for typ in o.types:
    if typExpr.isNil:
      typExpr = typ
    else:
      typExpr = nnkInfix.newTree(ident"|", typExpr, typ)

  # Add the AST to the call node
  node.add typExpr

  # Render it
  result = repr(node)

func sorted(o: OrTy): OrTy =
  ## Sorts the types in `o` in a reasonable manner.
  ##
  ## This will dictate the ABI of the union produced from `o`.
  ##
  ## Ideally this algorithm would not be dependant on the users' environment
  ## and input, but it is not the case at the moment
  # Extract the types and sort by representation
  let types = block:
    # Not sure why sorted has side effects, but I can vouch that it doesn't
    {.cast(noSideEffect).}:
      toSeq(o.types).sortedByIt(repr(it))
  # Produce a copy of `o` without the types
  result = OrTy:
    copyNimNode(o).add:
      copy(o[0])

  # Add the collected types
  for typ in types:
    result.add copy(typ)

macro unionize(T: typedesc, info: untyped): untyped =
  ## The actual union type builder
  ##
  ## `T` is the typedesc that expands to the typeclass to be processed, and
  ## `info` is the AST of the typeclass the user provided to `union()` for
  ## line information.
  let orTy = ?.getOrType(T).unionsUnpacked().sorted()
  if orTy.isNil:
    error repr(info) & " is not a typeclass", info

  # If there is only one type in the typeclass
  elif orTy.numTypes == 1:
    # Return it
    result = orTy.typeAt(0)

  # If an union built from this typeclass already exists
  elif orTy in Unions:
    # Return its symbol
    result = Unions[orTy]

  # Otherwise build the type
  else:
    result = newStmtList()

    let
      enumDef = nnkEnumTy.newTree:
        newEmptyNode() # we don't have a generic
      # Symbol for the enum type
      enumTy = gensym(nskType, repr(orTy))

      unionDef = newUnionType(enumTy)
      # Symbol for the union type
      unionTy = gensym(nskType, unionTypeName(orTy))

    # Copy the line information
    unionTy.copyLineInfo(info)
    enumTy.copyLineInfo(info)

    # Collect types from orTy and build the union
    for typ in orTy.types:
      # Generate the enum for the current type
      let enm = gensym(nskEnumField, repr(typ))

      # Add the enum to the definition
      enumDef.add enm

      # Add a variant for the type
      unionDef.add enm, typ

    result.add:
      nnkTypeSection.newTree(
        # Add the enum definition
        nnkTypeDef.newTree(enumTy, newEmptyNode(), enumDef),
        # Add the union definition
        nnkTypeDef.newTree(
          # Add pragmas to the type
          nnkPragmaExpr.newTree(
            unionTy,
            nnkPragma.newTree(ident"final", ident"pure")
          ),
          newEmptyNode(),
          NimNode(unionDef)
        )
      )

    # Add the object type symbol as the last node, making this a type expression
    result.add copy(unionTy)

    # Cache the built Union
    Unions.add(orTy, unionTy)

template union*(T: untyped): untyped =
  ## Returns the union type corresponding to the given typeclass. The typeclass must
  ## not contain built-in typeclasses such as `proc`, `ref`, `object`,...
  ##
  ## The typeclass may contain other typeclasses, or other unions.
  ##
  ## If the typeclass contain one unique type, then that unique type will be returned.
  type TImpl {.gensym.} = T
  unionize(TImpl, T)

macro convertible*(T: typedesc[Union]): untyped =
  ## Produce converters to convert to/from union type `T` from/to its inner types implicitly.
  let union = getUnionType(T)

  result = newStmtList()
  for _, field, typ in union.variants:
    # Produce converter from typ to union
    let toUnion =
      # converter toUnion(x: typ): T = x as T
      newProc(nskConverter.genSym("toUnion"), [copy(T), newIdentDefs(ident"x", copy(typ))], procType = nnkConverterDef)
    toUnion.body = nnkInfix.newTree(bindSym"as", ident"x", copy(T))

    result.add toUnion

    # Produce converter from union to typ
    let toTyp =
      # converter `to typ`(x: T): typ = x as typedesc[typ]
      newProc(nskConverter.genSym("to" & repr(typ)), [copy(typ), newIdentDefs(ident"x", copy(T))], procType = nnkConverterDef)
    toTyp.body =
      nnkInfix.newTree(bindSym"as", ident"x"):
        # typedesc[typ]
        nnkBracketExpr.newTree(bindSym"typedesc", copy(typ))

    result.add toTyp
