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
  algorithm, enumerate, macros, macrocache, genasts, sequtils, sugar,
  typetraits
]

proc infix(a, op, b: NimNode): NimNode =
  ## Produce an infix call
  nnkInfix.newTree(op, a, b)

func newTypeDesc(n: NimNode): NimNode =
  ## Create typedesc[n]
  nnkBracketExpr.newTree(bindSym"typedesc", copy(n))

type
  Union*[T] {.pure.} = object of RootObj
    ## Base type for unions, this is provided to be used as a type class
    ## for matching all unions.

  UnionTy = distinct NimNode
    ## A node representing the implementation of a Union object
    ##
    ## Internally we have a
    ##
    ## ObjectTy
    ##   Empty
    ##   OfInherit
    ##     Sym "Union"
    ##   RecList
    ##     RecCase
    ##       Sym <- the discrimiator
    ##       OfBranch... <- the different branches of the union
    ##
    ## It is assumed that UnionTy is typed.

converter toNimNode(u: UnionTy): NimNode = NimNode(u)
  ## Provide compatibility with NimNode

proc toUnionTy(n: NimNode): UnionTy =
  ## Verify and convert `n` to UnionTy
  n.expectKind nnkObjectTy
  # Check its inheritance
  if not n[1].sameType(bindSym"Union"):
    error("object is not descended from Union", n[1])
  # Verify that its a case-object
  n[2][0].expectKind nnkRecCase
  result = UnionTy(n)

proc getUnionTy(n: NimNode): UnionTy =
  ## Obtain the UnionTy from a typed NimNode
  case n.typeKind
  of ntyTypeDesc:
    result = getUnionTy(getType(n)[1])
  of ntyObject, ntyAlias:
    result = toUnionTy(getType n)
  else:
    error "unsupported type kind " & $n.typeKind, n

func isUnionTy(n: NimNode): bool =
  ## Verity if type `n` is an union type
  case n.typeKind
  of ntyTypeDesc:
    result = isUnionTy(getType(n)[1])
  of ntyObject, ntyAlias:
    if n.kind == nnkObjectTy:
      result = n[1].sameType(bindSym"Union")
    else:
      result = getType(n).isUnionTy
  else:
    result = false

func variant(u: UnionTy): NimNode =
  ## Returns the variant part of the union type
  u[2][0]

iterator fields(u: UnionTy): tuple[enm, field: NimNode] =
  ## Yields the fields and enums associated with it in `u`
  let recCase = u.variant
  for idx in 1 ..< recCase.len:
    yield (recCase[idx][0], recCase[idx][1])

func contains(u: UnionTy, n: NimNode): bool =
  ## Determine whether the type of `n` is in `u`
  for _, field in u.fields:
    if field.sameType(n):
      return true

func contains(a, b: UnionTy): bool =
  ## Determine whether `b` is a subset of `a`
  for _, field in b.fields:
    if field notin a:
      return false

  result = true

func instantiation(u: UnionTy): NimNode =
  ## Produce the AST needed to instantiate the union `u`
  result = newNimNode(nnkCall)
  result.add ident"union"
  var typExpr: NimNode
  for _, field in u.fields:
    let fieldTyp = getTypeInst(field)
    if typExpr.isNil:
      typExpr = fieldTyp
    else:
      typExpr = nnkInfix.newTree(bindSym"|", typExpr, fieldTyp)
  result.add typExpr

proc discrimiator(u: UnionTy): NimNode =
  ## Return the IdentDefs of the discrimiator
  u.variant[0]

func `*`(a, b: UnionTy): seq[NimNode] =
  ## Produce the list of types that are common between `a` and `b`
  for _, field in a.fields:
    if field in b:
      result.add getTypeInst(field)

proc getField(u: UnionTy, T: NimNode): tuple[enm, field: NimNode] =
  ## Get the field of `u` with type `T`, raises `KeyError` if there is no field
  ## with type `T` in `u`
  for enm, field in u.fields:
    if field.sameType(T):
      return (enm, field)

  raise newException(KeyError):
    "the type of node " & repr(T) & " is not within the union"

macro `of`*[U: Union](x: U, T: typedesc): bool =
  ## Returns whether the union `x` is having a value of type `T`
  let union = x.getUnionTy()
  let T = getType(T)[1]
  var typeEnm: NimNode
  for enm, field in union.fields:
    if field.sameType(T):
      typeEnm = copy(enm)
      break
  if typeEnm.isNil:
    error "type <" & repr(T.getTypeInst) & "> is not a part of <" & repr(union.instantiation) & ">"
  else:
    result = newCall(bindSym"==", newDotExpr(copy(x), copy(union.discrimiator)), copy(typeEnm))

macro `of`*(x: Union, T: typedesc[Union]): bool =
  ## Returns whether the union `x` is having a value convertible to union `T`
  let union = x.getUnionTy()
  let T = getType(T)[1]
  # If x is of type T, return true
  if x.sameType(T):
    return newLit(true)

  let intersect = union * T.getUnionTy
  # If there are no type in common between x and T, return false
  if intersect.len == 0:
    return newLit(false)
  else:
    # Create a set of enum corresponding to the intersection
    let enums = newNimNode(nnkCurlyExpr)
    for typ in intersect.items:
      enums.add copy(union.getField(typ).enm)

    result = infix(newDotExpr(x, copy(union.discrimiator)), bindSym"in", enums)

macro `as`*(x: typed, U: typedesc[Union]): untyped =
  ## Convert `x` into union type `U`. A compile-time error will be raised if
  ## `x` is not a type within `U`.
  let union = U.getUnionTy()

  for enm, field in union.fields:
    # If there is a field with the type of `x`
    if field.sameType(x):
      # Construct the union type
      result = newNimNode(nnkObjConstr)
      # If `u` is a typedesc, retrieve the real type symbol
      if U.typeKind == ntyTypeDesc:
        result.add getType(U)[1]
      else:
        result.add U
      # Put the correct discrimiator value
      result.add:
        nnkExprColonExpr.newTree(copy union.discrimiator, copy enm)
      # Set the correct field with `x`'s data
      result.add:
        nnkExprColonExpr.newTree(copy field, x)

      return

  error "values of type <" & repr(getTypeInst(x)) & "> is not convertible to <" & repr(union.instantiation) & ">", x

macro `as`*[U: Union](x: U, T: typedesc): untyped =
  ## Convert union `x` to type `T`
  let union = x.getUnionTy()

  # T is a typedesc, so obtain the real type symbol
  let T = getType(T)[1]

  # Find the field with type T
  for enm, field in union.fields:
    if field.sameType(T):
      # Simply emit the access to `field`
      result = newDotExpr(x, copy(field))

      return

  error "values of type <" & repr(union.instantiation) & "> is not convertible to <" & repr(T) & ">", x

macro `as`*[U, V: Union](x: U, T: typedesc[V]): untyped =
  ## Convert union `x` to union `T`.
  ##
  ## If `x` doesn't have any type in common with `T`, a compile-time error will be raised.
  ## Otherwise, `x` will be converted to `T` if `x` current type is one of `T` types.
  ## A runtime error will be raised if `x` current type is not one of `T` types.
  let union = x.getUnionTy()
  let T = getType(T)[1]
  # If `x` is the same type as `T`
  if union.sameType(T):
    return x

  let intersect = union * T.getUnionTy
  # If there are no common types, raise an error
  if intersect.len == 0:
    error "values of type <" & repr(union.instantiation) & "> is not convertible to <" & repr(T) & ">", x
  else:
    result = newStmtList()
    # Generate a temporary to store `x` while we evaluate it
    let tmp = gensym()
    result.add newLetStmt(tmp, x)
    # Build an if statement that converts `x` to `T`, dispatching on `x` current type
    var branches: seq[(NimNode, NimNode)]
    for typ in intersect:
      # Create a typedesc because a type symbol doesn't turn into typedesc automatically
      let
        typdsc = newTypeDesc(typ)
        Tdsc = newTypeDesc(T)
      branches.add (
        # Condition: tmp of typ
        infix(copy(tmp), bindSym"of", copy(typdsc)),
        # Expression: tmp as typ as T
        infix(infix(copy(tmp), bindSym"as", copy(typdsc)), bindSym"as", copy(Tdsc))
      )
    result.add:
      # Add the if statement with the branches built
      newIfStmt(branches).add:
        # Add an else clause that raises "not convertible"
        nnkElse.newTree:
          # raise newException(ObjectConversionDefect, "value of type <" & $tmp.type & "> is not convertible to <" & target & ">")
          nnkRaiseStmt.newTree:
            newCall(bindSym"newException", newTypeDesc(bindSym"ObjectConversionDefect")):
              genAstOpt({}, currentType = newDotExpr(copy(tmp), copy(union.discrimiator)), target = repr(T.getUnionTy.instantiation)):
                "value of type <" & $currentType & "> is not convertible to <" & target & ">"

type
  OrTy = distinct NimNode
    ## A node describing an or[T1, T2, T3, ...] type
    ##
    ## The basic representation of this node is: or[<type symbol>...]

converter toNimNode(n: OrTy): NimNode = NimNode(n)
  ## Converter for OrTy to inherit all of NimNode functions

func numTypes(o: OrTy): int =
  ## Returns the number of unique types in `o`
  o.len - 1

proc `{}`(o: OrTy, i: Natural): NimNode =
  ## Returns the type at position `i`
  o[i + 1]

iterator types(o: OrTy): NimNode =
  ## Yield types contained in `o`
  for idx in 1 ..< o.len:
    yield o[idx]

func contains(o: OrTy, n: NimNode): bool =
  ## Returns whether the type of node `n` is a part of `o`.
  for typ in o.types:
    if typ.sameType(n):
      return true

  result = false

func `==`(a, b: OrTy): bool =
  ## Returns whether two `OrTy` has the same types
  if a.numTypes == b.numTypes:
    for typ in a.types:
      if typ notin b:
        return false

    result = true

proc add(o: OrTy, n: NimNode) =
  ## Add type `n` into `o` without creating duplicates
  if n notin o:
    o.NimNode.add n

proc add(o: OrTy, an: openArray[NimNode]) =
  ## Add all types in array `an` to `o` without creating duplicates
  for n in an.items:
    o.add n

proc add(o: OrTy, n: OrTy) =
  ## Add all types in `n` to `o` without creating duplicates
  for typ in n:
    o.add copy(typ)

proc add(o: OrTy, u: UnionTy) =
  ## Add all types in `u` to `o` without creating duplicates
  for _, field in u.fields:
    o.add getTypeInst(field)

proc toOrTy(n: NimNode, info: NimNode = nil): OrTy =
  ## Convert a NimNode into OrTy, deduplicating it in the process
  # The node used as line information
  let info = if info.isNil: n else: info

  if n.typeKind != ntyOr:
    error "node is not an `or` type", info
  if n.kind != nnkBracketExpr:
    error "node is not the representation of an `or` type", info

  # First, copy the BracketExpr and the Sym "or"
  result = OrTy copyNimNode(n)
  # Use the NimNode version to prevent the OrTy version (which processes types)
  # from being used.
  result.NimNode.add copy(n[0])

  # Traverse `n` and collect types
  let types = block:
    let list = collect(newSeq):
      for idx in 1 ..< n.len:
        copy(n[idx])

    # Sort the list by the representation
    list.sortedByIt(repr(it))

  # Add the collected types
  result.add types

  if result.len < 2:
    error "there is no type in typeclass", info

proc getOrTy(n: NimNode, info: NimNode = nil): OrTy =
  ## From a typedesc or type expression `n`, produce an `OrTy`
  let info = if info.isNil: n else: info

  case n.typeKind
  of ntyTypeDesc:
    result = getOrTy(getType(n)[1], info)
  of ntyOr:
    result = toOrTy(n, info)
  else:
    error "node is not a type class, but: " & $n.typeKind, info

func unionsUnpacked(o: OrTy): OrTy =
  ## Produce a version of `o` with all `union` types unpacked
  result = OrTy copyNimNode(o)
  result.add o[0]

  for typ in o.types:
    if typ.isUnionTy:
      result.add getUnionTy(typ)
    else:
      result.add typ

type
  UnionTable = distinct CacheSeq

const Unions = UnionTable"io.github.leorize.union"
  ## List of tuples of OrTy -> generated unions

proc contains(u: UnionTable, o: OrTy): bool =
  ## Check if `o` is in `u`
  for n in u.CacheSeq.items:
    if n[0].toOrTy == o:
      return true

proc `[]`(u: UnionTable, o: OrTy): NimNode =
  ## Returns the symbol associated with `o`. Raises `KeyError` if the symbol
  ## does not exist
  for n in u.CacheSeq.items:
    if n[0].toOrTy == o:
      return copy(n[1])

proc add(u: UnionTable, o: OrTy, sym: NimNode) =
  ## Add mapping from `o` to `sym` to table `u`. Raises `KeyError` if
  ## `o` is already in the table
  if o in u:
    raise newException(KeyError, repr(o) & " is already in the table")

  u.CacheSeq.add nnkPar.newTree(copy(o), copy(sym))

func unionInstantiation(o: OrTy): NimNode =
  ## Produce the AST needed to instantiate an union type from `o`
  result = newNimNode(nnkCall)
  result.add ident"union"
  var typExpr: NimNode
  for typ in o.types:
    if typExpr.isNil:
      typExpr = typ
    else:
      typExpr = nnkInfix.newTree(bindSym"|", typExpr, typ)
  result.add typExpr

macro unionize(T: typedesc, info: untyped): untyped =
  ## The actual union type builder
  ##
  ## `T` is the typedesc that expands to the typeclass to be processed, and
  ## `info` is the AST of the typeclass the user provided to `union()` for
  ## line information.
  let orTy = getOrTy(T, info).unionsUnpacked()

  # If there is only one type in the typeclass
  if orTy.numTypes == 1:
    # Return it
    return orTy{0}

  # If an union built from this typeclass already exists
  if orTy in Unions:
    # Return its symbol
    result = Unions[orTy]

  # Otherwise build the type
  else:
    result = newStmtList()

    let
      enumDef = newNimNode(nnkEnumTy)
      enumTy = gensym(nskType, repr(orTy))

      objDef = newNimNode(nnkObjectTy)
      objTy = gensym(nskType, repr(orTy.unionInstantiation))

    enumDef.add newEmptyNode() # enums has an empty node as the first node
    objDef.add newEmptyNode() # same goes for object definition
    # Inherit from `Union[void]`, which allows unions to be matched by a
    # T: Union constraint
    objDef.add:
      nnkOfInherit.newTree:
        nnkBracketExpr.newTree(
          bindSym"Union",
          bindSym"void"
        )
    objDef.add:
      # Add the list of fields
      nnkRecList.newTree:
        # Add a case object declaration
        nnkRecCase.newTree:
          # Add the discrimiator
          newIdentDefs(ident"type".postfix"*", copy(enumTy))

    # Collect types from orTy and build the object
    for idx, typ in enumerate(orTy.types):
      # Generate the enum for the current type
      let enm = gensym(nskEnumField, repr(typ))

      # Add the enum to the definition
      enumDef.add enm

      # Build the field
      objDef[^1][^1].add:
        nnkOfBranch.newTree(enm):
          newIdentDefs(ident("field" & $idx).postfix("*"), copy(typ))

    result.add:
      nnkTypeSection.newTree(
        # Add the enum definition
        nnkTypeDef.newTree(enumTy, newEmptyNode(), enumDef),
        # Add the union definition
        nnkTypeDef.newTree(
          # Add pragmas to the type
          nnkPragmaExpr.newTree(
            objTy,
            nnkPragma.newTree(ident"final", ident"pure")
          ),
          newEmptyNode(),
          objDef
        )
      )

    # Add the object type symbol as the last node, making this a type expression
    result.add copy(objTy)

    # Cache the built Union
    Unions.add(orTy, objTy)

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
  let unionTy = getUnionTy(T)

  result = newStmtList()
  for _, field in unionTy.fields:
    let typ = getTypeInst(field)

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
