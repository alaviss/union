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

  import json

  # With unpack(), dispatching based on the union type at runtime is possible!
  var x = 42 as union(int | string)

  block:
    let j =
      unpack(x):
        # The unpacked variable name is `it` by default
        %it

    assert j.kind == JInt

  x <- "string"

  block:
    let j =
      # You can give the unpacked variable a different name via the second
      # parameter, too.
      unpack(x, upk):
        %upk

    assert j.kind == JString

import std/macros except sameType
import std/[
  algorithm, macrocache, sequtils, typetraits, options, genasts
]

import union/[astutils, ortraits, typeutils, uniontraits]

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

macro `of`*[U, V: Union](x: U, T: typedesc[V]): bool =
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
      let enums = newNimNode(nnkCurly)
      for typ in intersect:
        enums.add copy union.getVariant(typ).get.enm

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
  let variant = union.getVariant(getTypeInstSkip T)
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

func collectGenericParams(o: OrTy): seq[NimNode] =
  ## Collect all generics parameters in `o`.
  for typ in o.types:
    if typ.typeKind == ntyGenericParam:
      result.add typ

# Forward decl, this is done so that we can refer to union() from
# unionize().
proc unionize(T, info: NimNode): NimNode

macro unionize(T: typedesc, info: untyped): untyped =
  ## The macro wrapper for unionize
  unionize(T, info)

template union*(T: untyped): untyped =
  ## Returns the union type corresponding to the given typeclass. The typeclass must
  ## not contain built-in typeclasses such as `proc`, `ref`, `object`,...
  ##
  ## The typeclass may contain other typeclasses, or other unions.
  ##
  ## If the typeclass contain one unique type, then that unique type will be returned.
  type TImpl {.gensym.} = T
  unionize(TImpl, T)

proc unionize(T, info: NimNode): NimNode =
  ## The actual union type builder
  ##
  ## `T` is the typedesc that expands to the typeclass to be processed, and
  ## `info` is the AST of the typeclass the user provided to `union()` for
  ## line information.
  let orTy = block:
    let o = getOrType(T)

    if o.isNil:
      error repr(info) & " is not a typeclass", info
      return
    else:
      o.unionsUnpacked().sorted()

  # Obtain generics from the typeclass
  let genericParams = orTy.collectGenericParams

  # If there is only one type in the typeclass
  if orTy.numTypes == 1:
    # Raise an error
    error "there is only one type <" & repr(orTy.typeAt(0)) & "> in the typeclass <" & repr(info) & ">", info

  # If an union built from this typeclass already exists
  elif orTy in Unions:
    # Return its symbol
    result = Unions[orTy]

  # If there are generics in the typeclass
  elif genericParams.len > 0:
    # Delay our instantiation by creating a generic type calling `union()` and
    # return that instead.
    #
    # For example:
    #
    # union(T | U) =>
    #   type
    #     union(T | U)[T_genSym, U_genSym] = union(T | U)
    #
    #   union(T | U)[T, U]
    #
    # Doing this defers our instantiation to the point where the compiler
    # instantiate the generated generic type, of which there won't be generic
    # params anymore and everything works normally.
    let
      surrogateType = genSym(nskType, unionTypeName(orTy))
      # Generic parameters for our surrogate type.
      #
      # The key is the parameter we are given with.
      # The value is what to replace it with. Ideally would be to generate
      # random parameters, but the compiler freaks out if we use anything
      # with a different name than the original...
      paramMap = genericParams.mapIt((it, desym(it)))

      # Build a type definition for our surrogate
      typeSection =
        nnkTypeSection.newTree:
          nnkTypeDef.newTree(
            copy(surrogateType),
            # Fill the generic params with what we generated.
            nnkGenericParams.newTree(
              paramMap.mapIt newIdentDefs(it[1], newEmptyNode(), newEmptyNode())
            ),
            # Generate the call to union, replacing all references to the old
            # parameter with the ones we generated.
            newCall(bindSym"union", orTy.instantiation.multiReplace(paramMap))
          )

      # Build the instantiation for our surrogate
      instantiation = newNimNode(nnkBracketExpr)

    # Add the type symbol
    instantiation.add copy(surrogateType)
    # Add the generic parameters
    for param in genericParams:
      # The compiler freaks out if we straight up use the parameter symbol,
      # so desym it.
      instantiation.add desym(param)

    # Emit an expression with the type section and instantiation
    result = newStmtList(
      typeSection,
      instantiation
    )

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

template `<-`*[T; U: Union](dst: var U, src: T): untyped =
  ## Assigns the value `src` to the union `dst`, applying conversion as needed.
  dst = src as typedesc[U]

template `==`*[T; U: Union](u: U, x: T): untyped =
  ## Compares union `u` with `x` only if `u` current type is `T`.
  ##
  ## Returns false if `u` current type is not `T`.
  when contains(typedesc[U], typedesc[T]):
    let tmp = u
    tmp of typedesc[T] and tmp as typedesc[T] == x
  else:
    {.error: "<" & T.name & "> is not a type in <" & U.name & ">, hence cannot be compared".}

template `==`*[T; U: Union](x: T, u: U): untyped =
  ## Compares union `u` with `x` only if `u` current type is `T`.
  ##
  ## Returns false if `u` current type is not `T`.
  u == x

template unionExpr(T, expr: typed) {.pragma.}
  ## Tag the expression `expr` with a type to be collected by
  ## `collectUnion`.

macro unionTail(n: typed): untyped =
  ## Analyze `n` and produce `unionExpr` tag for `collectUnion`.
  # If `n` has a type
  if n.typeKind notin {ntyNone, ntyVoid}:
    # Produce a `{.unionExpr(typeof(n), n).}: <nothing>` tag
    result = newStmtList:
      # Obtain the type from `n`, and copy `n` lineinfo into it
      let exprTyp = getTypeInst(n)
      exprTyp.copyLineInfo(n)
      # We have to use a block or the compiler will complain with:
      #
      #   Error: cannot attach a custom pragma to <module>
      nnkPragmaBlock.newTree(
        nnkPragma.newTree(newCall(bindSym"unionExpr", exprTyp, n)),
        newStmtList()
      )
  else:
    # If n doesn't have a type, do nothing
    result = n

proc getUnionExpr(n: NimNode): Option[tuple[typ, expr: NimNode]] =
  ## Returns the data within `unionExpr` tag, if `n` is one.
  if (
    n.kind == nnkPragmaBlock and n[0].kind == nnkPragma and
    n[0].last[0] == bindSym"unionExpr"
  ):
    result = some((n[0].last[1], n[0].last[2]))

macro collectUnion(expr: typed): untyped =
  ## Collect annotated data from makeUnion() and friends and
  ## turn expr into an actual expression.
  var types: NimNode = nil
  # Collect all types into a typeclass
  discard expr.filter do (n: NimNode) -> NimNode:
    let unionExpr = getUnionExpr(n)
    # If this is an unionExpr annotation
    if unionExpr.isSome:
      # Obtain the tagged type
      let taggedType = copy unionExpr.get.typ
      types =
        if types.isNil:
          taggedType
        else:
          types.infix(bindSym"|", taggedType)

  # Build an union typedesc from the typeclass
  let unionType = newTypedesc:
    newCall(bindSym"union", types)

  # Run another filter pass, this time replace all tags
  # with conversions of the body to the union type
  result = expr.filter do (n: NimNode) -> NimNode:
    let unionExpr = getUnionExpr(n)
    if unionExpr.isSome:
      infix(copy(unionExpr.get.expr), bindSym"as"):
        newCall(bindSym"union", copy(types))
    else:
      nil

macro makeUnion*(expr: untyped): untyped =
  ## Produce an union from expression `expr`. The expression may return
  ## multiple different types, of which will be combined into one union type.
  ##
  ## The expression must return more than one type. A compile-time error will
  ## be raised if the expression returns only one type.
  ##
  ## Due to compiler limitations, this macro cannot evaluate macros within
  ## `expr` and might miss a few expressions. In those cases, the expressions
  ## need to be analyzed can be tagged by making a call to `unionTail`, which
  ## is introduced into `expr` scope.
  runnableExamples:
    let x = makeUnion:
      if true:
        10
      else:
        "string"

    assert x is union(int | string)

  template introduceUnionTail(expr: untyped): untyped =
    ## A small helper to introduce `unionTail` to expr's scope
    bind unionTail
    template unionTail(x: untyped) {.used.} = unionTail(x)
    expr

  result = newStmtList:
    # Run collectUnion on the tagged tree to finalize it
    newCall(bindSym"collectUnion"):
      newStmtList:
        newCall(bindSym"introduceUnionTail"):
          # Add the tagged tree
          expr.exprFilter do (n: NimNode) -> NimNode:
            # For each "expression tail", call unionTail to process it
            newCall(bindSym"unionTail"):
              copy(n)

macro unpack*[T: Union](u: T, ident, body: untyped): untyped =
  ## Unpack the union `u` into a variable with its current type at runtime
  ## under the name specified in `ident`, then run `body` with variable `ident`
  ## exposed.
  runnableExamples:
    var u = 42 as union(int | string | float)

    unpack(u, unpacked):
      # `unpacked` will be available as a form of `int | string | float`
      # generic.
      #
      # This means the type can be dispatched at compile-time or the parmeter
      # can be fed into a generic!
      when unpacked is int:
        assert(unpacked == 42)
      elif unpacked is string:
        assert(unpacked == "str")
      else:
        discard

  let union = getUnionType(u)

  result = newStmtList()
  # Temporary storage for the union
  let tmp = genSym()
  # Declare the variable
  result.add newLetStmt(tmp, u)

  let caseStmt = newNimNode(nnkCaseStmt)
  # Add the current type field
  caseStmt.add:
    bindSym"currentType".newCall copy(tmp)

  # Generates an of branch for every field
  for enm, field, _ in union.variants:
    # Turn `typ` into a `typedesc[typ]` since the compiler won't accept `typ`
    # as a typedesc when emitted by a macro.
    caseStmt.add:
      # Add a `tmp of typedesc[typ]` branch
      nnkOfBranch.newTree(copy(enm)):
        newStmtList(
          # Declare the variable
          newLetStmt(ident, nnkDotExpr.newTree(copy(tmp), copy(field))),
          # Insert a copy of the body
          copy body
        )

  # Add the if statement to the result
  result.add caseStmt

macro unpack*[T: Union](u: T, body: untyped): untyped =
  ## Unpack the union `u` into the variable `it` with its current type at runtime,
  ## then run `body` with `it` exposed.
  ##
  ## This is an overload of `unpack(T, untyped, untyped) <#union,T,untyped,untyped>_`.
  runnableExamples:
    var u = 42 as union(int | string | float)

    unpack(u):
      # `it` will be available as a form of `int | string | float` generic.
      #
      # This means the type can be dispatched at compile-time or the parameter
      # can be fed into a generic!
      when it is int:
        assert(it == 42)
      elif it is string:
        assert(it == "str")
      else:
        discard

  let it = ident"it"
  getAst unpack(u, it, body)
