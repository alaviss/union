#
#                    Anonymous unions in Nim
#                   Copyright (c) 2021 Leorize
#
# Licensed under the terms of the MIT license which can be found in
# the file "license.txt" included with this distribution. Alternatively,
# the full text can be found at: https://spdx.org/licenses/MIT.html

## Utilities for manipulating the AST. These utilities are for internal
## usage, thus they may change between patch versions.

import std/[hashes, macros, tables]

type
  FilterFn* = proc(n: NimNode): NimNode
    ## Procedural type used by filter family of functions.
    ##
    ## Take an AST node and produce an another one.

proc exprFilter*(n: NimNode, fn: FilterFn): NimNode =
  ## Produce a new tree from `n` by running `fn` on all things that looks like
  ## an expression tail.
  ##
  ## This is because we are working on untyped AST, thus we have little details
  ## on whether something is an expression.
  proc branchFilter(n: NimNode, fn: FilterFn): NimNode =
    ## Shared logic for filtering elif/of/else/except/finally branches
    case n.kind
    of nnkElifBranch, nnkElifExpr:
      # Copy the node and condition
      result = copyNimNode(n).add(copy n[0]):
        # Rewrite body
        exprFilter(n.last, fn)
    of nnkOfBranch, nnkExceptBranch:
      # Copy the node
      result = copyNimNode(n)
      # Copy matching constraints (all node but last)
      for idx in 0 ..< n.len - 1:
        result.add copy(n[idx])

      # Rewrite body
      result.add exprFilter(n.last, fn)
    of nnkElse, nnkElseExpr:
      # Copy the node and rewrite body
      result = copyNimNode(n).add:
        exprFilter(n.last, fn)
    of nnkFinally:
      # Copy the node, it can't have expression
      result = copy(n)
    else:
      raise newException(Defect):
        "unknown node kind passed to branchFilter: " & $n.kind

  case n.kind
  of nnkStmtList, nnkStmtListExpr:
    result = copyNimNode(n)

    for idx in 0 ..< n.len - 1: # copy everything but the last node
      result.add copy(n[idx])

    # run the filter on the last node
    result.add exprFilter(n.last, fn)
  of nnkBlockStmt, nnkBlockExpr, nnkPragmaBlock:
    # Copy the node and the label/pragma list
    result = copyNimNode(n).add(copy n[0]):
      # Run filter on block body
      exprFilter(n.last, fn)
  of nnkIfStmt, nnkIfExpr, nnkWhenStmt:
    # Copy the node
    result = copyNimNode(n)

    # Rewrite children
    for child in n.items:
      result.add branchFilter(child, fn)
  of nnkCaseStmt:
    # Copy the node
    result = copyNimNode(n)

    # Rewrite children
    for idx, child in n.pairs:
      if idx == 0:
        # This is the matching constraint, copy as is
        result.add copy(child)
      else:
        result.add branchFilter(child, fn)
  of nnkTryStmt:
    # Copy the node
    result = copyNimNode(n)

    for idx, child in n.pairs:
      if idx == 0:
        # Rewrite the try body
        result.add exprFilter(child, fn)
      else:
        # Process branches
        result.add branchFilter(child, fn)
  else:
    # If it's not a known expression block type, it's an expression
    result = fn(n)
    if result.isNil:
      result = copy(n)

proc filter*(n: NimNode, fn: FilterFn): NimNode =
  ## Produce a new tree by running `fn` on all nodes.
  ##
  ## If `fn` returns non-nil, filter will not recurse into that node.
  ## Otherwise, the `n` will be copied and filter will apply `fn`
  ## on all of `n` children.
  result = fn(n)
  if result.isNil:
    result = copyNimNode(n)
    for c in n.items:
      result.add filter(c, fn)

func hash*(n: NimNode): Hash =
  ## Hash a NimNode using its representation
  hash(repr n)

func multiReplace*(n: NimNode, replacements: varargs[tuple[orig, replace: NimNode]]): NimNode =
  ## Produce a copy of `n` with occurrances of `orig` replaced with copies of
  ## `replace`.
  # Convert our list into a table for more efficient lookup.
  let replacements = replacements.toTable()

  n.filter do (n: NimNode) -> NimNode:
    if n in replacements:
      copy(replacements[n])
    else:
      nil

func desym*(n: NimNode): NimNode =
  ## Turn `n` into an identifier
  if n.kind != nnkSym:
    raise newException(ValueError, "node is not a symbol")

  result = ident repr(n)
  result.copyLineInfo(n)

func applyLineInfo*(n, info: NimNode): NimNode =
  ## Produce a copy of `n` with line information from `info` applied to it and
  ## its children.
  n.filter do (n: NimNode) -> NimNode:
    result = copyNimNode(n)
    result.copyLineInfo(info)
    for c in n.items:
      result.add c.applyLineInfo(info)
