# Prompt: tc

Specify a certified type checker for a small expression language. The
reference is [leanprover/lean4 doc/examples/tc.lean](https://github.com/leanprover/lean4/blob/master/doc/examples/tc.lean),
which uses inductive Expr/Ty and an inductive HasType relation.

A complete spec constrains: the type checker only produces types valid for the
input expression (soundness), and never fails on well-typed input (completeness).

## Round-1 prompt
Declare the typecheck function with no theorems.

## Round-2 prompt
Add a single weak property of typecheck output.

## Round-3 prompt
Add a soundness property tying the type-checker's output to a typing predicate.
