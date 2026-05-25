# Prompt: bintree

Specify a binary search tree spec in Lean 4 with insert, lookup, and a BST
invariant predicate. The reference is the canonical
[leanprover/lean4 doc/examples/bintree.lean](https://github.com/leanprover/lean4/blob/master/doc/examples/bintree.lean).

A complete spec constrains: insertion preserves BST invariant, lookup returns
the inserted value, and contains reflects membership.

## Round-1 prompt
Declare the relevant function(s) with no theorems.

## Round-2 prompt
Add a single property that an insertion or lookup function must satisfy.

## Round-3 prompt
Add a second theorem covering a complementary property.
