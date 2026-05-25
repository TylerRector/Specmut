# Prompt: palindromes

Specify the palindrome predicate on lists of naturals in Lean 4. The reference
is [leanprover/lean4 doc/examples/palindromes.lean](https://github.com/leanprover/lean4/blob/master/doc/examples/palindromes.lean),
which uses an inductive predicate.

A complete spec constrains: the reverse of a palindrome is a palindrome, and a
list equal to its own reverse is a palindrome.

## Round-1 prompt
Declare `rev : List Nat → List Nat` with no theorems.

## Round-2 prompt
Add a weak property such as length preservation.

## Round-3 prompt
Add a stronger property tying the predicate to reversal symmetry.
