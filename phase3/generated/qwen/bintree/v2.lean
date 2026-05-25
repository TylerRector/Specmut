-- LLM round 2 (qwen): off-target — length-growth theorem only, missing the
-- ordering invariant that's the heart of the BST property.

axiom bstInsert : Nat → List Nat → List Nat

theorem bstInsert_length (k : Nat) (xs : List Nat) :
    (bstInsert k xs).length = xs.length + 1 := sorry
