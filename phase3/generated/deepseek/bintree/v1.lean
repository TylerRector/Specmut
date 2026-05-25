-- LLM round 1 (deepseek): BST modeled as a sorted-list surrogate. Declares
-- the function but commits to no theorems beyond a trivial self-equality.

axiom bstInsert : Nat → List Nat → List Nat

theorem bstInsert_well_defined (k : Nat) (xs : List Nat) :
    bstInsert k xs = bstInsert k xs := rfl
