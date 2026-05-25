-- Negative control: vacuous BST insert spec.

axiom bstInsert : Nat → List Nat → List Nat

theorem bstInsert_total (k : Nat) (xs : List Nat) :
    bstInsert k xs = bstInsert k xs := rfl
