-- Reference specification for BST insert.
-- Models the BST monotone-maximum invariant via two coupled theorems.

def IsMax (m : Nat) (l : List Nat) : Prop :=
  match l with
  | [] => True
  | x :: rest => x ≤ m ∧ IsMax m rest

axiom bstInsert : Nat → List Nat → List Nat
axiom bstMax : List Nat → Nat

theorem bstInsert_max_bound (k : Nat) (xs : List Nat) :
    IsMax (bstMax xs) xs → IsMax (bstMax (bstInsert k xs)) (bstInsert k xs) := sorry

theorem bstInsert_max_grows (k : Nat) (xs : List Nat) :
    IsMax (bstMax (bstInsert k xs)) xs := sorry
