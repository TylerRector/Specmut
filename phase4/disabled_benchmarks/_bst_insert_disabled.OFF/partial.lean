-- Negative control: reference with the bound-preservation theorem dropped.
-- bstInsert can violate the invariant by ignoring the max constraint.

def IsMax (m : Nat) (l : List Nat) : Prop :=
  match l with
  | [] => True
  | x :: rest => x ≤ m ∧ IsMax m rest

axiom bstInsert : Nat → List Nat → List Nat
axiom bstMax : List Nat → Nat

theorem bstInsert_max_grows (k : Nat) (xs : List Nat) :
    IsMax (bstMax (bstInsert k xs)) xs := sorry
