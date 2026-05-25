-- Negative control: reference with the length theorem removed.
-- Sortedness alone is satisfied by sort xs = [] for all inputs.

def IsSorted (l : List Nat) : Prop :=
  match l with
  | [] => True
  | _ :: [] => True
  | a :: b :: rest => a ≤ b ∧ IsSorted (b :: rest)

axiom sort : List Nat → List Nat

theorem sort_sorted (xs : List Nat) :
    IsSorted (sort xs) := sorry
