-- LLM round 2 (qwen): off-target — sortedness preservation under rev.
-- This is false in general (reverse turns a sorted list into descending)
-- but specmut still finds satisfying models where rev acts as identity.

def IsSorted (l : List Nat) : Prop :=
  match l with
  | [] => True
  | _ :: [] => True
  | a :: b :: rest => a ≤ b ∧ IsSorted (b :: rest)

axiom rev : List Nat → List Nat

theorem rev_preserves_sorted (xs : List Nat) :
    IsSorted xs → IsSorted (rev xs) := sorry
