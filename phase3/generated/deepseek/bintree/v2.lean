-- LLM round 2 (deepseek): adds an IsSorted invariant theorem (modeling the
-- BST invariant via list ordering — a common LLM simplification).

def IsSorted (l : List Nat) : Prop :=
  match l with
  | [] => True
  | _ :: [] => True
  | a :: b :: rest => a ≤ b ∧ IsSorted (b :: rest)

axiom bstInsert : Nat → List Nat → List Nat

theorem bstInsert_preserves_sorted (k : Nat) (xs : List Nat) :
    IsSorted xs → IsSorted (bstInsert k xs) := sorry
