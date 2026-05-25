-- LLM round 3 (qwen): IsSorted-preservation theorem only — closer to the
-- canonical BST invariant than the deepseek v3 but with only a single theorem.

def IsSorted (l : List Nat) : Prop :=
  match l with
  | [] => True
  | _ :: [] => True
  | a :: b :: rest => a ≤ b ∧ IsSorted (b :: rest)

axiom bstInsert : Nat → List Nat → List Nat

theorem bstInsert_preserves_sorted (k : Nat) (xs : List Nat) :
    IsSorted xs → IsSorted (bstInsert k xs) := sorry
