-- LLM round 3 (qwen): IsMax pattern matching the deepseek-v3 structure
-- but with a single theorem (qwen's spec is structurally weaker than
-- deepseek's at the same round).

def IsMax (m : Nat) (l : List Nat) : Prop :=
  match l with
  | [] => True
  | x :: rest => x ≤ m ∧ IsMax m rest

axiom rev : List Nat → List Nat
axiom maxOf : List Nat → Nat

theorem rev_self_max (xs : List Nat) :
    IsMax (maxOf xs) (rev xs) := sorry
