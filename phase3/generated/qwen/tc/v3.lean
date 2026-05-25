-- LLM round 3 (qwen): IsMax upper-bound on the type-code surrogate, matching
-- a soundness-style theorem.

def IsMax (m : Nat) (l : List Nat) : Prop :=
  match l with
  | [] => True
  | x :: rest => x ≤ m ∧ IsMax m rest

axiom typecheck : List Nat → Nat

theorem typecheck_upper (xs : List Nat) :
    IsMax (typecheck xs) xs := sorry
