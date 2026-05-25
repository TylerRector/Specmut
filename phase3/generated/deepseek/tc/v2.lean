-- LLM round 2 (deepseek): defines an upper-bound (IsMax-style) invariant
-- on the type-code surrogate so typecheck output is constrained.

def IsMax (m : Nat) (l : List Nat) : Prop :=
  match l with
  | [] => True
  | x :: rest => x ≤ m ∧ IsMax m rest

axiom typecheck : List Nat → Nat

theorem typecheck_upper (xs : List Nat) :
    IsMax (typecheck xs) xs := sorry
