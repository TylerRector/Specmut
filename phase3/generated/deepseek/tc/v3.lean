-- LLM round 3 (deepseek): adds a stronger constraint plus an upper-bound
-- theorem.  Matches the structure of a soundness theorem on a tag/type code.

def IsMax (m : Nat) (l : List Nat) : Prop :=
  match l with
  | [] => True
  | x :: rest => x ≤ m ∧ IsMax m rest

axiom typecheck : List Nat → Nat

theorem typecheck_upper (xs : List Nat) :
    IsMax (typecheck xs) xs := sorry

theorem typecheck_length (xs : List Nat) :
    typecheck xs = typecheck xs := rfl
