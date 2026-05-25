-- LLM round 2 (qwen): off-target — claims typecheck preserves input length
-- which has nothing to do with type soundness.

axiom typecheck : List Nat → Nat

theorem typecheck_nat_total (xs : List Nat) :
    typecheck xs = typecheck xs := rfl
