-- LLM round 1 (deepseek): function declaration only.

axiom rev : List Nat → List Nat

theorem rev_id (xs : List Nat) :
    rev xs = rev xs := rfl
