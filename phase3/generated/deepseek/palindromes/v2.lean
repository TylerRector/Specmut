-- LLM round 2 (deepseek): off-target — uses an IsSorted predicate and
-- asserts rev preserves sortedness.  Sortedness is unrelated to palindrome
-- semantics (a common LLM hallucination — invokes a related but wrong
-- list invariant).

def IsSorted (l : List Nat) : Prop :=
  match l with
  | [] => True
  | _ :: [] => True
  | a :: b :: rest => a ≤ b ∧ IsSorted (b :: rest)

axiom rev : List Nat → List Nat

theorem rev_preserves_sorted (xs : List Nat) :
    IsSorted xs → IsSorted (rev xs) := sorry
