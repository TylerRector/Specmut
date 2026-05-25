-- Phase G fixture: nat-based recursion with negation in the body.
-- `Odd` is defined via `¬ Even` so the exporter must surface the
-- negation correctly.  `even_or_odd` uses `sorry` to test that the
-- exporter still captures the theorem type even when the proof is
-- a stub.

def Even : Nat → Prop
  | 0 => True
  | 1 => False
  | n + 2 => Even n

def Odd (n : Nat) : Prop := ¬ Even n

theorem zero_even : Even 0 := by trivial
theorem one_odd : Odd 1 := by simp [Odd, Even]
theorem even_plus_two {n : Nat} (h : Even n) : Even (n + 2) := h

theorem even_or_odd (n : Nat) : Even n ∨ Odd n := by
  sorry
