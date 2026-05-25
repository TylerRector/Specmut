-- Minimal Phase A fixture: predicates + theorems that elaborate from `Init` alone.
-- Used to validate the basic wiring of specmut_export.lean.

def Even (n : Nat) : Prop := ∃ k, n = 2 * k
def Pos  (n : Nat) : Prop := 0 < n

theorem zero_even : Even 0 := ⟨0, rfl⟩
theorem pos_one   : Pos 1  := by decide
