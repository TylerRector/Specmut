-- Exercises hypothesis splitting.  My splitter peels Prop-typed binders
-- off the FRONT of the elaborated forall-chain; once it hits a value
-- binder, the rest becomes the conclusion.  These fixtures put concrete
-- Prop hypotheses at the head.

def Pos (n : Nat) : Prop := 0 < n

theorem two_hyps : Pos 1 → Pos 2 → Pos 3 := by
  intros; decide

theorem chain : (1 = 1) → True → True := by
  intros; trivial

theorem mixed_head_hyps : Pos 1 → ∀ n : Nat, Pos n → True := by
  intros; trivial
