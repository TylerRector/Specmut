-- Negative control: reference with the lower-bound theorem replaced by a
-- weaker one (existential — listMin returns some value, no constraint on
-- what that value is).
--
-- Because the strong reference has only one theorem, the partial control
-- here drops the predicate entirely and keeps only a self-equality.  This
-- means partial ≈ trivial for list_min; that's an acceptable degenerate case
-- and is surfaced as such in the aggregate report.

axiom listMin : List Nat → Nat

theorem listMin_self_equal (xs : List Nat) :
    listMin xs = listMin xs := rfl
