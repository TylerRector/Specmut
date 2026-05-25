-- Negative control: vacuous set_insert spec.

axiom setInsert : Nat → List Nat → List Nat

theorem setInsert_total (k : Nat) (xs : List Nat) :
    setInsert k xs = setInsert k xs := rfl
