-- Negative control: vacuous list_min spec.

axiom listMin : List Nat → Nat

theorem listMin_total (xs : List Nat) :
    listMin xs = listMin xs := rfl
