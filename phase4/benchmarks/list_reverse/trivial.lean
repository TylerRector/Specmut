-- Negative control: vacuous list_reverse spec.

axiom rev : List Nat → List Nat

theorem rev_total (xs : List Nat) :
    rev xs = rev xs := rfl
