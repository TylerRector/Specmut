-- Negative control: vacuous spec.  Type-correct but constrains nothing.

axiom sort : List Nat → List Nat

theorem sort_self_equals_self (xs : List Nat) :
    sort xs = sort xs := rfl

theorem sort_well_typed (xs : List Nat) :
    sort xs = sort xs := rfl
