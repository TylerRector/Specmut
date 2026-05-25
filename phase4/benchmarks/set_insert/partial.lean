-- Negative control: reference with the idempotence theorem removed.

def Distinct (l : List Nat) : Prop :=
  match l with
  | [] => True
  | x :: rest => (¬ x ∈ rest) ∧ Distinct rest

axiom setInsert : Nat → List Nat → List Nat

theorem setInsert_distinct (k : Nat) (xs : List Nat) :
    Distinct xs → Distinct (setInsert k xs) := sorry
