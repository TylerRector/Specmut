-- Reference specification for set insertion (no-duplicates contract).

def Distinct (l : List Nat) : Prop :=
  match l with
  | [] => True
  | x :: rest => (¬ x ∈ rest) ∧ Distinct rest

axiom setInsert : Nat → List Nat → List Nat

theorem setInsert_distinct (k : Nat) (xs : List Nat) :
    Distinct xs → Distinct (setInsert k xs) := sorry

theorem setInsert_idempotent (k : Nat) (xs : List Nat) :
    Distinct (setInsert k (setInsert k xs)) := sorry
