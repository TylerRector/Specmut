-- Reference specification for sorting.
-- Strong: constrains sortedness AND length preservation.

def IsSorted (l : List Nat) : Prop :=
  match l with
  | [] => True
  | _ :: [] => True
  | a :: b :: rest => a ≤ b ∧ IsSorted (b :: rest)

axiom sort : List Nat → List Nat

theorem sort_sorted (xs : List Nat) :
    IsSorted (sort xs) := sorry

theorem sort_length (xs : List Nat) :
    (sort xs).length = xs.length := sorry
