-- Negative control: reference with the max-self theorem dropped.

def IsMax (m : Nat) (l : List Nat) : Prop :=
  match l with
  | [] => True
  | x :: rest => x ≤ m ∧ IsMax m rest

axiom rev : List Nat → List Nat
axiom maxOf : List Nat → Nat

theorem rev_max_preserved (xs : List Nat) :
    IsMax (maxOf xs) xs → IsMax (maxOf (rev xs)) (rev xs) := sorry
