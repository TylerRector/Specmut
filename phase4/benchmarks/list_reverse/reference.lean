-- Reference specification for list reversal.
-- Uses the IsMax invariant + an auxiliary maxOf accessor to constrain rev
-- via two coupled theorems.  This is structurally analogous to constraining
-- "rev preserves the multiset / extremal elements" without requiring an
-- inductive predicate that specmut's translator can't elaborate.

def IsMax (m : Nat) (l : List Nat) : Prop :=
  match l with
  | [] => True
  | x :: rest => x ≤ m ∧ IsMax m rest

axiom rev : List Nat → List Nat
axiom maxOf : List Nat → Nat

theorem rev_max_preserved (xs : List Nat) :
    IsMax (maxOf xs) xs → IsMax (maxOf (rev xs)) (rev xs) := sorry

theorem rev_self_max (xs : List Nat) :
    IsMax (maxOf xs) (rev xs) := sorry
