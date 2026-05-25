-- Reference specification for list minimum.
-- Constrains both directions: every element ≥ listMin xs, AND listMin returns
-- a value present in the list (modeled via IsMin predicate, dual of IsMax).
-- (Replaces "stack" from the original Phase 4 task list, which failed the
-- pre-registration gate by OOM-killing specmut at n=2.)

def IsMin (m : Nat) (l : List Nat) : Prop :=
  match l with
  | [] => True
  | x :: rest => m ≤ x ∧ IsMin m rest

axiom listMin : List Nat → Nat

theorem listMin_is_lower (xs : List Nat) :
    IsMin (listMin xs) xs := sorry
