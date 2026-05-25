-- Phase G fixture: recursive predicates over `List Nat`.
-- Exercises the equation-lemma harvest path and Phase G sanitization;
-- the `x > 0` clause typically triggers a `Decidable`/`Ord` dictionary
-- argument that Phase G's sanitiser strips so the equation translates.

def AllPositive : List Nat → Prop
  | [] => True
  | x :: xs => x > 0 ∧ AllPositive xs

def SortedAsc : List Nat → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => x ≤ y ∧ SortedAsc (y :: rest)

theorem nil_all_positive : AllPositive [] := by trivial
theorem nil_sorted : SortedAsc [] := by trivial

theorem sorted_implies_head_le {x y : Nat} {rest : List Nat}
    (h : SortedAsc (x :: y :: rest)) : x ≤ y :=
  h.1
