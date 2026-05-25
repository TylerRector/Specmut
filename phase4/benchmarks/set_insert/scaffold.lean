-- Phase 4 (qwen-only template-constrained variant) scaffold.
-- Mirrors benchmarks/set_insert/reference.lean header.

def Distinct (l : List Nat) : Prop :=
  match l with
  | [] => True
  | x :: rest => (¬ x ∈ rest) ∧ Distinct rest

axiom setInsert : Nat → List Nat → List Nat
