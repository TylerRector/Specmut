-- Phase 4 (qwen-only template-constrained variant) scaffold.
-- Mirrors benchmarks/sorting/reference.lean header.

def IsSorted (l : List Nat) : Prop :=
  match l with
  | [] => True
  | _ :: [] => True
  | a :: b :: rest => a ≤ b ∧ IsSorted (b :: rest)

axiom sort : List Nat → List Nat
