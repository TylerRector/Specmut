-- Phase 4 (qwen-only template-constrained variant) scaffold.
-- Mirrors benchmarks/list_reverse/reference.lean header.

def IsMax (m : Nat) (l : List Nat) : Prop :=
  match l with
  | [] => True
  | x :: rest => x ≤ m ∧ IsMax m rest

axiom rev : List Nat → List Nat
axiom maxOf : List Nat → Nat
