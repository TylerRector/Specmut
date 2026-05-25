-- Phase 4 (qwen-only template-constrained variant) scaffold.
--
-- This file is prepended to every LLM-generated theorem block so the
-- model only has to write theorem statements, not invent the vocabulary
-- (axioms / predicates).  The names declared here are the ONLY identifiers
-- the LLM is told it may use in its theorem bodies.
--
-- Mirrors benchmarks/list_min/reference.lean header (no theorem lines).

def IsMin (m : Nat) (l : List Nat) : Prop :=
  match l with
  | [] => True
  | x :: rest => m ≤ x ∧ IsMin m rest

axiom listMin : List Nat → Nat
