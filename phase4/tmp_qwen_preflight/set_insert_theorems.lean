-- ↓↓↓ qwen-only LLM-generated theorems (HAND-WRITTEN IDEAL) ↓↓↓
theorem setInsert_preserves_distinct_generated (k : Nat) (xs : List Nat) :
    Distinct xs → Distinct (setInsert k xs) := sorry

theorem setInsert_idempotent_distinct_generated (k : Nat) (xs : List Nat) :
    Distinct (setInsert k (setInsert k xs)) := sorry
