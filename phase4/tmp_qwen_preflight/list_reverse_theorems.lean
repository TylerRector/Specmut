-- ↓↓↓ qwen-only LLM-generated theorems (HAND-WRITTEN IDEAL) ↓↓↓
theorem rev_max_preserved_generated (xs : List Nat) :
    IsMax (maxOf xs) xs → IsMax (maxOf (rev xs)) (rev xs) := sorry

theorem rev_max_self_generated (xs : List Nat) :
    IsMax (maxOf xs) (rev xs) := sorry
