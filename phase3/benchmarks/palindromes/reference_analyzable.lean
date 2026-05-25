inductive Palindrome : List α → Prop where
  | nil      : Palindrome []
  | single   : (a : α) → Palindrome [a]
  | sandwich : (a : α) → Palindrome as → Palindrome ([a] ++ as ++ [a])

theorem palindrome_reverse (h : Palindrome as) : Palindrome as.reverse := sorry
theorem reverse_eq_of_palindrome (h : Palindrome as) : as.reverse = as := sorry
def List.last : (as : List α) → as ≠ [] → α
  | [a],         _ => a
  | _::a₂:: as, _ => (a₂::as).last (by simp)

theorem List.palindrome_ind (motive : List α → Prop)
    (h₁ : motive [])
    (h₂ : (a : α) → motive [a])
    (h₃ : (a b : α) → (as : List α) → motive as → motive ([a] ++ as ++ [b]))
    (as : List α)
    : motive as := sorry
theorem List.palindrome_of_eq_reverse (h : as.reverse = as) : Palindrome as := sorry
def List.isPalindrome [DecidableEq α] (as : List α) : Bool :=
    as.reverse = as

theorem List.isPalindrome_correct [DecidableEq α] (as : List α) : as.isPalindrome ↔ Palindrome as := sorry
