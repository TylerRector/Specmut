-- A toy Lean 4 source for end-to-end testing of the specmut Lean
-- bridge.  The extractor recognises the predicate / theorem headers
-- here; the elaborator would only produce a usable signature for
-- predicates whose argument types are simple named sorts, so most of
-- this file flows through the extraction-only path on real Lean
-- installations.

def Sorted_v1 (l : List Nat) : Prop := ∀ i j, i < j → l[i] ≤ l[j]
def Sorted_v2 (l : List Nat) : Prop := ∀ i, i + 1 < l.length → l[i] ≤ l[i+1]
def Perm_v1 (a b : List Nat) : Prop := ∀ x, a.count x = b.count x
def Perm_v2 (a b : List Nat) : Prop := a.length = b.length ∧ ∀ x, x ∈ a ↔ x ∈ b

theorem sort_spec_v1 : ∀ l, Sorted_v1 (insertionSort l) ∧ Perm_v1 l (insertionSort l) := by sorry
theorem sort_spec_v2 : ∀ l, Sorted_v2 (mergeSort l) ∧ Perm_v2 l (mergeSort l) := by sorry
theorem sort_spec_v3 : ∀ l, Sorted_v1 (heapSort l) ∧ Perm_v1 l (heapSort l) := by sorry
