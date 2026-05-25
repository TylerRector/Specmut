-- BST fixture: inductive type + constructors + recursive predicate
-- with pattern matching + theorem statements.  Used to validate the
-- §3.3 IR schema coverage of the specmut exporter.

inductive Tree where
  | leaf : Tree
  | node : Tree → Nat → Tree → Tree
deriving Repr

def Tree.contains : Tree → Nat → Bool
  | .leaf,       _ => false
  | .node l v r, x =>
      if x = v then true
      else if x < v then l.contains x
      else r.contains x

def Sorted : List Nat → Prop
  | []           => True
  | [_]          => True
  | a :: b :: rs => a ≤ b ∧ Sorted (b :: rs)

theorem sorted_nil       : Sorted [] := trivial
theorem sorted_singleton : ∀ n : Nat, Sorted [n] := fun _ => trivial

theorem leaf_contains_none : ∀ x : Nat, ¬ Tree.contains .leaf x := by
  intro x; simp [Tree.contains]
