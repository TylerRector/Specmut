-- Phase G fixture: type-class instance suppression.
-- `deriving Repr, DecidableEq, BEq, Hashable` synthesises ~15 type-class
-- instance constants.  Phase G's exporter filter should drop them all,
-- leaving only the Color sort, its three constructors, the isPrimary
-- predicate, and the two theorems.

inductive Color where
  | red | green | blue
  deriving Repr, DecidableEq, BEq, Hashable

def isPrimary : Color → Prop
  | .red => True
  | .green => False
  | .blue => True

theorem red_is_primary : isPrimary Color.red := by trivial
theorem blue_is_primary : isPrimary Color.blue := by trivial
