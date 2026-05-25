-- Phase G fixture: multi-constructor inductive with a recursive function
-- (`eval`, codomain Nat) and a propositional predicate (`isLit`).  The
-- theorems are equalities about `eval`, exercising the function-eqn path.

inductive Expr where
  | lit (n : Nat)
  | add (e1 e2 : Expr)
  | mul (e1 e2 : Expr)

def eval : Expr → Nat
  | .lit n => n
  | .add e1 e2 => eval e1 + eval e2
  | .mul e1 e2 => eval e1 * eval e2

def isLit : Expr → Prop
  | .lit _ => True
  | _ => False

theorem lit_eval (n : Nat) : eval (Expr.lit n) = n := by rfl
theorem eval_add (e1 e2 : Expr) :
    eval (Expr.add e1 e2) = eval e1 + eval e2 := by rfl
