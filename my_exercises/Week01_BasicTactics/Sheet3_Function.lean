import Mathlib.Tactic

-- ## how to define new types from old types
-- Terms can be anonnymous functions (also called λ-expressions)
#check ℕ
-- New types can be created by defining a function between types
#check ℕ → ℤ
#check fun (x : ℕ) ↦ x
#check fun (x : ℕ) ↦ (x : ℤ)
#check fun (x : ℕ) ↦ (x^2+x-10: ℤ)
def f' := fun (x : ℕ) ↦ (x^2+x-10: ℤ)

#check ℕ → ℕ → Prop
#check fun x : ℕ ↦ fun y ↦ x = y

def f := fun x : ℕ ↦ fun y : ℕ  ↦ x = y
#check f
-- function can be partially applied
#check f 0
#check f 0 0

example : f 0 0 := by rfl

/-! New tactics
* `rewrite [h]`   - replace a term in a *goal* with an equivalent term (*hypothesis*: statement, function) `h`.
* `rewrite [← h]` - replace a term in a *goal* with `h` in the reverse direction stated by `h`.
* `assumption` - we are done because ∃`h` s.t. `exact h` can close the *goal*
* `rw` -- rewrite, followed by trying to close the *goal* by `rfl`.
-/

example (x: ℕ): f 0 x → x = 0 := by
  intro h
  rw [f] at h
  symm at h
  assumption

-- Give a direct proof
example (x: ℕ): f x 1 → x ≠ 2 := by
  intro fx
  rw [f] at fx
  rw [fx]
  trivial

example (x y: ℕ): f 0 x ∧ f 0 y → x = y := by
  intro af
  obtain ⟨ fx, fy ⟩ := af
  rw [f] at fx fy
  rw [← fx,fy]

/-! Bonus:
* `by_contra` - assume the negation of the *goal* and prove False
* `contradiction` - we are done because we have a proof of `h : P` and `h' : ¬ P`
* `contrapose!` - Transforms the *goal* into its contrapositive and uses pushes negations inside P and Q. Usage matches `contrapose`.
* `trivial` - apply `rfl` or `assumption` or `contradiction` tactics
-/

-- Prove by contradiction
example (h1: a = b): a = b := by
  by_contra neq
  contradiction

example (x: ℕ): f x 1 → x ≠ 2 := by
  -- rewrite [f]
  -- intro x1
  -- by_contra x2
  -- rw [x2] at x1
  -- contradiction

  contrapose!
  intro x2
  rw [f, x2]
  trivial
