import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
set_option tactic.hygienic false


/-!
## Universal quantifier (∀) and Existential (∃) Quantifiers
* `∀ x : α, P x` means for every element x of type α, the property `P x` holds.
   In Lean, this is the same as `(x : α) → P x`
* `∃ x : α, P x` means there exists some element x of type α such that `P x` holds
-/

/-! Working with universal quantifier
* `intro` -- to reduce a *goal* of the form `∀ x : ℕ , P(x)` to `P(x)` and obtain `x : ℕ` as a variable
  i.e., to prove for-all statement, let fix an arbitrary element x, and then we prove P(x)
  This is because, in Lean, `∀ x : N, P(x)` is equivalent to `(x : ℕ) →  P(x)`
-/

def f (x :ℕ) := x = 0
#check f
example : (∀ x : ℕ, f x) ↔ ((x : ℕ) → f x) := by rfl

example : ∀ n : ℕ, n + 0 = n := by
  intro n
  rfl


/-! tactics for working with the existential quantifier
* `use` -- The use tactic is used to provide a witness for a *goal* of existential statement: `∃ x, P x`
* `obtain` -- reverse of the `use` tactic on a *hypothesis* that states `h : ∃ x, P x`,
           -- "extract"ing the witness `x` and its property `P x` from `h` so you can use them in your proof.
           -- `obtain ⟨x, hx⟩ := h` extracts witness and property from `h: ∃ x, P x`
           -- Use obtain `⟨a, ⟨b, c⟩⟩ := h` for nested existentials
-/

example : ∃ n : ℕ, n + 3 = 7 := by
  use 4

example : ∃ n m : ℕ, n + m = 5 := by
  use 2,3

-- Definition of an even number.
def IsEven (n : ℤ) : Prop := ∃ k, n = 2 * k

-- If there exists an even number `n` that is greater than 10,
-- then there must exist some integer `m` that is greater than 5.
example (h : ∃ n : ℤ, IsEven n ∧ n > 10) : ∃ m : ℤ, m > 5 := by
  -- Use `obtain` to get the number `n` and its properties from `h`.
  -- The syntax is: `obtain ⟨n, hn_prop⟩ := h`
  obtain ⟨ x, hx ⟩ := h
  obtain ⟨ h1, h2 ⟩ := hx
  use x
  omega

def IsOdd (n : ℤ) : Prop := ∃ k, n = 2 * k + 1

example (n:ℤ) (h : IsEven n) :  IsOdd (n+1) := by
  rw [IsOdd]
  rw [IsEven] at h
  obtain ⟨ k, hk ⟩ := h
  use k
  rw [hk]

  -- unfold IsOdd
  -- unfold IsEven at h
  -- obtain ⟨k,hk⟩ := h
  -- use k
  -- rw [hk]

-- Exercise 0. Prove that the sum of two even numbers is even.
#check Int.mul_add

example (a b:ℤ) (h_a : IsEven a) (h_b : IsEven b) : IsEven (a + b) := by
  rw [IsEven] at h_a
  rw [IsEven] at h_b
  obtain ⟨ ka, ha ⟩ := h_a
  obtain ⟨ kb, hb ⟩ := h_b
  use (ka + kb)
  rw [ha]
  rw [hb]
  rw [Int.mul_add]
