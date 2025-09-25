import Mathlib.Tactic



section BasicLogic

/-! ## Basic Logic

These exercises practice the fundamental logical reasoning tactics.
Remember:
- Use `intro` to introduce hypotheses for implications
- Use `exact` when you have exactly what you need
- Use `constructor` to split goals like `P ∧ Q` or `P ↔ Q`
-/

variable (P Q R : Prop)

-- Example: reflexivity of implication
example : P → P := by
  intro h
  exact h

-- Exercise 3: Simple implication chain
example : P → (Q → P) := by
  intro h1
  intro h2
  exact h1

-- Exercise 4: Transitivity of implication
example : (P → Q) → (Q → R) → (P → R) := by
  intro h1 h2 h3
  apply h2
  apply h1
  exact h3

-- Exercise 5: Conjunction introduction
example (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  · apply hP
  · apply hQ

-- Exercise 6: Conjunction commutativity
example : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro hPQ
    constructor
    · exact hPQ.right
    · exact hPQ.left
  · intro hQP
    constructor
    · exact hQP.right
    · exact hQP.left

-- Exercise 7: More complex logical reasoning
example : (P → Q) ∧ (P → R) → (P → Q ∧ R) := by
  intro h1
  intro hP
  constructor
  · apply h1.left
    exact hP
  · apply h1.right
    exact hP

end BasicLogic


section ApplyTactic

variable (P Q R S : Prop)

-- Example: basic apply usage
example (h1 : P → Q) (h2 : P) : Q := by
  apply h1
  exact h2
  -- equivalent to:
  -- apply h1 at h2
  -- exact h2
  -- equivalent to:
  -- exact h1 h2

-- Exercise 8: Chaining apply
example (h1 : P → Q) (h2 : Q → R) (h3 : P) : R := by
  apply h2
  apply h1
  exact h3

-- Exercise 9: Apply with multiple premises (from w1sheet2 style)
example (h0 : P ∧ Q ∧ R) (h : P → Q → R → S) : S := by
  obtain ⟨hp, hq, hr⟩ := h0
  apply h
  exact hp
  exact hq
  exact hr

-- Exercise 10: Mixed apply and intro
example : (P → Q) → (Q → R) → (P → R) := by
  intro hPQ hQR hP
  apply hQR
  apply hPQ
  exact hP

-- Hint: Chain the implications by working backwards from the goal
example (P Q R : Prop) : ((P → Q) ∧ (Q → R)) → (P → R) := by
  intro h_and hP
  obtain ⟨ hPQ, hQR ⟩ := h_and
  apply hQR
  apply hPQ
  -- equivalent to:
  -- apply h_and.right
  -- apply h_and.left
  exact hP

end ApplyTactic

section Functions

def f := fun x : ℕ ↦ fun y : ℕ ↦ x = y
-- equivalent to:
-- def f (x y : ℕ) : Prop := x = y

-- Exercise 11: Basic function application
example : f 0 0 := by rfl

-- Exercise 12: Function reasoning
example (x : ℕ) : f 0 x → x = 0 := by
  intro f0x
  rewrite [f] at f0x
  symm at f0x
  assumption
  -- equivalent to:
  -- symm
  -- exact f0x

-- Exercise 13: Function with inequality
example (x : ℕ) : f x 1 → x ≠ 2 := by
  intro fx1
  rewrite [f] at fx1
  by_contra gx2
  rewrite [fx1] at gx2
  contradiction
  -- equivalent to:
  -- trivial

-- Exercise 14: More complex function reasoning
example (x y : ℕ) : f 0 x ∧ f 0 y → x = y := by
  intro h1
  obtain ⟨ f0x, f0y ⟩ := h1
  rewrite [f] at f0x
  rewrite [f] at f0y
  rewrite [f0x] at f0y
  assumption
  -- equivalent to:
  -- trivial

end Functions
