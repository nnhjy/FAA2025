import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card

/- This exercise covers the essential concepts from Week 2:
- Quantifiers: universal (∀) and existential (∃)
- Set theory basics: membership (∈), subset (⊆), union (∪), intersection (∩)
- New tactics: `intro`, `use`, `obtain`, `left`, `right`, `cases`, `by_cases`, `ext`, `rintro`
- Set operations and extensionality principles
-/

/-! ## Part 1: Quantifiers and Basic Logic

Working with universal (∀) and existential (∃) quantifiers.
Remember: `∀ x, P x` is the same as `(x : α) → P x` in Lean.
-/

section Quantifiers

-- Exercise 1: Basic universal quantifier
-- Hint: Use `intro` to assume an arbitrary element, then prove the property
example : ∀ n : ℕ, n + 0 = n := by
  intro
  rfl

-- Exercise 2: Basic existential quantifier
-- Hint: Use `use` to provide a witness that satisfies the property
example : ∃ n : ℕ, n + 3 = 7 := by
  use 4

-- Exercise 3: Multiple existentials
-- Hint: Provide witnesses for both variables using `use`
example : ∃ n m : ℕ, n + m = 5 := by
  use 0,5

-- Definition for even numbers
def IsEven (n : ℤ) : Prop := ∃ k, n = 2 * k

-- Exercise 4: Working with definitions
-- Hint: Use `obtain` to extract the witness and property from the existential
example (h : ∃ n : ℤ, IsEven n ∧ n > 10) : ∃ m : ℤ, m > 5 := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨hn_1, hn_2⟩ := hn
  use n
  omega

-- Exercise 5: Combining quantifiers with logic
-- Hint: Unfold the definition, obtain the witness, then provide a new witness
example (n : ℤ) (h : IsEven n) : IsEven (n + 2) := by
  unfold IsEven at h
  unfold IsEven
  obtain ⟨ hk, hn ⟩ := h
  rw [hn]
  use hk+1
  rw [Int.mul_add]
  omega

end Quantifiers

/-! ## Part 2: Set Theory Fundamentals

Basic set operations and their properties.
Sets in Lean are functions α → Prop.
-/

section SetBasics

open Set
variable {α : Type*}
variable (A B C D : Set α)

-- Exercise 6: Reflexivity of subset
-- Hint: Rewrite using subset definition, then use `intro` and `assumption`
#check subset_def
example : A ⊆ A := by
  rw [@subset_def]
  intro a ha
  assumption

-- Exercise 7: Empty set is subset of everything
-- Hint: Use subset definition, then `exfalso` to derive contradiction from empty set membership
example : ∅ ⊆ A := by
  rw [@subset_def]
  intro x ha
  exfalso
  contradiction

-- Exercise 8: Transitivity of subset
-- Hint: Use subset definition, then chain the implications
example : A ⊆ B → B ⊆ C → A ⊆ C := by
  intros ab bc
  rw [@subset_def]
  rw [@subset_def] at ab bc
  intro x xa
  apply bc
  apply ab
  exact xa

-- Exercise 9: Intersection subset
-- Hint: Use subset and intersection definitions
#check mem_inter_iff
example : A ∩ B ⊆ B := by
  rw [@subset_def]
  intro x AB
  rw [@mem_inter_iff] at AB
  obtain ⟨xA, xB⟩ := AB
  exact xB

-- Exercise 10: Subset intersection characterization
-- Hint: Use constructor to split the conjunction, then prove each direction
example : A ⊆ B → A ⊆ C → A ⊆ B ∩ C := by
  intros AB AC
  rw [@subset_def]
  rw [@subset_def] at AB AC
  intro x xA
  constructor
  · apply AB; exact xA
  · apply AC; exact xA


end SetBasics

/-! ## Part 3: Disjunctions and Case Analysis

Working with logical OR (∨) and case analysis.
-/

section Disjunctions

open Set
variable {α : Type*}
variable (A B C : Set α)

-- Exercise 11: Left inclusion in union
-- Hint: Use `left` to choose the first disjunct
example : A ⊆ A ∪ B := by
  rw [@subset_def]
  intro x xA
  left
  exact xA

-- Exercise 12: Case analysis with excluded middle
-- Hint: `by_cases` splits into two cases automatically
example (x : α) : x ∈ A ∨ x ∉ A := by
  by_cases h : x ∈ A
  · left; exact h
  · right; exact h

  -- by_cases h: x ∉ A
  -- · right; exact h
  -- · left
  --   by_contra xn
  --   contradiction


-- Exercise 13: Union subset characterization
-- Hint: Use constructor for the biconditional, then `cases` to handle the union
#check mem_union
lemma my_union_subset_iff : A ⊆ C ∧ B ⊆ C ↔ A ∪ B ⊆ C := by
  constructor

  · intro han
    obtain ⟨AC,BC⟩ := han
    rw [@subset_def]
    intro x xAuB
    cases xAuB
    · rw [@subset_def] at AC
      apply AC; assumption
    · rw [@subset_def] at BC
      apply BC; assumption

  · intro hor
    constructor
    · rw [@subset_def] at hor
      rw [@subset_def]
      intro x xA
      apply hor
      rw [@mem_union]
      left; exact xA
    · rw [@subset_def] at hor
      rw [@subset_def]
      intro x xB
      apply hor
      rw [@mem_union]
      right; exact xB

-- Exercise 14: Using the characterization
-- Hint: Apply the lemma you just proved
example : B ⊆ A → C ⊆ A → B ∪ C ⊆ A := by
  intro BA CA
  rw [← my_union_subset_iff]
  exact ⟨BA, CA⟩

end Disjunctions
