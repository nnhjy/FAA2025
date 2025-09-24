import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
set_option tactic.hygienic false

/-! New tactics
 * `left`  -- change the goal of the form P ∨ Q to P
 * `right` -- change the goal of the form P ∨ Q to Q
 * `cases` -- deal with cases. That is, if you have h: P ∨ Q then cases h will automatically split into two goals.
              One goal assume P and the other goal assume Q.
 * `by_cases` -- prove by cases
-/

open Set
variable {α : Type*}
variable (A B C D: Set α)

-- Example: Left/Right tactics
example : A ⊆ A ∪ B := by
  rw [@subset_def]
  intro x hx
  rw [@mem_union]
  left
  exact hx

-- Example: by_cases tactics
example (x : α) : x ∈ A ∨ x ∉ A := by
  by_cases h : x ∈ A
  · left; exact h
  · right; exact h

-- Example: cases tactics
example: ∀ x ∈ A ∪ B, x ∈ A ∪ B ∪ C:= by
  intro x hx
  cases hx
  left
  left
  exact h
  left
  right
  exact h

-- Exercise 5: Cases tactics. You are allowed to use *only* these two lemmas.
#check mem_union
#check subset_def

lemma my_union_subset_imp :  A ⊆ C ∧ B ⊆ C → A ∪ B ⊆ C := by sorry

-- Extend my_union_subset_imp to my_union_subset_iff
-- You are allowed to use *only* these two lemmas.
#check mem_union
#check subset_def

-- running example
lemma my_union_subset_iff:  A ⊆ C ∧ B ⊆ C ↔ A ∪ B ⊆ C := by
  constructor
  intro a
  exact my_union_subset_imp A B C a
  intro
  rw [Set.subset_def] at a
  constructor
  intro x hx
  apply a
  simp only [mem_union]
  left
  exact hx
  intro x hx
  apply a
  right
  exact hx

-- Exercise 6: you may want to use my_union_subset_iff
example : B ⊆ A → C ⊆ A → B ∪ C ⊆ A := by sorry

/-! New tactics
 * `ext`  -- extensionality. Proving that two functions are identical. Since sets are functions in Lean, `ext` can be used to prove set equality.
-/

-- example
lemma inter_comm: A ∩ B = B ∩ A := by
  ext x
  constructor
  rintro ⟨a,b⟩
  exact ⟨b,a⟩
  rintro ⟨a,b⟩
  exact ⟨b,a⟩

-- example
lemma absorption_law: A ∩ (A ∪ B) = A := by
  ext x
  constructor
  · intro
    exact a.1
  · intro
    constructor
    · exact a
    · left
      exact a

-- Exercise 7
lemma union_comm : A ∪ B = B ∪ A := by sorry
