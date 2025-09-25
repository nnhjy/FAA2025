import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
set_option tactic.hygienic false

/-! New tactics
 * `left`  -- change a *goal* of the form `P ∨ Q` or `P ∪ Q` to P
 * `right` -- change a *goal* of the form `P ∨ Q` or `P ∪ Q` to Q
 * `cases` -- deal with cases *hypothesis*.
              That is, if you have `h: P ∨ Q` then `cases h` will automatically split into two goals.
              One goal assume `P` and the other goal assume `Q`.
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
  rw [@mem_union] at hx

  cases hx
  · left
    left
    exact h
  · left
    right
    exact h

-- Exercise 5: Cases tactics. You are allowed to use *only* these two lemmas.
#check mem_union
#check subset_def

lemma my_union_subset_imp : A ⊆ C ∧ B ⊆ C → A ∪ B ⊆ C := by
  intro pre
  obtain ⟨ hac,hbc ⟩ := pre
  rw [@subset_def] at hac hbc
  rw [@subset_def]
  intro x haub
  rw [@mem_union] at haub
  cases haub
  · apply hac; exact h
  · apply hbc; exact h

-- Extend my_union_subset_imp to my_union_subset_iff
-- You are allowed to use *only* these two lemmas.
#check mem_union
#check subset_def

-- running example
lemma my_union_subset_iff: A ⊆ C ∧ B ⊆ C ↔ A ∪ B ⊆ C := by
  constructor
  intro a
  exact my_union_subset_imp A B C a
  intro
  rw [Set.subset_def] at a
  constructor
  · intro x hx
    apply a
    simp only [mem_union]
    left
    exact hx
  · intro x hx
    apply a
    right
    exact hx

-- Exercise 6: you may want to use my_union_subset_iff
example : B ⊆ A → C ⊆ A → B ∪ C ⊆ A := by
  intro hba hca

  rewrite [← my_union_subset_iff]
  exact ⟨hba, hca⟩
  -- OR equivalently:
  -- rw [@subset_def] at hba hca
  -- rw [@subset_def]
  -- intro x xbc
  -- rw [@mem_union] at xbc
  -- cases xbc
  -- · apply hba; exact h
  -- · apply hca; exact h

/-! New tactics
 * `ext` -- extensionality. Proving that two functions are identical.
         -- Since sets are functions in Lean, `ext` can be used to prove set equality.
-/

-- example
lemma inter_comm: A ∩ B = B ∩ A := by
  ext x

  -- constructor
  -- · intro h
  --   rw [@mem_inter_iff]
  --   obtain ⟨ h1, h2 ⟩ := h
  --   constructor
  --   exact h2
  --   exact h1
  -- · intro h
  --   rw [@mem_inter_iff]
  --   obtain ⟨ h1, h2 ⟩ := h
  --   constructor
  --   exact h2
  --   exact h1

  -- constructor <;> all_goals {
  --   intro h
  --   rw [@mem_inter_iff]
  --   obtain ⟨ h1, h2 ⟩ := h
  --   constructor
  --   exact h2
  --   exact h1
  -- }

  constructor
  · rintro ⟨a,b⟩
    exact ⟨b,a⟩
  · rintro ⟨a,b⟩
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
lemma union_comm : A ∪ B = B ∪ A := by
  ext x

  -- constructor <;> all_goals {
  --   intro h
  --   cases h
  --   · right; exact h_1
  --   · left; exact h_1
  -- }

  constructor <;> all_goals {
    · rintro (h_l | h_r)
      · right; exact h_l
      · left; exact h_r
  }
