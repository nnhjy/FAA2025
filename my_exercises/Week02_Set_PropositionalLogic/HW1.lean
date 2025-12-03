import Mathlib.Tactic
import Mathlib.Data.Finset.Card

set_option autoImplicit false
set_option tactic.hygienic false

/- # Instruction
In this homework, you are not allowed to use tactics outside the basic tactics listed below.
Basic tactics:
`exact`, `rfl`, `trivial`,`contradiction`,`assumption`,
`intro`, `apply`, `rw`, `constructor`,
`left`, `right`, `cases`, `by_cases`, `ext`, ,`have`, `by_contra`, `rintro`

If you need to use different tactics, please justify why basic tactics in the list above are not sufficient.
In particular, you are not allowed to use automation (simp, aesop, grind, ring, omega, etc) to finish the goal.

**Instruction**:
(1) Fill each `sorry` with the appropriate tactics.
(2) For each problem, give an informal explanation of the proof strategy. This should correspond to your Lean proof.
**Submission**:  HW1.lean file in Moodle. The grading will be based on (1) and (2).

-/

-- **Set definitions** (hope this is allowed)
#check Set.subset_def
#check Set.union_def
#check Set.inter_def
#check Set.mem_union
#check Set.mem_inter_iff

section
open Set
variable {α : Type*}
variable (A B C : Set α)

/-
* Proof strategy for P1 is:
- Split the equivalence into two directions using constructor.
- Forward direction (→):
  - Assume (B ∪ C) ⊆ A.
  - Show both B ⊆ A and C ⊆ A by:
    - For B ⊆ A: Take any x ∈ B, then x ∈ B ∪ C, so x ∈ A.
    - For C ⊆ A: Take any x ∈ C, then x ∈ B ∪ C, so x ∈ A.
- Backward direction (←):
  - Assume B ⊆ A and C ⊆ A.
  - Show (B ∪ C) ⊆ A by:
    - Take any x ∈ B ∪ C, do a case split:
      - If x ∈ B, then x ∈ A.
      - If x ∈ C, then x ∈ A.
-/

lemma P1 : (B ∪ C) ⊆ A ↔ B ⊆ A ∧ C ⊆ A := by
  constructor
  · intro lpre
    rw [@subset_def] at lpre
    constructor
    · rw [@subset_def]
      intro x xB
      apply lpre
      rw [@mem_union]
      · left; exact xB
    · rw [@subset_def]
      intro x xC
      apply lpre
      rw [@mem_union]
      · right; exact xC
  · intro rpre
    obtain ⟨hBA, hCA⟩ := rpre
    rw [@subset_def] at hBA hCA
    rw [@subset_def]
    intro x xBuC
    rw [@mem_union] at xBuC
    cases xBuC
    · apply hBA; exact h
    · apply hCA; exact h

/-
* Proof strategy for P2 is:
1. Extensionality: Use ext x to reduce set equality to elementwise equality.
2. Two directions (constructor):
  - Forward (→):
    - Assume x ∈ A ∩ (B ∪ C).
    - Unpack this as x ∈ A and x ∈ B ∪ C.
    - By cases on whether x ∈ B or x ∈ C, show x ∈ (A ∩ B) or x ∈ (A ∩ C).
  - Backward (←):
    - Assume x ∈ (A ∩ B) ∪ (A ∩ C).
    - By cases, unpack as x ∈ A ∩ B or x ∈ A ∩ C.
    - In both cases, show x ∈ A and x ∈ B ∪ C by reconstructing the membership.
-/

theorem P2 : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  constructor

  · intro hx
    obtain ⟨hA, hBuC⟩ := hx
    rw [@mem_union] at hBuC
    rw [@mem_union]
    cases hBuC
    · left
      rw [@mem_inter_iff]
      exact ⟨hA,h⟩
    · right
      rw [@mem_inter_iff]
      exact ⟨hA,h⟩

  · intro hx
    constructor
    · cases hx
      · rw [@mem_inter_iff] at h
        obtain ⟨xA, xB⟩ := h; exact xA
      · rw [@mem_inter_iff] at h
        obtain ⟨xA, xC⟩ := h; exact xA
    · rw [@mem_union] at hx
      rw [@mem_union]
      cases hx
      · rw [@mem_inter_iff] at h
        obtain ⟨xA, xB⟩ := h
        left; exact xB
      · rw [@mem_inter_iff] at h
        obtain ⟨xA, xC⟩ := h
        right; exact xC

/-
* Proof strategy for P3 is:
1. Auxiliary Lemmas:
  - Prove two helper lemmas that allow to rewrite and simplify the main expression.
  `(A ∩ B) ∪ (A ∩ C) = A ∩ (B ∪ C)` (my_union_inter)
  `(A ∪ B) ∩ (A ∪ C) = A ∪ (B ∩ C)` (my_inter_union)
2. Elementwise Reasoning:
  - Use `ext x` to reduce set equality to elementwise membership.
  - Split the proof into two directions using constructor.
3. Forward Direction:
  - Assume `x ∈ (A ∪ B) ∩ (A ∪ C) ∩ (B ∪ C)` and use the helper lemmas to rewrite intersections and unions.
  - Do case analysis to show x must be in one of (A ∩ B), (A ∩ C), or (B ∩ C).
4. Backward Direction:
  - Assume x ∈ (A ∩ B) ∪ (A ∩ C) ∪ (B ∩ C) and use the helper lemmas to reconstruct the membership in the triple intersection.
  - Do case analysis on which part of the union x belongs to, and show it satisfies the intersection.
-/

theorem P3 : (A ∪ B) ∩ (A ∪ C) ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) ∪ (B ∩ C) := by

  -- Auxiliary Lemma 1
  have my_union_inter : (A ∩ B) ∪ (A ∩ C) = A ∩ (B ∪ C) := by
    ext x
    constructor
    · intro h1
      rw [@mem_union] at h1
      rw [@mem_inter_iff] at h1 h1
      rw [@mem_inter_iff]
      rw [@mem_union]
      cases h1
      · obtain ⟨xA, xB⟩ := h
        constructor
        · exact xA
        · left; exact xB
      · obtain ⟨xA, xC⟩ := h
        constructor
        · exact xA
        · right; exact xC
    · intro h1
      rw [@mem_inter_iff] at h1
      rw [@mem_union] at h1
      rw [@mem_union]
      rw [@mem_inter_iff, @mem_inter_iff]
      obtain ⟨xA, xBvC⟩ := h1
      cases xBvC
      · left; exact ⟨xA,h⟩
      · right; exact ⟨xA,h⟩

  -- Auxiliary Lemma 2
  have my_inter_union : (A ∪ B) ∩ (A ∪ C) = A ∪ (B ∩ C) := by
    ext x
    constructor
    · intro h1
      rw [@mem_inter_iff] at h1
      rw [@mem_union] at h1 h1
      rw [@mem_union]
      rw [@mem_inter_iff]
      obtain ⟨xAvB, xAvC⟩ := h1
      by_cases h: x ∈ A
      · left; exact h
      · cases xAvB
        · contradiction
        · right
          constructor
          · exact h_1
          · cases xAvC
            · contradiction
            · exact h_2
    · intro h1
      rw [@mem_union] at h1
      rw [@mem_inter_iff] at h1
      rw [@mem_inter_iff]
      rw [@mem_union, @mem_union]
      cases h1
      · constructor
        · left; exact h
        · left; exact h
      · obtain ⟨xB, xC⟩ := h
        constructor
        · right; exact xB
        · right; exact xC

-- Main proof
  ext x
  constructor

  · rintro ⟨h_l, h_r⟩
    rw [my_inter_union] at h_l
    rw [my_union_inter]
    cases h_l
    · left; exact ⟨h, h_r⟩
    · right; exact h

  · rintro (h_l | h_r)
    · rw [my_union_inter] at h_l
      rw [my_inter_union]
      obtain ⟨xA, xBuC⟩ := h_l
      constructor
      · left; exact xA
      · exact xBuC
    · rw [my_inter_union]
      constructor
      · right; exact h_r
      · obtain ⟨xB, xC⟩ := h_r
        left; exact xB

/-
* Proof strategy for P4 is:
1. Forward direction (→):
  - Assume there exists a set X such that A ∪ X = B.
  - Show A ⊆ B by rewriting the goal using the given equality and applying the fact that A ⊆ A ∪ X.
2. Backward direction (←):
  - Assume A ⊆ B.
  - Construct X = B \ A (the set difference).
  - Show that A ∪ (B \ A) = B by elementwise reasoning:
    - For any x ∈ A ∪ (B \ A), show x ∈ B.
    - For any x ∈ B, show x ∈ A ∪ (B \ A) by cases on whether x ∈ A or not.
-/

-- The set difference operation is denoted by B \ A
-- This can be simplified using rw [mem_diff] where
#check mem_diff

-- In this theorem, the partial proof has been outlined.
-- Your task is to fill in the sorry
-- the following theorem can be helpful
#check subset_union_left

theorem P4 : (∃ X : Set α, A ∪ X = B) ↔ A ⊆ B := by
  constructor
  · -- Forward direction: if there exists X such that A ∪ X = B, then A ⊆ B
    intro h_e
    obtain ⟨sX, hAuX⟩ := h_e
    rw [← hAuX]
    exact subset_union_left
  · -- Reverse direction: if A ⊆ B, then there exists X such that A ∪ X = B
    intro h           -- "Assume A ⊆ B"
    use B \ A         -- "Let X = B \ A"
    ext x
    constructor
    · intro h_pre
      cases h_pre
      · apply h at h_1
        exact h_1
      · rw [@mem_diff] at h_1
        obtain ⟨xB, xNA⟩ := h_1
        exact xB
    · intro h_xB
      by_cases hc: x ∈ A
      · left; exact hc
      · right
        rw [@mem_diff]
        exact ⟨h_xB, hc⟩

end

section

variable {α : Type*} [DecidableEq α]
variable (A B C : Finset α)

open Finset
-- Finset is a set whose cardinality is bounded
-- If A is a Finset, then #A is the cardinality of the set

/- Recall rw tactics:
If thm is a theorem a = b, then as a rewrite rule,
  rw [thm] means to replace a with b, and
  rw [← thm] means to replace b with a.
-/

def IsEven (n : ℕ) : Prop := ∃ k, n = 2 * k
def IsDisjoint (A B: Finset α) : Prop := A ∩ B = ∅

-- you may find the following operations useful
#check card_union
#check card_eq_zero
#check Nat.two_mul

/-
* Proof strategy for P5 is:
1. Key Claim:
- Prove that #(A ∪ B) = #A + #B using the fact that A and B are disjoint (A ∩ B = ∅),
  so their union's cardinality is the sum of their cardinalities.
2. Rewrite the Goal:
- Use the definition of IsEven (∃ k, #U = 2 * k).
- Substitute U = A ∪ B and the claim above to get #U = #A + #B.
3. Use the Given Equality:
- Substitute #A = #B to get #U = #B + #B = 2 * #B.
4. Conclude Evenness:
- Provide a witness of k = #B such that #U = 2 * k is even by definition.
-/

theorem P5 (U : Finset α) (A B : Finset α)
(hAB : IsDisjoint A B) (hcard : #A = #B) (htotal : A ∪ B = U) : IsEven (#U) := by
  -- Hint: First prove the following claim:
  have AB_eq: #(A ∪ B) = #A + #B := by
    rw [card_union]
    rw [IsDisjoint] at hAB
    rw [← card_eq_zero] at hAB
    rw [hAB]
    rfl

  -- Then use AB_eq to finish the proof
  rw [IsEven]
  rw [← htotal]
  rw [AB_eq]
  rw [hcard]
  use #B
  rw [Nat.two_mul]

end
