import Mathlib.Tactic
import Lectures.Week06.API

set_option autoImplicit false
set_option tactic.hygienic false


-- In this sheet, we are going to prove the merge lemma

def Merge: List ℕ → List ℕ → List ℕ
  | x, [] => x
  | [], x => x
  | x::xs, y::ys =>
    if x ≤ y then x :: Merge xs (y::ys)
    else y :: Merge (x :: xs) ys
/-
# Note
In a proof applying `fun_induction` on `Merge`,
since the function is defined in curried form (x → y → z), is it not necessary to explictly claim the two variables,
i.e.
`fun_induction Merge` is as good as `fun_induction Merge l1 l2`
-/

-- Example: Let's prove this by `recursion`
lemma merge_size_sum (l1 l2 : List ℕ) : (Merge l1 l2).length = l1.length + l2.length  := by
  match l1, l2 with
  | x, [] => simp [Merge]
  | [], x => unfold Merge; aesop
  | x::xs, y::ys =>
    simp +arith +decide only [List.length_cons, Merge]
    split_ifs
    · simp
      apply merge_size_sum
    · simp
      have: xs.length + ys.length + 1 = (xs.length +1 ) + ys.length := by omega
      rw [this]
      apply merge_size_sum

-- Example: prove *merge_size_sum* by `functional induction`
example (l1 l2 : List ℕ) : (Merge l1 l2).length = l1.length + l2.length  := by
  fun_induction Merge l1 l2
  · simp
  · simp
  · simp
    rw [ih1]
    simp +arith
  · simp
    rw [ih1]
    simp +arith

-- Example: prove *merge_size_sum* by `functional induction` in detail
example (l1 l2 : List ℕ) : (Merge l1 l2).length = l1.length + l2.length  := by
fun_induction Merge
· simp only [List.length_nil, add_zero]
· simp only [List.length_nil, zero_add]
· simp only [List.length_cons]
  grind
  -- simp_all
  -- rfl
· simp +arith only [List.length_cons]
  have: xs.length + ys.length + 1 = (xs.length +1 ) + ys.length := by omega
  rw [this]
  grind
  -- simp_all

-- Example: prove *merge_size_sum* leveraging `automation + functional induction`
example (l1 l2 : List ℕ) : (Merge l1 l2).length = l1.length + l2.length  := by
fun_induction Merge <;> all_goals grind

-- Example: another theorem with this hammer
theorem mem_either_merge_auto (xs ys : List ℕ) (z : ℕ) (hz : z ∈ Merge xs ys)
  : z ∈ xs ∨ z ∈ ys := by
  fun_induction Merge <;> all_goals grind

-- Let's break down the proof and see how to prove this `by hand`.
-- Exercise 2.1: try to prove this using either recursion or functional induction (don't use grind on the inductive step)
theorem mem_either_merge (xs ys : List ℕ) (z : ℕ) (hz : z ∈ Merge xs ys)
  : z ∈ xs ∨ z ∈ ys := by
  fun_induction Merge xs ys
  · simp; exact hz
  · right; exact hz
  · simp_all
    cases hz
    · simp_all
    · simp [h_1] at ih1
      cases ih1
      · left; right; exact h_2
      · right; exact h_2
  · simp_all
    cases hz
    · right; left; exact h_1
    · simp [h_1] at ih1
      cases ih1
      · left; exact h_2
      · right; right; exact h_2

-- Prove *mem_either_merge* by `recursion`
theorem mem_either_merge_rec (xs ys : List ℕ) (z : ℕ) (hz : z ∈ Merge xs ys)
  : z ∈ xs ∨ z ∈ ys := by
  match xs, ys with
  | x, [] =>
    rw [Merge] at hz
    left; exact hz
  | [], x =>
    unfold Merge at hz; aesop
    -- `unfold` to manipulate the `inductive structure` which can be handled by `aesop
    -- # equivalent detail
    -- by_cases h : x = []
    -- · rw [h] at hz ⊢
    --   rw [Merge] at hz
    --   left; exact hz
    -- · rw [Merge] at hz
    --   right; exact hz
    --   intro hx; contradiction
  | x::xs, y::ys =>
    unfold Merge at hz
    split at hz
    -- # recursion in such case is more complex
    · have: z = x ∨ z ∈ Merge xs (y:: ys) := by exact List.eq_or_mem_of_mem_cons hz
      cases this
      · subst h
        left
        exact List.mem_cons_self
      · apply mem_either_merge_rec at h
        cases h
        · left
          exact List.mem_cons_of_mem x h_1
        · right
          exact h_1
    · have: z = y ∨ z ∈ Merge (x::xs) (ys) := by exact List.eq_or_mem_of_mem_cons hz
      cases this
      · subst h
        right
        exact List.mem_cons_self
      · apply mem_either_merge_rec at h
        cases h
        · left
          exact h_1
        · right
          exact List.mem_cons_of_mem y h_1

-- Exercise 2.2: use mem_either_merge to prove the following.
#check mem_either_merge
#print Nat.MinOfList
theorem min_all_merge
  (x : ℕ) (xs ys: List ℕ) (hxs : x.MinOfList xs) (hys : x.MinOfList ys)
  : x.MinOfList (Merge xs ys):= by
  simp
  intro y hy
  have : y ∈ xs ∨ y ∈ ys := by
    apply mem_either_merge; exact hy
  cases this
  · exact hxs y h
  · exact hys y h
  -- obtain case1 | case2 := this
  -- · exact hxs y case1
  -- · exact hys y case2

  -- fun_induction Merge xs ys
  -- · exact hxs
  -- · exact hys
  -- · simp_all
  -- · simp_all

-- We are ready to prove the main sorted merge.
-- discuss a proof
#check Sorted.cons_min
#check sorted_min
#check sorted_suffix

theorem sorted_merge (l1 l2 : List ℕ) (hxs: Sorted l1) (hys: Sorted l2)
  : Sorted (Merge l1 l2) := by
  fun_induction Merge l1 l2
  · exact hxs
  · exact hys
  · apply Sorted.cons_min
    apply sorted_min at hxs
    apply sorted_min at hys
    · apply min_all_merge
      exact hxs
      grind
    -- non_recursion
    · apply ih1
      · exact sorted_suffix hxs
      . exact hys
  · apply Sorted.cons_min
    apply sorted_min at hxs
    apply sorted_min at hys
    · apply min_all_merge
      · grind
      · grind
    -- non-recursion
    · apply ih1
      · exact hxs
      · exact sorted_suffix hys

-- c.f. with recursive proofs.
theorem sorted_merge_rec (l1 l2 : List ℕ) (hxs: Sorted l1) (hys: Sorted l2)
  : Sorted (Merge l1 l2) := by
  match l1,l2 with
  | x, [] => simpa [Merge]
  | [],x => unfold Merge; aesop
  | x::xs, y::ys =>
    simp [Merge]
    split_ifs with h
    · apply Sorted.cons_min
      apply sorted_min at hxs
      apply sorted_min at hys
      · apply min_all_merge
        · grind
        · grind
      -- recursion
      · apply sorted_merge
        · exact sorted_suffix hxs
        · exact hys
    · apply Sorted.cons_min
      apply sorted_min at hxs
      apply sorted_min at hys
      · apply min_all_merge
        · grind
        · grind
      -- recursion
      · apply sorted_merge
        · exact hxs
        · exact sorted_suffix hys

-- Exercise 2.3
theorem merge_min_out (x : ℕ) (xs ys : List ℕ)
  (h_min_in_xs : ∀ y ∈ xs, x ≤ y)
  : Merge (x :: ys) xs = x :: Merge ys xs := by
  -- # Why matching xs only:
  -- Only the variation in `xs` (whether `[]` or not) leads to different cases in the `Merge` definition
  match xs with
  | [] => simp [Merge];
  | z::z_xlist =>
    -- `conv` to handle *equation goal: f(a)=g(b)*
    conv =>
      left
      unfold Merge
      -- simp [Merge]
    split_ifs with h
    · rfl
    · simp at h
      -- # this case is actually impossible
      -- exfalso
      have : x ≤ z := by
        -- aesop
        apply h_min_in_xs
        simp
      linarith
      -- omega

-- Exercise 2.4
theorem merge_min_out_sym
  (x : ℕ) (xs ys : List ℕ)
  (h_min_in_xs : ∀ y ∈ xs, x ≤ y)
  (h_min_in_ys : ∀ y ∈ ys, x ≤ y)
  : Merge ys (x::xs) = x :: Merge ys xs := by
  -- # Why matching ys only:
  -- Only the variation in `ys` (whether `[]` or not) leads to different cases in the `Merge` definition
  match ys with
  | [] => unfold Merge; aesop
  | y::y_ylist =>
    conv =>
      left
      unfold Merge
    split_ifs with h
    swap
    · rfl
    · have : x ≤ y := by aesop
      observe : x = y
      -- substitute all occurrance
      subst this
      suffices Merge y_ylist (x :: xs) = x :: Merge y_ylist xs by
      -- Assume we have `Merge y_ylist (x :: xs) = x :: Merge y_ylist xs`,
      -- we can finish the goal by rewriting and applying known lemmas.
      -- Same as `have : Merge y_ylist (x :: xs) = x :: Merge y_ylist xs := by ...`
        rw [this]
        rw [merge_min_out]
        exact h_min_in_xs
      apply merge_min_out_sym
      · aesop
      · aesop
