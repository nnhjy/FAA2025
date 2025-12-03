import Mathlib.Tactic

set_option autoImplicit false
set_option tactic.hygienic false

-- For Problem 1 and 2, we work on the binary search algorithm for bitonic sorted array

def Bitonic (f : ℕ → ℤ) (n : ℕ) : Prop :=
  ∃ k, k < n
  ∧ StrictMonoOn f (Set.Icc 0 k)   -- nondecreasing on [0,k]
  ∧ StrictAntiOn f (Set.Ici k)     -- nonincreasing on [k, ∞)

-- A "bitonic" array is an array that strictly increases and then strictly decreases, like [1, 4, 8, 10, 5, 2]. The goal is to find the "peak" element (10). The search logic is:
-- Look at mid and mid+1.
-- If arr.get mid < arr.get (mid+1), the peak must be in the right half.
-- If arr.get mid > arr.get (mid+1), the peak is in the left half (and mid could be it).

def IsMaximum (f : ℕ → ℤ) (n : ℕ) (k : ℕ) : Prop :=
  k < n ∧ ∀ i < n, f i ≤ f k

structure BitonicSortedArrayFun (n :ℕ) where
  get : ℕ → ℤ
  size : ℕ := n
  bitonic: Bitonic get n

-- This property appears in the analysis, marking noncomoputable is fine.
noncomputable
def BitonicSortedArrayFun.peak_idx {n :ℕ} (arr: BitonicSortedArrayFun n) := (arr.bitonic).choose
lemma BitonicSortedArrayFun.peak_idx_spec {n :ℕ} (arr: BitonicSortedArrayFun n)
  : arr.peak_idx < n
  ∧ StrictMonoOn arr.get (Set.Icc 0 arr.peak_idx)
  ∧ StrictAntiOn arr.get (Set.Ici arr.peak_idx) := (arr.bitonic).choose_spec

-- # Problem 1 (20 pts): prove that BitonicSortedArrayFun has a unique maximum which is arr.peak_idx
theorem Problem1 {n : ℕ} (arr : BitonicSortedArrayFun n) :
  IsMaximum arr.get n arr.peak_idx
  ∧ ∀ (y : ℕ), IsMaximum arr.get n y → y = arr.peak_idx := by
  have := arr.peak_idx_spec
  constructor
  · constructor
    · exact this.1
    · intro i h_i
      simp [StrictMonoOn, StrictAntiOn] at this
      grind
  · intro y h_max_idx_y
    unfold IsMaximum at h_max_idx_y

    by_cases h_case : y < arr.peak_idx
    · have h_mono := this.2.1
      have h_y_in : y ∈ (Set.Icc 0 arr.peak_idx) := by
        simp [Set.Icc]
        gcongr
      have h_peak_in : arr.peak_idx ∈ (Set.Icc 0 arr.peak_idx) := by
        simp [Set.Icc]
      have h_value_idy_lt_peak : arr.get y < arr.get arr.peak_idx := by
        apply h_mono
        apply h_y_in
        apply h_peak_in
        exact h_case
      have h_value_idy_ge_peak: arr.get arr.peak_idx ≤ arr.get y := by
        apply h_max_idx_y.2
        exact this.1
      linarith

    · simp at h_case
      by_cases h_y_gt : arr.peak_idx < y
      · have h_anti := this.2.2
        have h_y_in : y ∈ (Set.Ici arr.peak_idx) := by
          simp [Set.Ici]
          gcongr
        have h_peak_in : arr.peak_idx ∈ (Set.Ici arr.peak_idx) := by
          simp [Set.Ici]
        have h_value_idy_lt_peak : arr.get y < arr.get arr.peak_idx := by
          apply h_anti
          apply h_peak_in
          apply h_y_in
          exact h_y_gt
        have h_value_idy_ge_peak: arr.get arr.peak_idx ≤ arr.get y := by
          apply h_max_idx_y.2
          exact this.1
        linarith
      · linarith

-- # Problem 2 (30 pts): Prove that the following binary search algorithm returns index of maximum value in an bitonic array.
def find_idx_peak {n : ℕ}(arr : BitonicSortedArrayFun n) : ℕ :=
  aux 0 (n-1) where
  aux (a b : ℕ) (h : a ≤ b := by omega) : ℕ :=
    if h_eq : a = b then a
    else
      let mid := (a+b) / (2 :ℕ)
      if arr.get mid < arr.get (mid + 1) then
        -- We are on the increasing slope, so the peak is in the right half.
        aux (mid + 1) b
      else
        -- We are on the decreasing slope (or mid is the peak).
        -- The peak is in the left half, including mid.
        aux a mid

def IsPeakInRange {n :ℕ }(arr : BitonicSortedArrayFun n) (a b: ℕ): Prop :=
  arr.peak_idx ∈ Set.Icc a b

-- (20 pts)
-- Formulate and prove the following intermediate statement statement in Lean:
-- The index of the peak is in the range [a,b] if and only if the algorithm find_idx_peak.aux is correct on [a,b].

-- State the theorem and prove it
-- [theorem Problem2A_find_peak_correct_range]
theorem Problem2A_find_peak_correct_range (n a b : ℕ)
  (arr : BitonicSortedArrayFun n) (h_le : a ≤ b)
  : (IsPeakInRange arr a b) ↔ (find_idx_peak.aux arr a b h_le) = arr.peak_idx := by
  have := arr.peak_idx_spec
  fun_induction find_idx_peak.aux

  -- Case 1: a=b
  · constructor
    · intro h_range
      simp_all [IsPeakInRange]
    · intro h_peak_idx
      simp_all [IsPeakInRange]

  --  Case 2: nondecreasing
  · have h_temp_1a : (IsPeakInRange arr (mid + 1) b_1) → (IsPeakInRange arr a_1 b_1) := by
      unfold IsPeakInRange
      simp [Set.Icc]
      grind

    -- This is ensured by the case hypothesis h_2 for being in the nondecreasing side
    have h_temp_1b : (IsPeakInRange arr a_1 b_1) → (IsPeakInRange arr (mid + 1) b_1) := by
      unfold IsPeakInRange
      simp [Set.Icc]
      have h_le_mid : mid ≤ (mid+1) := by omega
      intro h_a_le h_b_le
      constructor
      · by_contra h_neg
        push_neg at h_neg
        have h_peak_le_mid : arr.peak_idx ≤ mid := by omega

        by_cases h_eq : arr.peak_idx = mid
        · -- Case: peak_idx = mid
          rw [← h_eq] at h_2
          have h_anti := this.2.2
          have : arr.get (arr.peak_idx + 1) < arr.get arr.peak_idx := by
            apply h_anti
            · simp [Set.Ici]
            · simp [Set.Ici]
            · omega
          linarith
        · -- Case: peak_idx < mid
          have h_peak_lt_mid : arr.peak_idx < mid := by omega
          have h_anti := this.2.2
          have : arr.get (mid + 1) < arr.get mid := by
            apply h_anti
            · simp [Set.Ici]; omega
            · simp [Set.Ici]; omega
            · omega
          linarith
      · exact h_b_le
    grind

  --  Case 3: nonincreasing
  · simp at h_2

    have h_temp_1a : (IsPeakInRange arr a_1 mid) → (IsPeakInRange arr a_1 b_1) := by
      unfold IsPeakInRange
      simp [Set.Icc]
      grind

    -- This is ensured by the case hypothesis h_2 for being in the nonincreasing side
    have h_temp_1b : (IsPeakInRange arr a_1 b_1) → (IsPeakInRange arr a_1 mid) := by
      unfold IsPeakInRange
      simp [Set.Icc]
      have h_le_mid : mid ≤ (mid+1) := by omega
      intro h_a_le h_b_le
      constructor
      · grind
      · by_contra h_neg
        push_neg at h_neg
        have h_peak_le_mid : arr.peak_idx ≥ mid := by omega

        by_cases h_eq : arr.peak_idx = mid
        · -- Case: peak_idx = mid
          rw [← h_eq] at h_2
          have h_anti := this.2.2
          have : arr.get (arr.peak_idx + 1) < arr.get arr.peak_idx := by
            apply h_anti
            · simp [Set.Ici]
            · simp [Set.Ici]
            · omega
          linarith
        · -- Case: peak_idx > mid
          have h_peak_lt_mid : arr.peak_idx > mid := by omega
          have h_anti := this.2.1
          have : arr.get (mid + 1) > arr.get mid := by
            apply h_anti
            · simp; omega
            · simp; omega
            · omega
          linarith
    grind

-- (10 pts): Use the formulation in the previous step to prove the correctness of this algorithm.
theorem Problem2B_find_peak_correct {n :ℕ}
  (h: 0 < n)(arr : BitonicSortedArrayFun n)
  : (find_idx_peak arr) = arr.peak_idx := by
  have := arr.peak_idx_spec
  unfold find_idx_peak
  have : IsPeakInRange arr 0 (n-1) := by
    unfold IsPeakInRange
    simp
    grind
  grind [Problem2A_find_peak_correct_range]

-- # Problem 3 (20 pts): Implement this function

def safeDivide (x y : ℕ) : Option ℕ :=
  if y = 0 then none else some (x / y)

/-
Implement a function that computes: ((a * b) / c) - ((d * e) / f)

Requirements:
1. Multiply a * b, then divide by c (use safeDivide)
2. Multiply d * e, then divide by f (use safeDivide)
3. Subtract the second result from the first
4. Return none if any division fails or if subtraction would be negative

You'll need this helper:
-/
def safeSub (x y : ℕ) : Option ℕ :=
  if x >= y then some (x - y) else none

/-
Part A: Implement using do notation
-/

def Problem3A (a b c d e f : ℕ) : Option ℕ := do
  -- Your code here
  let mult_1 := a * b
  let mult_2 := d * e
  let x ← safeDivide mult_1 c
  let y ← safeDivide mult_2 f
  let result ← safeSub x y
  pure result

#eval Problem3A 20 3 4 5 4 2
#eval Problem3A 20 0 4 5 4 2
#eval Problem3A 2 3 6 5 4 2

/-
Part B: Implement the SAME function WITHOUT do notation
(translate your do notation to explicit >>= operator:)
-/

def Problem3B (a b c d e f : ℕ) : Option ℕ :=
  -- Your code here
  let mult_1 := a * b
  let mult_2 := d * e
  safeDivide mult_1 c >>= fun x =>
  safeDivide mult_2 f >>= fun y =>
  safeSub x y >>= fun result =>
  pure result

#eval Problem3B 20 3 4 5 4 2
#eval Problem3B 20 0 4 5 4 2
#eval Problem3B 2 3 6 5 4 2

/- ## Problem 4 (30 pts): Monadic structure on lists
`List` can be viewed as a monad—like `Option`, but allowing multiple possible results. The code below defines `List` as a monad. -/

namespace List

#check List
#print List

def bind {α β : Type} : List α → (α → List β) → List β
  | [],      _ => []
  | a :: as, f => f a ++ bind as f

def pure {α : Type} (a : α) : List α := [a]

-- Problem 4A (10 pt): Prove the following.
theorem Problem4A {α β : Type} (a : α) (f : α → List β)
  : bind (pure a) f = f a := by
  -- unfold List.bind List.pure
  -- aesop
  induction' [a] <;> grind [List.pure, List.bind]

-- Problem 4B (10 pt): Provce the following
theorem Problem4B {α : Type} :
  ∀as : List α, bind as pure = as := by
  intros as

  -- induction as with
  -- | nil =>
  --   unfold List.bind
  --   rfl
  -- | cons a as ih =>
  --   unfold bind pure
  --   simp
  --   exact ih

  induction' as
  · unfold List.bind; rfl
  . unfold List.bind List.pure
    simp
    exact tail_ih

-- Helper lemma: bind distributes over append
theorem bind_append {α β : Type} (f : α → List β) :
  ∀xs ys : List α, bind (xs ++ ys) f = bind xs f ++ bind ys f := by
  intros xs ys

  induction xs with
  | nil =>
    unfold List.bind; simp
  | cons head tail =>
    unfold List.bind
    simp [tail_ih]
    aesop

-- Problem 4C (10 pt): Prove the following
-- the bind_append theorem may be useful
theorem Problem4C {α β γ : Type} (f : α → List β) (g : β → List γ) :
  ∀as : List α, bind (bind as f) g = bind as (fun a ↦ bind (f a) g) := by
  intros as

  induction as with
  | nil =>
    unfold List.bind
    rfl
  | cons head tail ih =>
    simp only [List.bind]
    --  `unfold List.bind` does too much

    rw [bind_append]
    rw [ih]

end List
