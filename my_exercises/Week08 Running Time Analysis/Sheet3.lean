import Mathlib.Tactic -- imports all of the tactics in Lean's maths library
import Lectures.Week08.Sheet2
import Lectures.Week08.API

-- Running Time Analysis
set_option autoImplicit false
set_option tactic.hygienic false

-- The following helper lemmas are useful
@[simp] theorem merge_time (xs ys : List ℕ) :
  (merge xs ys).time = xs.length + ys.length := by
  simp [merge]
  fun_induction merge.go <;> simp_all
  all_goals grind

@[simp] theorem merge_ret_length_eq_sum (xs ys : List ℕ) :
  (merge xs ys).ret.length = xs.length + ys.length := by
  simp [merge]
  fun_induction merge.go <;> simp_all
  all_goals grind

@[simp] theorem mergeSort_same_length (xs : List ℕ) :
  (mergeSort xs).ret.length = xs.length:= by
  fun_induction mergeSort <;> simp_all
  subst left right n
  simp only [List.length_take, List.length_drop, half]
  have : half < x.length := by omega
  omega

/- # Next, we pave our way towards proving O(n log n) running time of merge sort.
- The direct proof of the `example` is extremely difficult
  example (xs : List ℕ) (h : ∃ k, xs.length = 2 ^ k) :
  (mergeSort xs).time = xs.length*(Nat.log 2 xs.length) := by sorry

This is because:
1. **Complex recursive structure**:
  `mergeSort` has a messy recursion pattern with `take` and `drop`, making it hard to reason about directly.
2. **The divide-and-conquer split isn't clean**:
  When you split a list of length `n`, you get lengths `⌊n/2⌋` and `⌈n/2⌉`, which makes the recurrence relation complicated.
3. **The abstraction helps**: By introducing `MS_REC` as below as an abstract recurrence relation, you:
   - **Step 1**: Prove `mergeSort.time = MS_REC` (connects implementation to math)
   - **Step 2**: Prove `MS_REC (2^k) = MS_REC_SIMP (2^k)` (simplify the recurrence for powers of 2)
   - **Step 3**: Prove `MS_REC_SIMP (2^k) = 2^k * k` (solve the simplified recurrence)
   - **Step 4**: Combine everything to get the final result

This is a classic **proof by refinement** strategy:

mergeSort.time  →  MS_REC  →  MS_REC_SIMP  →  closed form (n log n)
  (messy impl)    (general)   (power of 2)     (final answer)
-/

def MS_REC : ℕ → ℕ
| 0 => 0
| n@(x+1) =>
/- `@` is called an as-pattern, here it means
  - Bind the whole value to `n`
  - Match `n` as `x+1` (decompose `n` into successor form)
  So you get both the original value `n` and its decomposition `x` simultaneously.
  This is useful because you need both `n` (for `n/2` and `+ n`) and `x` (to check if `x = 0`, i.e., if `n = 1`).
-/
  if x = 0 then 0
  else
    -- let n:= x+1 <=> n@(x+1)
    MS_REC (n/2) + MS_REC ((n-1)/2 + 1) + n

#eval mergeSort [4,1,3,4,5,6]
#eval MS_REC 6

/- ## Why uppercase function names?
  The uppercase naming (`MS_REC`, `MS_REC_SIMP`) is a convention to indicate these are *mathematical recurrence relations* rather than executable code.
  It helps distinguish:
  - `mergeSort` - the actual algorithm implementation
  - `MS_REC` - the mathematical recurrence that describes its time complexity
  - `MS_REC_SIMP` - a simplified version of the recurrence
-/

theorem mergeSort_time_eq_MS_REC (xs : List ℕ) :
  (mergeSort xs).time = MS_REC xs.length := by
  fun_induction mergeSort
  · simp only [pure, TimeM.pure]
    unfold MS_REC
    grind
    -- simp only [Pure.pure, pure]
    -- unfold MS_REC
    -- simp_all
    -- grind
  · simp_all only [not_lt, Bind.bind, TimeM.time_of_bind, merge_time, mergeSort_same_length]
    conv =>
      right
      unfold MS_REC
    simp_all
    split
    · simp_all
    · simp_all
      grind

    -- simp only [bind, TimeM.time_of_bind]
    -- simp only [merge_time]
    -- simp only [mergeSort_same_length]
    -- unfold MS_REC
    -- simp_all
    -- split
    -- · simp_all
    -- · simp_all
    --   grind

def MS_REC_SIMP : ℕ → ℕ
| 0 => 0
| n@(x+1) =>
  if x = 0 then 0
  else
    2*MS_REC_SIMP (n/2) + n

theorem MS_REC_SIMP_EQ (n : ℕ)
  : (MS_REC (2^n))= (MS_REC_SIMP (2^n)) := by
  induction' n  with n ih
  · unfold MS_REC_SIMP MS_REC
    simp only [↓reduceIte]
  · unfold MS_REC_SIMP MS_REC
    split <;> all_goals (simp_all)
    rename_i heq
    split
    next h =>
      subst h
      simp_all only [zero_add, Nat.pow_eq_one, OfNat.ofNat_ne_one, Nat.add_eq_zero, one_ne_zero, and_false, or_self]
    next h =>
      simp_all only [Nat.add_right_cancel_iff]
      rw [← heq]
      grind

theorem MS_REC_SIMP_EQ_CLOSED (n : ℕ) : MS_REC_SIMP (2^n) = 2^n * n := by
  induction' n  with n ih
  · unfold MS_REC_SIMP
    simp_all only [↓reduceIte, pow_zero, mul_zero]
    -- aesop
  · unfold MS_REC_SIMP
    simp_all only
    split
    next heq =>
      simp_all only [Nat.pow_eq_zero, OfNat.ofNat_ne_zero, ne_eq, Nat.add_eq_zero, one_ne_zero, and_false,
        not_false_eq_true, and_true]
    next heq =>
      simp_all only [Nat.succ_eq_add_one]
      split
      next h =>
        subst h
        simp_all only [zero_add, Nat.pow_eq_one, OfNat.ofNat_ne_one, Nat.add_eq_zero, one_ne_zero, and_false, or_self]
      next h =>
        rw [← heq]
        grind

-- The time is written assuming the length of the list is a power of two (for simplicity).
theorem MStimeBound (xs : List ℕ) (h : ∃ k, xs.length = 2 ^ k) :
  (mergeSort xs).time = xs.length*(Nat.log 2 xs.length) := by
  rw [mergeSort_time_eq_MS_REC]
  obtain ⟨k,hk⟩ := h
  rw [hk,MS_REC_SIMP_EQ,MS_REC_SIMP_EQ_CLOSED]
  simp only [Nat.lt_add_one, Nat.log_pow]
