import Mathlib.Tactic -- imports all of the tactics in Lean's maths library
set_option autoImplicit false
set_option tactic.hygienic false

-- DO NOT CHANGE THE THEOREM STATEMENT
-- Fill in the sorry

-- All tactics are welcome.

-- # Problem 1
-- Prove that the list reverse operation does not change the length of the list.
def reverse {α : Type} : List α → List α
| [] => []
| a :: xs => reverse xs ++ [a]

def len {α : Type} : List α → ℕ
| []     =>  0
| _ :: xs => 1 + len xs

-- Hint: use induction over the list
theorem problem1 (xs: List ℕ): len xs = len (reverse xs) := by
  -- missing lemma to complete the proof
  have lemma1 {α : Type} (l : List α) (a : α) :
    len (l ++ [a]) = len l + 1 := by
    induction l with
    | nil => simp [len]
    | cons x xlist ih => simp [len, ih]; grind

  -- Approach 1:
  -- fun_induction len xs
  -- · simp [reverse, len]
  -- · simp [reverse]
  --   rw [ih1, lemma1]
  --   grind

  -- Approach 2:
  -- induction xs with
  -- | nil => rfl
  -- | cons a alist ih =>
  --   simp [reverse, len]
  --   rw [ih, lemma1]
  --   grind

  -- Approach 3:
  match xs with
  | [] => rfl
  | x :: xlist =>
    simp [reverse, len, lemma1]
    simp [← problem1 xlist]
    grind

-- # Problem 2: Consider the following rescursive function
/-
S(n, k):
  S(0, 0) = 1
  S(0, k) = 0
  S(n, 0) = 0
  S(n+1, k) = 1 if n + 1 = k
          = k * S(n, k) + S(n, k-1) otherwise,
where n, k ∈ ℕ
-/
def S : ℕ → ℕ  → ℕ
  | 0, 0 => 1
  | 0, _ => 0
  | _, 0 => 0
  | n+1, k =>
    if n + 1 = k then 1
    else k* (S n k) + (S n (k-1))

#check Nat.twoStepInduction
#eval S 0 1
-- Hint: use induction over n
theorem problem2 (n: ℕ) (h: 0 < n): (S n 1) = 1 := by
  induction' n using Nat.twoStepInduction with i h_i h_i1
  · contradiction
  · simp [S]
  · unfold S
    by_cases h0 : i + 1 + 1 = 1
    · grind
    · simp
      simp at h0
      simp at h_i1
      simp [h_i1]
      unfold S
      rfl

-- # Problem 3
-- This is a continuation of Problem 2
-- You may want to use the result from theorem problem2 to prove problem3
#eval S 0 2
#eval 2^(0-1) - 1
theorem problem3 (n: ℕ): (S n 2) = 2^(n-1) - 1  := by
  induction' n with i h_i
  · simp [S]
  · simp [S]
    by_cases h_eq1 : i = 1
    · simp [h_eq1]
    · simp [h_eq1]
      by_cases h_gt1 : 1 < i
      · have h_pos : 0 < i := by omega
        rw [problem2 i h_pos, h_i]
        have temp_eq_1: (i + 1) - 1 = i := by omega
        have temp_eq_2: 2 * (2^(i - 1) - 1) + 1 = 2^((i + 1) - 1) - 1 := by
          ring_nf
          rw [Nat.sub_one_mul]
          rw [Nat.two_pow_pred_mul_two h_pos]
          rw [Nat.one_add_sub_one]
          rw [Nat.add_comm]
          have temp_pos_a : 2^i >= 2 := by
            grw [← h_gt1]
            · trivial
            · trivial
          have temp_pos_b : 2^i > 1 := by
            grw [← h_gt1]
            · trivial
            · trivial
          zify [temp_pos_a, temp_pos_b]
          linarith
        grind
      · have : i = 0 := by omega
        simp [this, S]

-- # Problem 4
/-
  Define R(r,s):
  R(r,2) = r
  R(2,s) = s
  R(r,s) = R(r-1,s) + R(r,s-1)
  Prove that R(r,s) ≤ (r+s-2).choose (r-1)
-/

def R (r s : ℕ ): ℕ :=
  if r = 0 ∨ s = 0 then 0
  else if r ≤ 1 ∨ s ≤ 1 then 1
  else if r = 2 ∨ s = 2 then 2
  else (R (r-1) s) + (R r (s-1))

-- You may find this useful
#check Nat.choose_eq_choose_pred_add

-- Hint: you may find functional induction useful
lemma problem4 (r s : ℕ): R r s ≤ (r+s-2).choose (r-1) := by
  fun_induction R r s
  · simp
  · obtain ⟨ h_r1 | h_s1 ⟩ := h_1
    · simp
    · grind
    · by_cases h_s1' : s_1 = 1
      · simp_all
      · simp_all
        grind
  · obtain ⟨ h_r1 | h_s1 ⟩ := h_2
    · simp_all
      grind
    · simp_all
      have temp_concl_rhs: r_1.choose (r_1 - 1) = r_1.choose 1 :=
        Nat.choose_symm (by omega)
      rw [temp_concl_rhs, Nat.choose_one_right]
      omega
  · rw [Nat.choose_eq_choose_pred_add]
    simp_all
    grw [ih1, ih2]
    · grind
    · grind
    · simp_all

-- # Problem 5.1

-- Part 1: Defining interleave function
-- Define a function called interleave that takes two lists, xs and ys, and returns a new list where the elements of xs and ys are alternated.
-- If one list is longer than the other, the remaining elements of the longer list should be appended at the end.

def interleave : List ℕ → List ℕ → List ℕ
  | xs, [] => xs
  | [], ys => ys
  | x::xs_sub, y::ys_sub => x::y::(interleave xs_sub ys_sub)

#eval interleave [1, 2, 3] [4, 5, 6]
#eval interleave [1, 2] [3, 4, 5, 6]
#eval interleave [1, 2, 3, 4] [5, 6]
#eval interleave [] [1, 2]
#eval interleave [1, 2] []
/--
 * interleave [1, 2, 3] [4, 5, 6] should produce [1, 4, 2, 5, 3, 6].
 * interleave [1, 2] [3, 4, 5, 6] should produce [1, 3, 2, 4, 5, 6].
 * interleave [1, 2, 3, 4] [5, 6] should produce [1, 5, 2, 6, 3, 4].
 * interleave [] [1, 2] should produce [1, 2].
 * interleave [1, 2] [] should produce [1, 2].
 --/

-- # Problem 5.2
-- Recall len and reverse functions from Problem 1
theorem problem5_part2 (xs ys: List ℕ): len (reverse (interleave xs ys))  = len (reverse (xs)) + len ys  := by
  match xs, ys with
  | [], [] =>
    rw [interleave, reverse, len]
  | x::xs_sub, [] =>
    simp [interleave, len]
  | [], y::ys_sub =>
    simp [interleave]
    rw [← problem1]
    simp [len, reverse]
  | x::xs_sub, y::ys_sub =>
    rw [← problem1, ← problem1]
    simp [len, interleave]
    -- rw [Nat.add_add_add_comm]
    ring_nf
    -- # Why this doesn't work to cancel out the number 2?
    -- rw [Nat.add_assoc, Nat.add_left_cancel]
    conv =>
      rhs
      congr
      · rhs
        rw [problem1]
    rw [problem1]
    rw [problem5_part2 xs_sub ys_sub]
    grind
