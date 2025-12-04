import Mathlib.Tactic -- imports all of the tactics in Lean's maths library
set_option autoImplicit false
set_option tactic.hygienic false
-- set_option diagnostics true

-- DO NOT CHANGE THE THEOREM STATEMENT
-- Fill in the sorry

-- Most tactics are welcome.
-- You are now allowed to use `aesop` and `grind` tactics.

-- # Problem 1
def SumOdd : ℕ → ℕ
  | 0 => 0
  | n + 1 => SumOdd n + (2*n +1)

theorem P1 (n : ℕ) : SumOdd (n) = n^2 := by
  induction' n with i ih
  · simp; rfl
  · unfold SumOdd
    rw [ih]
    linarith

-- # Problem 2 and 3
def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n
notation:10000 n "!" => factorial n

def isEven (n : ℕ) : Prop := ∃ k, n = 2*k

theorem P2 (n : ℕ) : isEven (n)! ↔ n ≥ 2 := by
  constructor
  · unfold isEven
    contrapose!
    intro hn
    intro k
    by_contra
    have h : n = 0 ∨ n = 1 := by omega
    obtain n0 | n1 := h
    · rw [n0] at a
      unfold factorial at a
      omega
    · rw [n1] at a
      unfold factorial at a
      rw [factorial] at a
      simp at a
      omega
  · unfold isEven
    intro h_n2
    induction' n,h_n2 using Nat.le_induction with i ih
    unfold factorial
    · simp [factorial]
    · obtain ⟨k_i, eq_i⟩ := a
      unfold factorial
      rw [eq_i]
      rw [Nat.mul_left_comm]
      use (i + 1) * k_i

theorem P3 : ∀ n > 0 , 3 ^ n > n ^ 2 := by
  intro n h_n
  induction' n, h_n using Nat.le_induction with i ih
  · simp
  · simp at ih

    if i=1 then
      rename_i i1
      rw [i1]
      omega
    else
      rename_i ix1

      if i = 2 then
        rename_i i2
        rw [i2]
        omega
      else
        rename_i ix2
        rw [@Nat.pow_add_one']
        rw [Nat.add_one_mul]
        rw [Nat.add_one_mul]
        rw [@add_sq]
        rw [Nat.one_mul]
        rw [Nat.mul_one]
        have igt2 : i > 2 := by omega
        have t1 : 3^i > 1 := by
          grw [igt2]
          norm_num
          trivial

        if i = 3 then
          rename_i i3
          rw [i3]
          omega
        else
          rename_i ix3
          have t2_ : 3 < i := by omega
          have t2 : i^2 > 2*i := by
            rw [Nat.pow_two]
            simp only [gt_iff_lt]
            rw [propext (Nat.mul_lt_mul_right ih)]
            trivial
          linarith



-- # Problem 4:
-- in this problem, you are asked to solve the following recurrence relation.
-- g(n) = g(n/2) + 1, g(0) = 0
-- Prove that that g(n) ≤  Nat.log 2 n + 1 for all n
-- state the formal theorem and prove it

-- The following lemmas can be helpful
#check Nat.sub_add_cancel
#check Nat.le_log_of_pow_le

def g (n : ℕ) : ℕ :=
  if n = 0 then 0
  else g (n/2) + 1

-- def g: ℕ → ℕ
--   | 0  => 0
--   | n => g (n/2) + 1
--  # why this way doesn't work, neither for ℚ?
--  # what is the difference between the 2 ways of definition?

def g_close (n :ℕ ) : ℕ :=  Nat.log 2 n + 1

#eval Nat.log 2 ((1/2)*2) = 0

--  # what is the difference between stating the ∀ and not?
theorem P4 : ∀ n, g (n) ≤ Nat.log 2 n + 1 := by
  intro n
  induction' n using Nat.div2Induction with i ih

  if i=0 then
    rename_i i0
    simp [i0]
    unfold g
    simp_all

  else
    rename_i ix0
    have i_pos : i > 0 := by omega
    have h_start : g (i / 2) ≤ Nat.log 2 (i / 2) + 1 := by omega

    have h1 : g (i / 2) + 1 ≤ Nat.log 2 (i / 2) + 1 + 1 := by grw [h_start]

    -- have val_log2_2 : Nat.log 2 2 = 1 := by norm_num
    have h2 : g (i / 2) + 1 ≤ Nat.log 2 (i / 2) + Nat.log 2 2 + 1 := by
      norm_num
      simp at h1
      trivial

    have h3 : g i ≤ Nat.log 2 (i / 2) + Nat.log 2 2 + 1 := by
        unfold g
        simp [ix0]
        simp at h2
        exact h2

    have h4 (_h : i ≥ 2) : Nat.log 2 (i / 2) + Nat.log 2 2 = Nat.log 2 i := by
      norm_num
      rw [Nat.sub_add_cancel]
      exact Nat.succ_le_of_lt (Nat.log_pos (by decide) (by linarith))
    -- have h2b: Nat.log 2 i = Nat.log 2 ((i / 2) * 2) := by
    --   rw [Nat.log_div_mul_self]

    if i=1 then
      rename_i i1
      unfold g
      simp [i1]
      unfold g
      simp

    else
      rename_i ix1
      have i_vals : i = 1 ∨ i ≥ 2 := by omega
      simp [ix1] at i_vals
      simp [i_vals] at h4
      simp [h4] at h3
      exact h3


-- # Problem 5
-- in this problem, you are asked to solve the following recurrence relation.
-- f(n) = 2*f(n-1) - f(n-2) + 2
-- where f(0) = 1 and f(1) = 1
-- Prove that that f(n) = n^2 - n + 1

-- state the formal theorem and prove it
-- Hint: you may find `zify` tactic useful

def f : Nat → Nat
  | 0   => 1
  | 1   => 1
  | n+2 => 2* f (n+1) - f (n) + 2
  -- | n => 2* f (n-1) - f (n-2) + 2
  -- # why the latter definition not working? -> (n-1) or (n-2) can go beyond Nat?

theorem P5 (n :ℕ ) : f (n) = n^2 - n + 1 := by
  induction' n using Nat.twoStepInduction with i fi fi1
  · simp [f]
  · simp [f]
  · if i=0 then
      rename_i i0
      simp [i0]
      unfold f
      rfl
    else
      rename_i i_neq_0
      have i_gt_0 : i > 0 := by omega
      simp at fi
      have i_add_1_gt_0 : i + 1 > 0 := by omega
      simp at fi1

      rw [Nat.pow_two] at *

      have i_ge_1 : i ≥ 1 := by omega
      have h_l1 : i * i ≥ i := by simp_all

      zify [h_l1] at fi

      have h_l2a : 1 + i * 2 + i * i ≥ (1 + i) := by
        grw [h_l1]
        linarith

      have h_l2b : (i + 1) * (i + 1) ≥ (1 + i) := by
        ring_nf
        rw [Nat.pow_two]
        exact h_l2a

      rw [Nat.right_distrib] at fi1
      rw [Nat.left_distrib, Nat.left_distrib] at fi1
      simp at fi1
      zify [h_l2a] at fi1

      have h_r : (i + 2) * (i + 2) ≥ i + 2 := by
        ring_nf
        rw [Nat.pow_two]
        omega

      unfold f
      simp

      have h_l : 2 * f (i + 1) ≥ f i := by
        zify
        rw [fi, fi1]
        ring_nf
        linarith

      zify [h_l, h_r]
      rw [fi1, fi]
      ring_nf

/-! # GRADING FEEDBACK
   Score: 100/100
   Q1: 20/20
   Q2: 20/20
   Q3: 20/20
   Q4: 20/20
   Q5: 20/20


  Re: your comment about definition patterns - You're exactly right! The pattern
   `| n => 2*f(n-1) - f(n-2) + 2` doesn't work because natural number subtraction
   is saturating (0-1=0), so Lean cannot verify termination. The `| n+2 => ...`
   pattern explicitly shows we're recursing on smaller values.


   Excellent work!
-/
