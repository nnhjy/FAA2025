import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
set_option tactic.hygienic false

set_option pp.proofs true

/-!
## Calculation Proofs
Lean provides a powerful suite of "tactics" that can perform calculations, simplify expressions, and even solve entire goals automatically.
-/

/-! basic tactics
* `simp` -- perform a sequence of simplifications.
* `grw` -- same as rw [e], but e can be a relation other than = or ↔
* `rel` -- apply `grw` to solve a relational goal by "substitution"
* `rw??` -- specific `rw` by clicking in the info view
* `gcongr` -- reduce a relational goal between a LHS and RHS matching the same pattern and outputs new simplified subgoals

-- Solver
* `norm_num` -- solve equalities/inequality involving literals (e.g., 3+1 ≤ 4, 1+1 = 2, 3 ≠ 4)
* `ring` --   solve expressions in commutative (semi)rings, allowing for variables in the exponent.
* `ring_nf` -- put the expression into a `normal' form
* `omega` --  solve integer and natural linear arithmetic problems.
* `linarith` -- solve linear arithmetic over the rationals

-- Powerful automation tactics
* `aesop` -- general-purpose automation tactic
          -- can handle a wide variety of goals, including those involving inductive types, algebraic structures, and logical reasonin
          -- allow customiseing the tactic behavior using aesop rules
* `grind` -- combines `simp`, `intro`, `cases`, `contradiction`, etc.
too powerful automation (we will not use these two this week)
-/


example : (1 : ℕ) + 1 ≠ 6 := by
  norm_num

example : (3.141 : ℝ) + 2.718 = 5.859 := by
  norm_num

example {a b x c d : ℝ} (h1 : a+1 ≤ b+1) (h2 : c ≤ d) :
  x ^ 2 * a + c ≤ x ^ 2 * b + d := by
  gcongr
  linarith

-- Example on grw/rel/gcongr
example {a b x c d : ℝ} (h1 : a ≤ b) (h2 : c ≤ d) :
  x ^ 2 * a + c ≤ x ^ 2 * b + d := by
  gcongr

example (a b c d: ℝ)(h₁ : a < b) (h₂ : b ≤ c) : a + d ≤ c + d := by
  grw [h₁, h₂]

example (a b c d: ℝ)(h₁ : a < b) (h₂ : b ≤ c) : a + d ≤ c + d := by
  -- Method 1:
  -- grw [← h₂, ← h₁]

  -- Method 2:
  calc
    a+d ≤ b+d := by grw [h₁]
    _   ≤ c+d := by grw [h₂]


-- Example
theorem power_two_ih (n : ℕ) (ih : 5 ≤ n) (h : 2 ^ n > n ^ 2) : 2 ^ (n + 1) > (n + 1) ^ 2 := by
  -- Method 1:
  -- grw [Nat.pow_add_one', h, add_sq n 1, Nat.two_mul (n ^ 2), add_assoc]
  -- simp only [mul_one, one_pow, gt_iff_lt, add_lt_add_iff_left]
  -- rw [Nat.pow_two n]
  -- calc
  --   2 * n + 1 < 5 * n := by omega
  --   _ ≤ n*n := by grw [ih]

  -- Method 2:
  rw [Nat.two_pow_succ n]
  rw [add_sq n 1]
  grw [h]
  simp
  rw [add_assoc]
  simp
  rw [Nat.pow_two n]
  calc
    2*n +1 < 5*n := by omega
    _ ≤ n*n := by grw [ih]


-- How to know we can use Nat? -> check for type ℕ in Mathlib docs
-- How to know there is `add_sq` as a function? -> type `rw?` for lean4 suggestions

--Alternate Proof
theorem power_two_ih_alt (n : ℕ) (ih : 5 ≤ n) (h : 2 ^ n > n ^ 2) : 2 ^ (n + 1) > (n + 1) ^ 2 := by
   calc 2 ^ (n + 1) = 2 * 2 ^ n := by ring
        _ > 2 * n ^ 2 := by omega -- `omega` uses `h`
        -- _ ≥ 2 * n ^ 2 := by grw [h]
        _ = n ^ 2 + n*n := by ring
        _ ≥ n ^ 2 + 5 * n := by
          simp only [ge_iff_le, add_le_add_iff_left]
          exact Nat.mul_le_mul_right n ih
        _ > n ^ 2 + 2 * n + 1 := by omega
        _ = (n + 1) ^ 2 := by ring

-- `_` comes with `calc`

-- Exercise 1
-- try without omega
theorem power_two_linear (n : ℕ) (ih : 3 ≤ n) (h : 2*n < 2^n) : 2*(n+1) < 2^(n+1) := by
  rw [mul_add_one 2 n]
  grw [h]
  rw [Nat.two_pow_succ n]
  simp
  -- grw [← ih]
  -- repeat norm_num
  calc
    2 < 2^3 := by norm_num
    _ ≤ 2^n := by
      gcongr
      norm_num

-- Exericse 2
-- prove this without omega
example (n:ℕ ) (h: 5 ≤ n): 1 + n * 2 < 5*n := by
  rw [Nat.mul_comm]
  rw [@Nat.add_lt_iff_lt_sub_right]
  rw [← Nat.mul_sub_right_distrib]
  norm_num
  grw [← h]
  norm_num
