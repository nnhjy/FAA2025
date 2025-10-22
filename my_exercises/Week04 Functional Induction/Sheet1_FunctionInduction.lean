import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
--set_option tactic.hygienic false


/-
# Function Induction
So far, we have seen induction over ℕ. This week we will cover functional induction.
The core idea is that if a function is recursively defined, then you can prove it recursively as long as you show termination.
On the other hand, functional induction formalizes recursive proofs and tells you exactly what is needed to complete the proof.
These two proofs are equivalent, but they may give you different perspective to think about a problem.
-/

-- functional induction


def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n

#check factorial.induct
-- Recall induction proof
lemma fact (n :ℕ) : 1 ≤ n ! := by
  induction' n with n ih
  · rfl
  · unfold factorial
    grw [← ih]
    exact NeZero.one_le

lemma fact' (n :ℕ) : 1 ≤ n ! := by
  fun_induction factorial
  · rfl
  · expose_names
    grw [← ih1]
    exact NeZero.one_le

-- Pascal sum

/-
P(a,b):
  P(a,0) = 1,
  P(0,b+1) = 1,
  P(a+1,b+1) = P(a+1,b) + P(a,b+1)
-/
def P : ℕ → ℕ → ℕ
  -- output 1 is independent of a
  | _, 0 => 1
  -- output 1 is indipendent of b
  | 0, _ + 1 => 1
  | a + 1, b + 1 => P (a + 1) b + P a (b + 1)

/-
ℕ → ℕ → ℕ: functional programming currying syntax, interpreted as
  ℕ → (ℕ → ℕ), allowing for partial application, e.g.
  f(x) := P(3, x)
-/
def f: ℕ → ℕ := P 3
-- Note that currying always fixes arguments from left to right, i.e. `P a` is always interpreted as `P(a, x)`
-- To partially apply to the second argument, i.e. `P(x, a)`,
/-
  def P_swapped := Function.swap P
-/
-- Then `P 3 4 == P_swapped 4 3`

/-
def P : ℕ → ℕ → ℕ is equivalent to: def P (x y : ℕ),
  but the latter does not allow partial application
-/


-- In Lean, every recursively defined function is equipped with functional induction
#check P.induct
#check P.induct_unfolding

#eval [P 0 0]
#eval [P 0 1,P 1 0]
#eval [P 2 0,P 1 1, P 2 0]
#eval [P 3 0,P 2 1, P 1 2, P 0 3]
#eval [P 4 0,P 3 1, P 2 2, P 1 3, P 0 4]

-- Example
lemma P_le_fact ( a b : ℕ ): P a b ≤ (a+b)! := by
  fun_induction P
  all_goals (expose_names)
  · simp only [add_zero]
    exact fact x
  · simp only [Nat.succ_eq_add_one, zero_add]
    exact fact (n + 1)
  · grw [ih1,ih2]
    clear * -; grind [fact,factorial] -- grind for algebraic proofs

-- grind is a powerful automation
-- We will not be using grind for the rest of the week.
lemma P_le_fact'' ( a b : ℕ ): P a b ≤ (a+b)! := by
  -- fun_induction P <;> all_goals grind only [fact, factorial]
  fun_induction P
  · grind[fact]
  · grind[fact]
  · grind[factorial]

-- This proof is more intuitive than the one-line proof
lemma P_le_fact' ( a b : ℕ ): P a b ≤ (a+b)! := by
  fun_induction P <;> all_goals (try simp_all only [add_zero, fact])
  · expose_names
    calc
      P (a + 1) b + P a (b + 1) ≤ (a + 1 + b) ! + (a + (b + 1)) !                            := by rel [ih1, ih2]
                              _ ≤ (a + b) * (a + b + 1) ! + (a + 1 + b) ! + (a + (b + 1)) !  := by omega
                              _ = ((a + b + 1) + 1) * (a + b + 1)!                           := by ring_nf
                              _ = ((a + b + 1) + 1)!                                         := by bound
                              _ = (a + 1 + (b + 1))!                                         := by ring_nf

--#print P_le_fact'
--#print P_le_fact'._proof_1_5

-- # Exercise 1.1
/-
Define T(m,n):
  T(m,0) = T(0,n) = 1,
  T(m,n) = T(m-1,n) + T(m,n-1)
  Prove that T(m,n) ≤ 2^{m+n}
-/

def T : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ => 1
  | m+1, n+1 => T m (n+1) + T (m+1) n

theorem solve_T (m n: ℕ):  T m n ≤ 2^(m+n)  := by
  fun_induction T
  all_goals (expose_names)
  · exact Nat.one_le_two_pow
  · exact Nat.one_le_two_pow
  · grw [ih1, ih2]
    simp_all
    grind

-- # Exercise 1.2
/-
Define C(m,n):
  C(m,0) = C(0,n) = 1,
  C(m,n) = C(m-1,n)*C(m,n-1)
  Prove that C(m,n) = 2^{m*n}
-/

def C : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ => 1
  | m+1, n+1 => C m (n+1) * C (m+1) n

-- theorem solve_C (m n: ℕ):  C m n = 2^(m*n)  := by
--   fun_induction C
--   all_goals (expose_names)
--   · exact rfl
--   · simp_all
--   · rw [ih2, ih1]
--     simp_all
