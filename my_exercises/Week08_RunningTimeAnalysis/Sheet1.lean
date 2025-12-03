import Mathlib.Tactic -- imports all of the tactics in Lean's maths library
import Lectures.Week08.API

set_option autoImplicit false
set_option tactic.hygienic false

-- # Q: How to analyze time complexity?
-- We will instrument the code to track the time. However, we do not want to interfere the correctness analysis.
-- We learn an elegant way to do this using Monad
-- # Separation of concerns: the correctness proof and running time proof should not interfere to each other

def len : List ℕ →  ℕ
| [] => 0
| _ :: xs => 1 + len xs

-- lenT with do notations
def lenT : List ℕ → TimeM ℕ
| [] => return 0  -- or `pure 0`
| _ :: xs => do -- with `✓` defined in the API
    -- # ?? correctness (in the time counting) and necessity of have this step??
    ✓ 0  -- or simply `✓ ()` or `✓ (), 0`

    let len_xs ← lenT xs
    ✓ (1 + len_xs)

-- Example usage
#eval lenT []
#eval lenT [3,2,5]
#eval lenT [1,2,3,4,5]

theorem lenT_correctness (xs : List ℕ): (lenT xs).ret = len xs := by
  induction xs
  · rfl
  · -- `unfold lenT; simp?`
    simp only [lenT, bind, TimeM.tick, PUnit.zero_eq, TimeM.ret_bind]
    rw [tail_ih]
    rfl

theorem lenT_time (xs : List ℕ ): (lenT xs).time = 2 *(len xs) := by
  induction xs
  · rfl
  · -- `unfold lenT; simp?`
    simp only [lenT, bind, TimeM.tick, PUnit.zero_eq, TimeM.time_of_bind]
    rw [tail_ih]
    rw [show len (head :: tail) = 1 + len tail from rfl]
    omega

-- ============================================================================
-- EXERCISE 1: Sum of a list
-- ============================================================================
-- Implement sumT that computes the sum of a list with time tracking
-- Each recursive call should cost 1 time unit
-- Expected time complexity: n where n is the length of the list

def sumT : List ℕ → TimeM ℕ
| [] => pure 0
| x :: xs => do
  -- # invalid here as contradicting the "sumT_time" below (?)
  -- ✓ ()  -- Count the recursive call itself
  let sum_xs ← sumT xs
  ✓ (x + sum_xs)  -- Each recursive call costs 1 time unit

def sum : List ℕ → ℕ
| [] => 0
| x :: xs => x + sum xs

-- Example usage
#eval sumT []
#eval sumT [3,2,5]
#eval sumT [1,2,3,4,5]

-- Prove correctness
theorem sumT_correctness (xs : List ℕ): (sumT xs).ret = sum xs := by
  induction xs
  · rfl
  · unfold sumT
    simp only [bind, TimeM.tick, TimeM.ret_bind]
    rw [tail_ih]
    simp [sum]

-- Prove time complexity: only holds when `✓ ()` is excluded in `sumT`
theorem sumT_time (xs : List ℕ): (sumT xs).time = xs.length := by
  induction xs
  · rfl
  · unfold sumT
    simp only [bind, TimeM.tick, TimeM.time_of_bind, List.length_cons]
    rw [tail_ih]
    -- simp only [bind, TimeM.tick, TimeM.time_of_bind, List.length_cons, Nat.add_right_cancel_iff]
    -- exact tail_ih

/- # Basics for EXERCISE 2 & 3
  Operation name    Operation   What it does    Time complexity
- cons(truction)    x :: xs     Add to front    O(1) - just create 1 new cell
- append            xs ++ [x]   Add to back     O(length(xs)) - must copy all of xs
-/

-- ============================================================================
-- EXERCISE 2: Reverse a list
-- ============================================================================
-- Implement reverseT that reverses a list with time tracking
-- Each cons operation should cost 1 time unit
-- Expected time complexity: n² where n is the length of the list

def reverseT : List ℕ → TimeM (List ℕ)
| [] => pure []
| x :: xs => do
  -- ✓ ()
  -- Count the cons operation of deconstructing/processing the cons `x :: xs`
  -- # But only O(n) time complexity, not dominant for the O(n^2) complexity

  let xs_r ← reverseT xs
  -- ✓ (xs_r ++ [x])
  ✓ (xs_r ++ [x]), xs_r.length
  -- the list *append* operation `xs_r ++ [x]` constructs `xs_r.length` new cons cells
  -- # (xs_r.length) seems to be the main reason of time complexity

def reverse : List ℕ → List ℕ
| [] => []
| x :: xs => reverse xs ++ [x]

#eval reverseT [1,2,3,4,5,6,7,8,9,10]

-- Prove correctness
theorem reverseT_correctness (xs : List ℕ): (reverseT xs).ret = reverse xs := by
  induction xs
  · rfl
  · unfold reverseT
    simp only [bind, TimeM.tick, TimeM.ret_bind, reverse]
    rw [tail_ih]

-- Hint: You'll need a helper lemma about the time of append
-- Prove time complexity is O(n²)
-- Helper lemma: The length of the reversed list equals the original length
lemma reverseT_ret_length (xs : List ℕ) :
  (reverseT xs).ret.length = xs.length := by
  induction xs
  · rfl
  · unfold reverseT
    simp only [bind, TimeM.tick, TimeM.ret_bind, List.length_append, List.length_cons]
    rw [tail_ih]
    simp

theorem reverseT_time_quadratic (xs : List ℕ):
  ∃ c, (reverseT xs).time ≤ c * xs.length * xs.length := by
  induction xs
  · use 1; rfl
  · obtain ⟨ c_ext, ih ⟩ := tail_ih
    use c_ext+2
    unfold reverseT
    simp only [bind, TimeM.tick, TimeM.time_of_bind, List.length_cons]
    grw [ih]
    -- `(reverseT tail).ret.length` needs relating to `tail.length`
    rw [reverseT_ret_length]  -- Apply the helper lemma!
    ring_nf
    omega

-- ============================================================================
-- EXERCISE 3: Tail-recursive reverse with accumulator
-- ============================================================================
-- Implement a tail-recursive reverse using an accumulator
-- Each step should cost 1 time unit
-- Expected time complexity: n (linear, much better than reverseT!)

def reverseTailT : List ℕ → List ℕ → TimeM (List ℕ)
| [], acc => pure acc
| x :: xs, acc => do
  -- ✓ ()
  -- reverseTailT xs (x::acc)
  let xs_r ← reverseTailT xs (x::acc)
  ✓ xs_r

def reverseTail : List ℕ → List ℕ → List ℕ
| [], acc => acc
| x :: xs, acc => reverseTail xs (x :: acc)

#eval reverseTailT [1,2,3,4,5,6,7,8,9,10] []

-- Prove correctness
theorem reverseTailT_correctness (xs acc : List ℕ):
  (reverseTailT xs acc).ret = reverseTail xs acc := by
  /-
    When using only `induction xs`, the `acc` parameter is fixed,
    but in the recursive call, `acc` changes to `head :: acc`
  -/
  induction xs generalizing acc

  · rfl
  · /-
    With `generalizing acc`,
    Induction hypothesis applies to any accumulator `acc`, i.e.
    `∀ acc, (reverseTailT tail acc).ret = reverseTail tail acc`
    -/
    unfold reverseTailT reverseTail
    simp_all [bind, TimeM.tick, TimeM.ret_bind]

-- Prove linear time complexity
theorem reverseTailT_time (xs acc : List ℕ):
  (reverseTailT xs acc).time = xs.length := by
  induction xs generalizing acc
  · rfl
  · unfold reverseTailT
    simp_all [bind, TimeM.tick, TimeM.time_of_bind, List.length_cons]
