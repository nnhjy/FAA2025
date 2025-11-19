import Mathlib.Tactic -- imports all of the tactics in Lean's maths library


set_option autoImplicit false
set_option tactic.hygienic false


-- We will use the following Monad
structure TimeM (α : Type) where
  ret : α
  time : ℕ

namespace TimeM

def pure {α} (a : α) : TimeM α :=
  ⟨a, 0⟩

def bind {α β} (m : TimeM α) (f : α → TimeM β) : TimeM β :=
  let r := f m.ret
  ⟨r.ret, m.time + r.time⟩

instance : Monad TimeM where
  pure := pure
  bind := bind

-- Increment time

@[simp] def tick {α : Type} (a : α) (c : ℕ := 1) : TimeM α :=
  ⟨a, c⟩

notation "✓" a:arg ", " c:arg => tick a c
notation "✓" a:arg => tick a  -- Default case with only one argument

def tickUnit : TimeM Unit :=
  ✓ () -- This uses the default time increment of 1


-- We define `@[simp]` lemmas for the `.time` field, similar to how we did for `.ret`.
@[grind, simp] theorem time_of_pure {α} (a : α) : (pure a).time = 0 := rfl
@[grind, simp] theorem time_of_bind {α β} (m : TimeM α) (f : α → TimeM β) :
 (TimeM.bind m f).time = m.time + (f m.ret).time := rfl
@[grind, simp] theorem time_of_tick {α} (a : α) (c : ℕ) : (tick a c).time = c := rfl
@[grind, simp] theorem ret_bind {α β} (m : TimeM α) (f : α → TimeM β) :
  (TimeM.bind m f).ret = (f m.ret).ret := rfl

-- allow us to simplify the chain of compositions
attribute [simp] Bind.bind Pure.pure TimeM.pure

end TimeM

#check bind
#check TimeM.bind
#check pure
#check TimeM.pure

-- ============================================================================
-- Problem 1: Maximum element (20 points)
-- ============================================================================
-- Implement maxT that finds the maximum element in a non-empty list
-- Each comparison should cost 1 time unit
-- Expected time complexity: n-1 comparisons for a list of length n

@[grind] def maxT : List ℕ → TimeM ℕ
| []  => return 0
| [x] => pure x
| x :: xs => do
  let max_xs_value ← maxT xs
  ✓ (max x max_xs_value)

@[grind] def mymax : List ℕ → ℕ
| [] => 0
| [x] => x
| x :: xs => max x (mymax xs)

#eval mymax [1,3,5,2]
#eval maxT [1,3,5,2]

theorem Problem1_maxT_correctness (xs : List ℕ):
  (maxT xs).ret = mymax xs := by
  unfold maxT mymax
  induction' xs
  · simp
  · simp only [pure]
    simp only [TimeM.pure]
    simp only [bind, TimeM.tick]
    grind

theorem Problem1_maxT_time (xs : List ℕ) (h : xs.length ≥ 1):
  (maxT xs).time = xs.length - 1 := by
  unfold maxT
  induction' xs
  · simp
  · simp only [pure]
    simp only [bind, TimeM.tick]
    grind

-- ============================================================================
-- Problem 2: Analysis of binary search (30 points)
-- ============================================================================

-- Week06: Sheet3
structure SortedArrayFun (n :ℕ) where
  get : ℕ → ℕ
  size : ℕ := n
  sorted: Monotone get

-- consider the following binary search algorithm on time monad
-- cf. Week06: Sheet3
def contains_bs_monad {n :ℕ }(arr : SortedArrayFun n) (q : ℕ) : TimeM (Option ℕ) :=
  bs_aux 0 (n-1)
  where bs_aux (a b :ℕ) (h: a ≤ b := by omega): TimeM (Option ℕ) := do
  if h: a = b then
    if q = arr.get a then return some a
    else return none
  else
    let mid := (a+b)/(2 :ℕ)
    if q < arr.get mid then
      let result ← bs_aux a mid
      ✓ result
    else if  arr.get mid < q then
      let result ← bs_aux (mid+1) b
      ✓ result
    else return (some mid)

-- You can use these two theorems without proof
-- subinterval_to_interval_qlt
-- subinterval_to_interval_qgt

-- cf. Week06: Sheet3
theorem subinterval_to_interval_qlt {n : ℕ} (arr : SortedArrayFun n) (q a mid b: ℕ)
  (h_bounds : a ≤ mid ∧ mid ≤ b)
  (h_q: q < arr.get mid):
  (∃ i, a ≤ i ∧ i ≤ b ∧ arr.get i = q) ↔ (∃ i, a ≤ i ∧ i ≤ mid ∧ arr.get i = q)  :=  sorry

-- cf. Week06: Sheet3 `bs_aux_correctness`
theorem subinterval_to_interval_qgt {n : ℕ} (arr : SortedArrayFun n) (q a mid b: ℕ)
  (h_bounds : a ≤ mid ∧ mid ≤ b)
  (h_q: arr.get mid < q ):
  (∃ i, a ≤ i ∧ i ≤ b ∧ arr.get i = q) ↔ (∃ i, (mid+1) ≤ i ∧ i ≤ b ∧ arr.get i = q)  := sorry

-- # (10 Points) Problem 2.1: Prove the correctness of this algorithm.
-- Hint: Your solution should be minimally changed from the non-monad version
-- cf. Week06: Sheet3 `contains_bs_correctness`
lemma bs_aux_monad_correctness (n q :ℕ)(arr : SortedArrayFun n) (a b :ℕ) (h_le : a ≤ b)
  : (∃ i, a ≤ i ∧ i ≤ b ∧ arr.get i = q) ↔ ((contains_bs_monad.bs_aux arr q a b h_le).ret ≠ none) := by
  fun_induction contains_bs_monad.bs_aux
  · simp_all
    use b_1
  · simp_all
    intro x hx hy
    have: x = b_1 := by omega
    subst this
    aesop
  · simp only [bind, TimeM.tick, TimeM.ret_bind, ne_eq]
    simp_all
    rw [← ih1]
    rw [subinterval_to_interval_qlt arr q a_1 mid b_1 (by grind) h_2]
  · simp only [bind, TimeM.tick, TimeM.ret_bind, ne_eq]
    simp_all
    rw [← ih1]
    rw [subinterval_to_interval_qgt arr q a_1 mid b_1 (by grind) h_3]
  · simp_all
    use mid
    grind

theorem Problem2_part1 (n q :ℕ)(h: 0 < n)(arr : SortedArrayFun n):
  (∃ i, i < n ∧ arr.get i = q) ↔ ((contains_bs_monad arr q).ret ≠ none) := by
  unfold contains_bs_monad
  have: 0 ≤ n-1 := by omega
  have := bs_aux_monad_correctness n q arr 0 (n-1) (by omega)
  grind

-- Next, we will prove the running time
def g (n : ℕ) : ℕ :=
  if n = 0 then 0
  else g (n/2) + 1

-- You can use these two theorems without proof
theorem g_close_form (n : ℕ) : g n ≤  Nat.log 2 n +1  :=  sorry
theorem g_monotone : Monotone g := sorry

-- # (20 Points) Problem 2.2: Prove the running time of this algorithm.
-- Hint: Formulate an intermediate lemma that works for general range [a,b] and then specialize to [0, n-1] to prove this
lemma bs_aux_time_le_g (n q :ℕ)(arr : SortedArrayFun n) (a b :ℕ) (h_le : a ≤ b)
  : (contains_bs_monad.bs_aux arr q a b h_le).time ≤ g (b - a) := by
  fun_induction contains_bs_monad.bs_aux
  · -- case a = b
    simp [g]
  · -- case a = b (second branch)
    simp [g]
  · -- case q < arr.get mid, recurse left
    simp only [bind, TimeM.tick, TimeM.time_of_bind]
    grw [ih1]
    have mid_def : mid - a_1 = (b_1 - a_1) / 2 := by grind
    rw [mid_def]
    grind [g]
  · -- case arr.get mid < q, recurse right
    simp only [bind, TimeM.tick, TimeM.time_of_bind]
    grw [ih1]
    have mid_bound : b_1 - (mid + 1) ≤ (b_1 - a_1) / 2 := by grind
    have g_bound : g (b_1 - (mid + 1)) ≤ g ((b_1 - a_1) / 2) := by
      apply g_monotone
      exact mid_bound
    grind [g]
  · -- case arr.get mid = q
    simp only [pure, TimeM.pure, zero_le]

lemma Problem2_part2_helper ( n q :ℕ)(arr : SortedArrayFun n) (a b :ℕ) (h_le : a ≤ b)
  : (contains_bs_monad.bs_aux arr q a b h_le).time ≤ Nat.log 2 (b-a) + 1 := by
  grw [bs_aux_time_le_g]
  exact g_close_form (b - a)

theorem Problem2_part2 (n q :ℕ)(arr : SortedArrayFun n)
  : (contains_bs_monad arr q).time ≤ Nat.log 2 (n-1) +1 := by
  unfold contains_bs_monad
  have : 0 ≤ n-1 := by omega
  have := Problem2_part2_helper n q arr 0 (n-1) (by omega)
  grind
