import Lectures.Week08.API

set_option autoImplicit false
set_option tactic.hygienic false

-- Analysis of merge sort
def merge (xs ys : List ℕ) : TimeM (List ℕ) :=
  -- `rec`: Lean keyword required within a `let` binding (scope)
  --  to mark the customiesed function recursion, i.e. the `go` function can call itself inside its definition
  -- `go`: name for our sub function
  let rec go : List ℕ → List ℕ → TimeM (List ℕ)
  | [], ys => ✓ ys, ys.length
  | xs, [] => ✓ xs, xs.length
  | x::xs', y::ys' => do
    if x ≤ y then
      let rest ← go xs' (y::ys')
      ✓ (x :: rest)
    else
      let rest ← go (x::xs') ys'
      ✓ (y :: rest)
  go xs ys

-- cf. Week06.Sheet1
def mergeSort (xs : List ℕ) : TimeM (List ℕ) := do
  if xs.length < 2 then return xs
  else
    let n := xs.length
    let half := n / 2
    let left :=  xs.take half
    let right := xs.drop half
    let sortedLeft ← mergeSort left
    let sortedRight ← mergeSort right
    merge sortedLeft sortedRight

-- # interpretation in each line
-- If the return type is a Monad, say (`List ℕ`), then
-- `let sortedLeft ← mergeSort left`
-- This line means you can treat `sortedLeft` as type `List ℕ` and `let` notation tell Lean to put `sortedLeft` into a box
-- If the return type is not a Monad, you can use normal `let` with `:=` notation.


#check mergeSort
#eval merge [1,2,3,10] [4,5]
#eval mergeSort [4,2,3,1]

-- Correctness of Merge sort

@[simp,grind] def Nat.MinOfList (a :ℕ ) (t: List ℕ) : Prop := ∀ y ∈ t, a ≤ y

-- inductive predicate
inductive Sorted: List ℕ  → Prop
  | nil : Sorted []
  | single (a : ℕ) : Sorted [a]
  | cons (a b : ℕ) (t : List ℕ ) : a ≤ b → Sorted (b :: t) → Sorted (a :: b :: t)
  | cons_min (a :ℕ) (t : List ℕ) : a.MinOfList t → Sorted (t) →  Sorted (a :: t)

-- Week06 HW5
theorem sorted_min {x : ℕ} {xs : List ℕ} (hxs : Sorted (x :: xs)) : x.MinOfList xs  := by
  cases hxs
  · simp
  · simp only [Nat.MinOfList, List.mem_cons, forall_eq_or_imp]
    constructor
    · exact a_1
    · apply sorted_min at a_2
      grind
  · exact a_1

theorem sorted_is_preserved_by_min_cons {a : ℕ} {t : List ℕ} (hmin : a.MinOfList t) (ht : Sorted t) : Sorted (a :: t) := by
  exact Sorted.cons_min a t hmin ht

-- Exercise: Port your the proof of merge sort from `Week06` into this proof.
-- Week06 HW5
theorem sorted_suffix {x : ℕ} {xs : List ℕ} (hxs : Sorted (x :: xs)) : Sorted xs := by grind [Sorted]

-- Week06 Sheet2
theorem mem_either_merge (xs ys : List ℕ) (z : ℕ)
  (hz : z ∈ (merge xs ys).ret) : z ∈ xs ∨ z ∈ ys := by
  rw [merge] at hz

  -- adapted from the proof of `mem_either_merge_auto`
  fun_induction merge.go
  · simp_all
  · simp_all
  · simp_all
    grind
  · simp_all
    grind

  -- #TODO: other approaches
  -- cases xs
  -- · simp only [List.not_mem_nil, false_or]
  --   rw [merge, merge.go] at hz
  --   simp_all

-- Week06.Sheet2.Exercise 2.2
theorem min_all_merge (x : ℕ) (xs ys : List ℕ)
  (hxs : x.MinOfList xs) (hys : x.MinOfList ys) : x.MinOfList (merge xs ys).ret := by
  simp
  intro y hy
  have : y ∈ xs ∨ y ∈ ys := by
    apply mem_either_merge; exact hy
  cases this
  · exact hxs y h
  · exact hys y h

  -- rw [merge]
  -- fun_induction merge.go
  -- · simp only [Nat.MinOfList, TimeM.tick]
  --   grind
  -- · simp only [Nat.MinOfList, TimeM.tick]
  --   grind
  -- · simp only [Nat.MinOfList, bind, TimeM.tick, TimeM.ret_bind, List.mem_cons, forall_eq_or_imp]
  --   simp_all
  -- · simp only [Nat.MinOfList, bind, TimeM.tick, TimeM.ret_bind, List.mem_cons, forall_eq_or_imp]
  --   simp_all

-- Week06.Sheet2
theorem sorted_merge {l1 l2 : List ℕ} (hxs : Sorted l1)
  (hys : Sorted l2) : Sorted ((merge l1 l2).ret) := by
  rw [merge]
  fun_induction merge.go l1 l2
  · simp only [TimeM.tick]
    exact hys
  · simp only [TimeM.tick];
    exact hxs
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

-- Let's do this one as an example.
theorem MSMCorrect (xs : List ℕ) : Sorted (mergeSort xs).ret := by
  fun_induction mergeSort
  · simp only [pure, TimeM.pure]
    cases x
    · grind [Sorted]
    · apply Sorted.cons_min
      · grind
      · have : tail = [] := by
          simp at h
          grind [List]
        rw [this]
        grind [Sorted]
  · simp only [bind, TimeM.ret_bind]
    apply sorted_merge ih2 ih1
