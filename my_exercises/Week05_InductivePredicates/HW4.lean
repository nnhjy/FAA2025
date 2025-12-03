import Mathlib.Tactic
set_option autoImplicit false
set_option tactic.hygienic false

-- All tactics are welcome.

-- # Problem 1: Predicate AllEven
-- Define Predicate `AllEven` is true if every number in the list is even.
-- e.g., [], [2], [8, 0, 4]
-- Complete the definition for AllEven. It should take a list of natural numbers (List ℕ) and return a Prop

def isEven (n :ℕ) : Prop := ∃k, n = 2*k

-- Your AllEven must use isEven function above
inductive AllEven : List ℕ → Prop
  | nil : AllEven []
  | single (a : ℕ) : isEven a → AllEven [a]
  | cons (a : ℕ) (l : List ℕ) : isEven a → (AllEven l → AllEven (a::l))

-- Prove that your AllEven predicate is equivalent to checking if every element in the list is even.
-- Let's split into two parts

-- # Part 1
theorem Problem1_1 (l : List ℕ) : AllEven l → ∀ n ∈ l, isEven n := by
  intro h_AE_l n h_n_l
  induction' l
  · contradiction
  · simp_all
    cases h_n_l
    -- # Question: how to proceed step-by-step by analysing the `AllEven(head::tail)` of `h_AE_l`?
    · grind [AllEven]
    · grind [AllEven]

-- # Part 2
theorem Problem1_2 (l : List ℕ) : (h : ∀ n ∈ l, isEven n) → AllEven l := by
  intro h_even_n
  induction' l
  · exact AllEven.nil
  · grind [AllEven]

-- # Sorted
-- We will use the following version of Sorted

def Nat.MinOfList (a :ℕ ) (t: List ℕ) : Prop := ∀ y ∈ t, a ≤ y

inductive Sorted: List ℕ  → Prop
  | nil : Sorted []
  | single (a : ℕ) : Sorted [a]
  | cons (a b : ℕ ) (t : List ℕ) : a ≤ b → Sorted (b :: t) → Sorted (a :: b :: t)
  | cons_min (a :ℕ) (t : List ℕ) : a.MinOfList t  → Sorted (t) →  Sorted (a :: t)

-- # Problem 2: Prove that a list of length at most 1 is sorted.
def len : List ℕ → ℕ
| []      => 0
| _ :: xs => 1 + len xs

theorem Problem2 (l : List ℕ) (h: len l ≤ 1): Sorted l := by
  -- cases l with
  -- | nil => exact Sorted.nil
  -- | cons a l_tail =>
  --   cases l_tail with
  --   | nil => exact Sorted.single a
  --   | cons b l_rest =>
  --     simp [len] at h
  cases l
  · exact Sorted.nil
  · cases tail
    · exact Sorted.single head
    -- · simp [len] at h
    · simp only [len] at h; simp at h

-- # Problem 3: Prove basic properties of Sorted
theorem Problem3_1 {x : ℕ} {xs : List ℕ} (hxs : Sorted (x :: xs)) : Sorted xs := by
  generalize h_eq : x::xs = l
  replace hxs : Sorted l := by rwa [← h_eq]
  -- have hxs_eq : Sorted l := by rwa [← h_eq]
  induction' hxs generalizing xs x
  all_goals
  grind [Sorted]

theorem Problem3_2 {x y : ℕ} {t : List ℕ} (hsort : Sorted (x :: y :: t)) : y.MinOfList t := by
  generalize h_eq : x::y::t = l
  replace hxyt : Sorted l := by rwa [← h_eq]
  -- have hxs_eq : Sorted l := by rwa [← h_eq]
  induction' hxyt generalizing x y t
  all_goals
  grind [Sorted, Nat.MinOfList]

-- # Problem 4: Alternate Definitions of Sorted
-- Consider the following inductive predicate
inductive Sorted2: List ℕ  → Prop
  | nil : Sorted2 []
  | single (a : ℕ) : Sorted2 [a]
  | cons (a b : ℕ ) (t : List ℕ ) : a ≤ b → Sorted2 (b :: t) → Sorted2 (a :: b :: t)

-- Prove that Sorted2 is equivalent to Sorted
-- You may find `ext` tactic useful
theorem Problem4 : Sorted2 = Sorted := by
  ext
  constructor
  · intro h_s2
    induction' x
    · exact Sorted.nil
    · generalize h_eq : head::tail = l
      replace h_s2 : Sorted2 l := by rwa [h_eq] at h_s2
      induction h_s2 generalizing head tail
      all_goals grind [Sorted2, Sorted]
  -- symmetrical
  · intro h_s2
    induction' x
    · exact Sorted2.nil
    · generalize h_eq : head::tail = l
      replace h_s2 : Sorted l := by rwa [h_eq] at h_s2
      induction h_s2 generalizing head tail
      all_goals grind [Sorted2, Nat.MinOfList]
      -- · grind
      -- · grind [Sorted2]
      -- · grind [Sorted2]
      -- · grind [Nat.MinOfList, Sorted2]

-- # Problem 5: Binary Tree
-- Consider the following version of BinaryTree
inductive BinaryTree
  | nil
  | node (left : BinaryTree) (key : ℕ) (right : BinaryTree)

-- Define mirror operation as reversing the tree
def mirror : BinaryTree → BinaryTree
  | BinaryTree.nil        => BinaryTree.nil
  | BinaryTree.node l key r => BinaryTree.node (mirror r) key (mirror l)

-- A binary tree is complete if every node has either two non-empty subtrees or two empty subtrees.
-- We can define it using inductive predicate as follows.

inductive Complete : BinaryTree  → Prop
  | leaf : Complete BinaryTree.nil
  | node  (l : BinaryTree) (key : ℕ) (r : BinaryTree)
      (hl : Complete l) (hr : Complete r)
      (hiff : l = BinaryTree.nil ↔ r = BinaryTree.nil) :
    Complete (BinaryTree.node l key r)

theorem mirror_nil_iff (r : BinaryTree): mirror r = BinaryTree.nil ↔ r = BinaryTree.nil := by
  induction' r
  · rw [mirror]
  · rw [mirror]
    simp only [reduceCtorEq]

-- Prove that if a mirror of t is complete then t is complete
theorem Problem5: ∀t : BinaryTree, Complete (mirror t) → Complete t := by
  intro t
  induction' t
  · simp [mirror]
  · intro h_p
    rw [mirror] at h_p
    cases h_p
    apply Complete.node
    · simp [hr] at left_ih; exact left_ih
    · simp [hl] at right_ih; exact right_ih
    -- # Is there a way to transform both sides of the goal into `hiff`?
    -- # the left-hand-side is easy by rw, which doen't work on the right-hand-side
    · rw [mirror_nil_iff, mirror_nil_iff] at hiff
      symm
      exact hiff
