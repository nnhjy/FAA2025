import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
set_option tactic.hygienic false

-- # Exercise: Define IsPalindrome
-- This should be true if and only if it can be read in forward and reverse direction
-- e.g., 'a', 'aba', 'aabbcbbaa'

inductive IsPalindrome {α : Type} : List α → Prop
 | nil : IsPalindrome []
 | single (a : α) : IsPalindrome [a]
 | cons_eq (a : α) (l : List α) : (IsPalindrome l) → IsPalindrome (a::l ++ [a])

theorem IsPalindrome_imp_eq_reverse {α : Type} (l : List α) :
  IsPalindrome l → l = List.reverse l := by
  intro h
  induction' h
  · simp only [List.reverse_nil]
  · simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
  · simpa
  -- # Alternative 1:
  -- · simp only [
  --     List.cons_append, List.reverse_cons, List.reverse_append, List.reverse_nil,
  --     List.nil_append, List.cons.injEq, List.append_cancel_right_eq, true_and
  --   ]; assumption
  -- # Alternative 2:
  -- · calc
  --     a :: l_1 ++ [a]
  --       = a :: l_1.reverse ++ [a] := by rw [← a_ih]
  --     _ = [a] ++ l_1.reverse ++ [a] := by
  --       simp only [List.cons_append, List.nil_append]
  --     _ = [a].reverse ++ l_1.reverse ++ [a].reverse := by
  --       simp only [List.cons_append, List.nil_append, List.reverse_cons, List.reverse_nil]
  --     _ = (a :: l_1 ++ [a]).reverse := by
  --       simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.reverse_append]

-- Challenging one :)
theorem IsPalindrome_pmi_eq_reverse {α : Type} (l : List α) :
  l = List.reverse l → IsPalindrome l  := by
  intro h_p
  induction' l with a as ih
  · exact IsPalindrome.nil
  · cases as with
    | nil =>
      -- l = [a]
      exact IsPalindrome.single a
    | cons b bs =>
      -- l = a :: b :: bs
      sorry

theorem IsPalindrome_reverse {α : Type} (l : List α) (h: IsPalindrome l) : IsPalindrome l.reverse  := by
  induction' h
  · simp only [List.reverse_nil]
    exact IsPalindrome.nil
  · simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
    exact (IsPalindrome.single a)
  · rw [← IsPalindrome_imp_eq_reverse]
  -- · rw [← IsPalindrome_imp_eq_reverse (a :: l_1 ++ [a])]
    all_goals
    apply IsPalindrome.cons_eq
    exact a_1

-- # Exercise: Binary Tree, Mirror and Complete Binary Tree
-- Define BinaryTree as follows

inductive BinaryTree
  | nil
  | node (left : BinaryTree) (key : ℕ) (right : BinaryTree)

#check BinaryTree
#check BinaryTree.nil
#check BinaryTree.node

-- Define mirror operation as reversing the tree
def mirror : BinaryTree → BinaryTree
  | BinaryTree.nil        => BinaryTree.nil
  | BinaryTree.node l key r => BinaryTree.node (mirror r) key (mirror l)

--  Prove that mirror of mirror of a tree is the tree itself.
theorem mirror_mirror (t : BinaryTree) : mirror (mirror t) = t := by
  -- cases t
  -- · rw [mirror, mirror]
  -- · rw [mirror, mirror]
  --   simp only [BinaryTree.node.injEq, true_and]
  --   constructor
  --   all_goals
  --   rw [mirror_mirror]
  fun_induction mirror t
  · rw [mirror]
  · grind [mirror]

--  Prove that mirror of mirror of a tree is the tree itself.
theorem mirror_nil_iff (r : BinaryTree): mirror r = BinaryTree.nil ↔ r = BinaryTree.nil := by
  induction' r
  · rw [mirror]
  · rw [mirror]
    simp only [reduceCtorEq]

-- A binary tree is complete if every node has either two non-empty subtrees or two empty subtrees.
-- We can define it using inductive predicate as follows.

inductive Complete : BinaryTree  → Prop
  | leaf : Complete BinaryTree.nil
  | node  (l : BinaryTree) (key : ℕ) (r : BinaryTree)
      (hl : Complete l) (hr : Complete r)
      (hiff : l = BinaryTree.nil ↔ r = BinaryTree.nil) :
    Complete (BinaryTree.node l key r)

-- Prove that if t is complete then its mirroring is also complete.
theorem complete_mirror  (t : BinaryTree) (ht : Complete t) :
  Complete (mirror t) := by
  induction' ht
  · rw [mirror]
    exact Complete.leaf
  · rw [mirror]
    apply Complete.node
    · exact hr_ih
    · exact hl_ih
    · rw [mirror_nil_iff, mirror_nil_iff]
      symm
      exact hiff
