
import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
set_option tactic.hygienic false

-- Lean defines the notation [] for nil and :: for cons,
example : [1,2,3] = 1 :: 2 :: 3 :: [] := by grind

def append {α : Type} : List α → List α → List α
| [], bs => bs
| a :: as, bs => a :: (append as bs)


#check append
#eval append [1, 2, 3] [4, 5, 6]
-- In Mathlib, append has notation ++

#eval [1,2,10,3] ++ [4,5,6]

-- Exercise: write reverse list
def reverse {α : Type} : List α → List α
| [] => []
| a :: xs => reverse xs ++ [a]

#eval reverse [1,2,3]

-- Exercise: compute the length of a list
def len {α : Type} : List α → ℕ
| []     =>  0
| _ :: xs => 1 + len xs

#check len.induct

#check len
-- proof by recursion
theorem len_append' (x : ℕ) (l : List ℕ) : len (l ++ [x]) = 1 + len l  := by
  match l with
  | []  => rfl
  | y :: ys =>
    simp only [List.cons_append,len]
    simp +arith +decide
    rw [add_comm]
    apply len_append'

-- proof by induction
theorem len_append (x : ℕ) (l : List ℕ) : len (l ++ [x]) = 1 + len l  := by
  induction' l with y ys
  · aesop
  · simp only [List.cons_append, len]
    rw [tail_ih]

#check len.induct
-- functional induction
theorem len_append2 (x : ℕ) (l : List ℕ) : len (l ++ [x]) = 1 + len l  := by
  fun_induction len l  <;> all_goals grind [len]


-- # Exercise 3.1: Define IsPalindrome
-- This should be true if and only if it can be read in forward and reverse direction
-- e.g., 'a', 'aba', 'aabbcbbaa'

inductive IsPalindrome {α : Type} : List α → Prop
--  | nil :  ??
--  | single (a : α) :  ??
--  | cons_eq (a : α) (l : List α) :  ??

theorem IsPalindrome_imp_eq_reverse {α : Type} (l : List α) :
  IsPalindrome l → l = List.reverse l := by sorry

theorem IsPalindrome_pmi_eq_reverse {α : Type} (l : List α) :
  l = List.reverse l → IsPalindrome l  := by sorry
