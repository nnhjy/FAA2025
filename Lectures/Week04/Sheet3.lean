
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

-- # Example: compute the length of a list
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
    simp only [Nat.add_left_cancel_iff]
    apply len_append'

-- `cases` tactics can break the goal based on constructors of an inductive type
theorem len_append_cases (x : ℕ) (l : List ℕ) : len (l ++ [x]) = 1 + len l  := by
  cases l
  · simp [len]
  · simp only [List.cons_append,len]
    simp only [Nat.add_left_cancel_iff]
    apply len_append_cases

-- proof by induction
theorem len_append_induction (x : ℕ) (l : List ℕ) : len (l ++ [x]) = 1 + len l  := by
  induction' l with y ys
  · aesop
  · simp only [List.cons_append, len]
    rw [tail_ih]

#check len.induct
-- proof by functional induction
theorem len_append_fun_induction (x : ℕ) (l : List ℕ) : len (l ++ [x]) = 1 + len l  := by
  fun_induction len l
  · simp [len]
  · simp only [List.cons_append]
    rw [len]
    simp only [Nat.add_left_cancel_iff]
    rw [ih1]

-- proof by functional induction oneline
theorem len_append_fun_induction_oneline (x : ℕ) (l : List ℕ) : len (l ++ [x]) = 1 + len l  := by
  fun_induction len l <;> all_goals grind [len]

-- # Exercise 3.1: write filter where it takes out items that are not in the list
def my_filter {α : Type} (p : α → Bool) : List α → List α
| [] => []
| a :: as => sorry

example: my_filter (fun x => x % 2 == 0) [1, 2, 3, 4, 5, 6] = [2,4,6] := sorry
example: my_filter (fun s => s.startsWith "a") ["apple", "banana", "almond", "kiwi"] =  ["apple", "almond"] := sorry

-- Prove this:
theorem filter_append {α : Type} (p : α → Bool) (l1 l2 : List α) :
  my_filter p (l1 ++ l2) = (my_filter p l1) ++ (my_filter p l2) := by sorry

-- # Exercise 3.2: Define IsPalindrome
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
