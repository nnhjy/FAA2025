
import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
set_option tactic.hygienic false

-- Lean defines the notation [] for nil and :: for cons,
example : [1,2,3] = 1 :: 2 :: 3 :: [] := by grind
example : [1,2,3] = 1 :: (2 :: (3 :: [])) := by grind
-- # pattern of a list

def append {α : Type} : List α → List α → List α
-- `append list_a list_b`
| [], bs => bs
| a :: as, bs => a :: (append as bs)
-- pattern matching `a :: as` for `list_a` = `[a, as...]`

#check append
#eval append [1, 2, 3] [4, 5, 6]
-- In Mathlib, `append` has notation `++`

#eval [1,2,10,3] ++ [4,5,6]

-- # Example: compute the length of a list
def len {α : Type} : List α → ℕ
-- `len list_x`
| []     =>  0
| _ :: xs => 1 + len xs
-- pattern matching `_ :: xs` for `list_x` = `[_, xs...]`
-- where particularly, `_` is simply an unused placeholder variable

#eval len [10, 20, 30]
-- Lean will evaluate:
-- len (10 :: 20 :: 30 :: [])
-- → 1 + len (20 :: 30 :: [])
-- → 1 + 1 + len (30 :: [])
-- → 1 + 1 + 1 + len []
-- → 1 + 1 + 1 + 0 = 3

def len' {α : Type} (l: List α): ℕ := match l with
| []     =>  0
| _ :: xs => 1 + len xs

#check len.induct
#check len
#check len'

-- proof by recursion
theorem len_append_recursion (x : ℕ) (l : List ℕ) : len (l ++ [x]) = 1 + len l  := by
  match l with
  | [] => rfl
  | y :: ys =>
    simp only [List.cons_append,len]
    simp only [Nat.add_left_cancel_iff]
    apply len_append_recursion

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
| a :: as =>
  if p a = true then a::(my_filter p as)
  else my_filter p as

#eval my_filter (fun x => x % 2 == 0) [1, 2, 3, 4, 5, 6]
example: my_filter (fun x => x % 2 == 0) [1, 2, 3, 4, 5, 6] = [2,4,6] := by rfl
-- Use `rfl` (reflexivity) if Lean can evaluate both sides to the same value.
-- Since `my_filter` is a recursive function and the input is concrete, Lean can compute it directly.

#eval my_filter (fun s => s.startsWith "a") ["apple", "banana", "almond", "kiwi"]
example: my_filter (fun s => s.startsWith "a") ["apple", "banana", "almond", "kiwi"] =  ["apple", "almond"] := by native_decide
-- `native_decide` uses the same computational backend as `#eval`
-- `rfl` only works for definitional equality - when terms are literally identical after basic reduction

-- Prove this:
theorem filter_append {α : Type} (p : α → Bool) (l1 l2 : List α) :
  my_filter p (l1 ++ l2) = (my_filter p l1) ++ (my_filter p l2) := by
  -- Approach 1:
  fun_induction my_filter p l1
  · grind
  · simp only [List.cons_append]
    -- rw [← ih1, my_filter, h]; rfl
    simp [← ih1, my_filter, h]
  · simp only [List.cons_append]
    -- rw [← ih1, my_filter, if_neg h]
    simp [← ih1, my_filter, h]
  -- `simp` can handle negation of a statement, whereas `rw` cannot (need `if_neg h`)

  -- Approach 2:
  -- induction l1 with
  -- | nil =>
  --   simp [my_filter]
  -- | cons head xs IH =>
  --   simp [my_filter]  -- This expands the definition
  --   by_cases h : p head = true
  --   · simp [h, IH]    -- Use the induction hypothesis
  --   · simp [h, IH]

  -- Approach 3:
  -- match l1 with
  -- -- | [] => simp [my_filter]
  -- | [] => rfl
  -- | x :: xs =>
  --   simp [my_filter]
  --   by_cases h : p x = true
  --   · simp [h, filter_append p xs l2]   -- Recursive call to the theorem itself!
  --   · simp [h, filter_append p xs l2]   -- Case where p x = false


-- # Exercise 3.2: write foldl
-- The foldl function (also known as reduce or fold-left)
-- combines the elements of a list using a binary operator,
-- starting from an initial value. It "folds" the list into a single value.
-- f: the combining function (accumulator -> element -> new_accumulator)
-- b: the initial base value (accumulator)

def my_foldl {α β : Type} (f : β → α → β) (b : β) : List α → β
| [] => b
| a :: as =>
  my_foldl f (f b a) as

#check my_foldl

example: my_foldl (fun acc x => acc + x) 0 [1, 2, 3, 4] = 10 := by simp [my_foldl]
example: my_foldl (fun acc x => x :: acc) ([] : List Nat) [1, 2, 3] = [3, 2, 1] := by simp [my_foldl]

-- Theorem
theorem foldl_append {α β : Type} (f : β → α → β) (b : β) (l1 l2 : List α) :
  my_foldl f b (l1 ++ l2) = my_foldl f (my_foldl f b l1) l2 := by
  fun_induction my_foldl
  · simp
  · simp_all [my_foldl]

-- # Exercise 3.3: Write map function that operates on lists
def my_map {α β : Type} (f : α → β) : List α → List β
| [] => []
| a :: as =>
  (f a) :: my_map f as

example: my_map (fun x => x + 1) [1, 2, 3] = [2,3,4] := by simp [my_map]
example: my_map (fun s => s.length) ["hello", "a", "world"] = [5,1,5] := by
  simp [my_map]
  aesop

-- Theorem: map composition
-- (f : α → β) (g : β → γ) (l : List α)
theorem map_map_comp {α β γ : Type} (f : α → β) (g : β → γ) (l : List α) :
  my_map (g ∘ f) l = my_map g (my_map f l) := by
  induction' l
  · simp [my_map]
  · simp_all [my_map]
