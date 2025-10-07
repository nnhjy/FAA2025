import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
set_option tactic.hygienic false


def reverse {α : Type} : List α → List α
| [] => []
| a :: xs => reverse xs ++ [a]

def len {α : Type} : List α → ℕ
| []     =>  0
| _ :: xs => 1 + len xs

-- Exercise: Write map function that operates on lists
def my_map {α β : Type} (f : α → β) : List α → List β
| [] => []
| a :: as => sorry

example: my_map (fun x => x + 1) [1, 2, 3] = [2,3,4] := sorry
example: my_map (fun s => s.length) ["hello", "a", "world"] = [5,1,5] := sorry

-- Theorem: map composition
-- (f : α → β) (g : β → γ) (l : List α)
theorem map_map_comp {α β γ : Type} (f : α → β) (g : β → γ) (l : List α) :
  my_map (g ∘ f) l = my_map g (my_map f l) := by sorry

-- Exercise: write foldl
-- The foldl function (also known as reduce or fold-left)
-- combines the elements of a list using a binary operator,
-- starting from an initial value. It "folds" the list into a single value.
-- f: the combining function (accumulator -> element -> new_accumulator)
-- b: the initial base value (accumulator)

def my_foldl {α β : Type} (f : β → α → β) (b : β) : List α → β
| [] => b
| a :: as => sorry

example: my_foldl (fun acc x => acc + x) 0 [1, 2, 3, 4] = 10 := sorry
example: my_foldl (fun acc x => x :: acc) ([] : List Nat) [1, 2, 3] = [3, 2, 1] := sorry

-- Theorem
theorem foldl_append {α β : Type} (f : β → α → β) (b : β) (l1 l2 : List α) :
  my_foldl f b (l1 ++ l2) = my_foldl f (my_foldl f b l1) l2 := by sorry
