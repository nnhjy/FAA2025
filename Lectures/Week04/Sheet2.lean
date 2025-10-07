import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
set_option tactic.hygienic false


/-! Inductive Type

In Lean 4, an inductive type is a way to define a new type by specifying its constructors,
which describe all possible ways to create values of that type.

* An inductive type is defined by listing its constructors. Each constructor can take arguments, allowing the creation of more complex structures.
* Inductive types can be recursive, meaning a constructor can include the type itself as part of its arguments. This enables defining structures like lists or trees.

-/

-- Simple Inductive Type: Enumeration
inductive Color
| Red : Color
| Green : Color
| Blue : Color

#check Color
#check Color.Red

inductive Color'
| Red
| Green
| Blue

def favoriteColor : Color → String
| .Red   => "Red is lovely"
| .Green => "Green is calming."
| .Blue  => "Blue is clear."

def favoriteColor2 (c : Color) : String := match c with
| .Red   => "Red is lovely"
| .Green => "Green is calming."
| .Blue  => "Blue is clear."

#eval favoriteColor Color.Red

-- Inductive Type with Parameters
inductive MyOption (α : Type)
| none
| some : α → MyOption α

#check MyOption ℕ
#check (MyOption.none : MyOption ℕ)
#check MyOption.some 2

def getOrElse {α : Type} (opt : MyOption α) (default : α) : α :=
  match opt with
  | .none   => default
  | .some x => x

-- Recursive Inductive Type: Nat
inductive nat : Type
| zero : nat
| succ (n: nat) : nat

inductive nat2 : Type
| zero : nat2
| succ : nat2 → nat2

-- basecase : 0 ∈ S
-- inductive: if x ∈ S, then x+1 ∈ S

-- {0, succ(0), succ (succ (0))}..
example: nat.zero ≠ nat.zero.succ := by aesop
#check nat.zero
#check nat.zero.succ.succ

-- Recursive Inductive Type: List
namespace MyList

inductive List (α : Type)
| nil : List α
| cons : α → List α → List α

-- the type List α is either
-- 1. an empty list (nil) or
-- 2. cons x xs where x : α and xs : List α
-- {[], [x], [x₁ x₂], [x₁ x₂ x₃] … }

#check List
#check List.nil
#check List.cons

inductive List2 (α : Type)
| nil : List2 α
| cons (n: α) (l : List2 α) : List2 α

#check List2.nil -- []
#check List2.cons 10 List2.nil -- [10]
#check List2.cons 10 (List2.cons 5 List2.nil) -- [10,5]

end MyList
