import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
set_option tactic.hygienic false


/-! Inductive Type

In Lean 4, an inductive type is a way to define a new type by specifying its constructors,
which describe all possible ways to create values of that type.

* An inductive type is defined by listing its constructors.
  Each constructor can take arguments, allowing the creation of more complex structures.
* Inductive types can be recursive, meaning a constructor can include the type itself as part of its arguments.
  This enables defining structures like lists or trees.

-/

-- # Simple Inductive Type: Enumeration
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
| Color.Green => "Green is calming."
| .Blue  => "Blue is clear."

def favoriteColor2 (c : Color) : String := match c with
| Color.Red   => "Red is lovely"
| .Green => "Green is calming."
| .Blue  => "Blue is clear."

#eval favoriteColor Color.Red
#check favoriteColor
#check favoriteColor2

-- # Inductive type: Atomic element and a function
inductive MyOptionNat
| none
| some : ℕ → MyOptionNat

#check MyOptionNat
#check MyOptionNat.none
#check MyOptionNat.some
#check MyOptionNat.some 1
#check MyOptionNat.some 100

-- Here, If OptionNat is a set, then it contains {.none, .some 1, .some 2, .some 3, ...}

-- ℕ can be generalized to a type α
-- Now, let's define a new type called `MyOption` parameterized by a type α.
inductive MyOption1 (α : Type)
| none
| some : α → MyOption1 α

#check MyOption1
#check MyOption1 ℕ
#check MyOption1.none
#check (MyOption1.none : MyOption1 ℕ)
#check MyOption1.some
#check MyOption1.some 50
#check (MyOption1.some 50 : MyOption1 ℕ)
#check MyOption1.some "mystring"
#check (MyOption1.some "mystring" : MyOption1 String)

-- Alternatively, some : α → MyOption α  can be written as some (a : α)
inductive MyOption2 (α : Type)
| none
| some (a : α)

#check MyOption2
#check MyOption2 ℕ
#check MyOption2.none
#check (MyOption2.none : MyOption2 ℕ)
#check MyOption2.some
#check MyOption2.some 1
#check (MyOption2.some 1 : MyOption2 ℕ)
#check MyOption2.some "mystring"
#check (MyOption2.some "mystring" : MyOption2 String)


-- Option can be used to implement to get some element
def getOrElse {α : Type} (opt : MyOption1 α) (default : α) : α :=
  match opt with
  | .none   => default
  | .some x => x

-- # Recursive Inductive Type: Nat
inductive nat1
| zero
| succ (n: nat1)
-- If nat is a set, then zero ∈ nat
-- If zero ∈ nat, then succ (zero) ∈ nat, and then succ (succ (zero)) ∈ nat
-- So, nat = {z,sz,ssz,sssz}

#check nat1.zero
#check nat1.succ
#check nat1.zero.succ
#check nat1.succ (.zero)
#check nat1.succ (.succ (.zero))
#check nat1.zero.succ.succ
-- {0, succ(0), succ (succ (0))} ..
-- {0, 00, 000,0000, ...}

-- ## Example application
def one : nat1 := .succ .zero
def two : nat1 := .succ (.succ .zero)
#check nat1.succ .zero
#check one
#check nat1.succ (.succ .zero)
#check two

-- ## Equivalent definition
inductive nat2
| zero : nat2
| succ : nat2 → nat2
-- basecase : 0 ∈ S
-- inductive: if x ∈ S, then x+1 ∈ S

-- # Recursive Inductive Type: List
namespace MyList

inductive List (α : Type)
| nil
-- nil: the empty list.
| cons (a : α) (l : List α )
-- cons: a constructor that takes an element a : α and a list l : List α, and returns a new list.

-- the type List α is either
-- 1. an empty list (nil) or
-- 2. cons x xs where x : α and xs : List α
-- {[], [x], [x₁ x₂], [x₁ x₂ x₃] … }
#check List ℕ

#check List.nil
#check (List.nil : List ℕ)
-- []

#check List.cons
#check List.cons 1 List.nil
#check (List.cons 1 .nil)
#check (List.cons 1 List.nil : List ℕ)
-- [1]

#check List.cons 2 (.cons 1 (.nil))
#check (List.cons 2 (.cons 1 (.nil)) : List ℕ)
-- [2 1]

-- Equivalently, it can be written this way in the functional form (Haskell-like)
inductive ListF (α : Type)
| nil : ListF α
-- nil: explicitly typed as ListF α.
| cons : α → ListF α → ListF α
-- cons: a constructor that takes an α and a ListF α, and returns a ListF α.

#check List
#check List.nil
#check List.cons

-- # Exercise 2.1
-- Define a type of binary tree
-- it is a leaf or a node with two subtrees
inductive BinaryTree (α : Type)
  | leaf
  -- leaf represents an empty tree (or a terminal node with no value).
  | node (a: α) (left: BinaryTree α) (right: BinaryTree α)
  -- node represents a non-empty tree node that:
  -- Stores a value a : α,
  -- Has a left subtree,
  -- Has a right subtree.

#check BinaryTree.node 1 BinaryTree.leaf BinaryTree.leaf
--     1
--    / \
--  leaf leaf
#check BinaryTree.node "node_1" BinaryTree.leaf BinaryTree.leaf
--   "node_1"
--    / \
--  leaf leaf

-- Equivalent definition 1: the position of `(a : α)` doen't make difference
inductive BinaryTree' (α : Type)
  | leaf
  | node (left: BinaryTree' α) (a : α) (right: BinaryTree' α)

-- Equivalent definition 2: curried format `node` constructor
inductive BinaryTree'' (α : Type)
  | leaf : BinaryTree'' α
  | node : α → BinaryTree'' α → BinaryTree'' α → BinaryTree'' α
  -- α → (BinaryTree'' α → (BinaryTree'' α → BinaryTree'' α))
  -- First you give it a value `a` : α,
  -- Then you give it a left subtree `left` : BinaryTree'' α,
  -- Then a right subtree `right` : BinaryTree'' α,
  -- And finally you get a tree node `a left right` : BinaryTree'' α.
#check BinaryTree''.node "node_1" BinaryTree''.leaf BinaryTree''.leaf


#check BinaryTree
#check BinaryTree.leaf
#check (BinaryTree.leaf : BinaryTree ℕ)
#check BinaryTree.node


inductive BinaryTree1 (α : Type)
| leaf (a : α)
| node (left : BinaryTree1 α) (right : BinaryTree1 α) (a : α)
-- miss the trees where some leaves have no value

inductive BinaryTree2 (α : Type)
| leaf
| node (left : BinaryTree2 α) (right : BinaryTree2 α)
-- structural binary tree without data

end MyList
