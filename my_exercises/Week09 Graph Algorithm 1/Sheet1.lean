import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Walk


namespace FAA

structure SimpleGraph (V : Type u) where
  /-- The adjacency relation of a simple graph. -/
  Adj : V → V → Prop
  symm : Symmetric Adj
  loopless : Irreflexive Adj

namespace SimpleGraph

variable {ι : Sort*} {V : Type u} (G : SimpleGraph V) {a b c u v w : V}

#check G

/-- `G.neighborSet v` is the set of vertices adjacent to `v` in `G`. -/
-- def neighborSet (v : V) : Set V := {w | G.Adj v w}

inductive Walk : V → V → Type u
  | nil {u : V} : Walk u u
  | cons {u v w : V} (h : G.Adj u v) (p : Walk v w) : Walk u w
  -- To build a Walk u w, take an edge h : u→v and prepend it to a walk p : v→w

/- # Walk is an inductive data type representing a path in the graph:
Walk u v: A walk from vertex u to vertex v
Two constructors:
nil: Empty walk from u to itself (no edges)
cons h p: A walk built by prepending one edge to an existing walk
h : G.Adj u v — proof of edge from u to v
p : Walk v w — remaining walk from v to w
Result: Walk u w (path from u to w)
-/

def Reachable (u v : V) : Prop := Nonempty (G.Walk u v)
def PreConnected : Prop := ∀ u v : V, G.Reachable u v

/- # Why G.Walk and G.Reachable work:
You're inside namespace SimpleGraph (line 13)

This means `Walk` and `Reachable` are defined as members of the SimpleGraph namespace
Dot notation automatically qualifies names

When you write G.Walk, Lean looks for Walk in the SimpleGraph namespace (since G : SimpleGraph V)
It expands to SimpleGraph.Walk
Similarly, G.Reachable expands to SimpleGraph.Reachable
The variable G : SimpleGraph V acts as a type hint

Lean uses G's type to know which namespace to search in
This is syntactic sugar that makes code more readable
-/

namespace Walk

variable {G}

/-- The length of a walk is the number of edges/darts along it. -/
def length {u v : V} : G.Walk u v → ℕ
  | nil => 0
  | cons _ q => q.length + 1

def triangle : SimpleGraph (Fin 3) where
  Adj := fun u v =>
    (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨  -- edge 0-1
    (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) ∨  -- edge 1-2
    (u = 2 ∧ v = 0) ∨ (u = 0 ∧ v = 2)    -- edge 2-0
  symm := by aesop_graph
  loopless := by simp_all [Irreflexive]

#check triangle

#check Walk.cons
def triangle_walk : triangle.Walk 0 2 :=
  SimpleGraph.Walk.cons (by simp [triangle] : triangle.Adj 0 1)
 (SimpleGraph.Walk.cons (by simp [triangle] : triangle.Adj 1 2)
  SimpleGraph.Walk.nil)

#eval length triangle_walk

/-- The concatenation of two compatible walks. -/
@[trans]
def append {u v w : V} : G.Walk u v → G.Walk v w → G.Walk u w
  | nil, q => q
  | cons h p, q => cons h (p.append q)
  /- # In the second case cons h p, q:
  The first argument G.Walk u v is destructured as cons h p

  h : G.Adj u v — the first edge
  p : Walk v w — remaining walk from v to w
  The second argument G.Walk v w remains as q
  -/

/-- The concatenation of the reverse of the first walk with the second walk. -/
def reverseAux {u v w : V} : G.Walk u v → G.Walk u w → G.Walk v w
  | nil, q => q
  | cons h p, q => Walk.reverseAux p (cons (G.symm h) q)

/-- The walk in reverse. -/
@[symm]
def reverse {u v : V} (w : G.Walk u v) : G.Walk v u := w.reverseAux nil

lemma length_reverse_aux {u v : V} (p: G.Walk u v) (q: G.Walk u w):
  (p.reverseAux q).length = p.length + q.length := by
  fun_induction reverseAux
  · aesop
  · expose_names
    rw [ih1]
    simp [length]
    omega

/-- Example : The reverse of a walk has the same length -/
-- requires the more general lemma as above
lemma length_reverse {u v : V} (p : G.Walk u v) : p.reverse.length = p.length := by
  simp [reverse]
  apply length_reverse_aux

/-- Exercise : The length of appended walks is the sum of their lengths -/
lemma length_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).length = p.length + q.length := by
  fun_induction append
  · aesop
  · expose_names
    simp [length]
    rw [ih1]
    omega

@[symm]
theorem reachable_symm {v w : V} (hvw : G.Reachable v w) :
    G.Reachable w v := by
    exact (Nonempty.congr (fun a ↦ id a.reverse) fun a ↦ id a.reverse).mpr hvw

#check Nonempty
#check Nonempty.intro

-- Do it together.
@[trans]
theorem reachable_trans {u v w : V} (huv : G.Reachable u v) (hvw : G.Reachable v w) :
    G.Reachable u w := by
    cases huv
    cases hvw
    simp [Reachable]
    refine Nonempty.intro ?_
    (expose_names; exact val.append val_1)

-- Example
lemma connected_iff_exists_forall_reachable [nonempty : Nonempty V]: G.PreConnected ↔ ∃ v, ∀ w, G.Reachable v w := by
  constructor
  · sorry
  · intro h
    obtain ⟨v,h⟩ := h
    simp [PreConnected]
    sorry

-- Exercise
lemma preconnected_iff_forall_reachable :
    G.PreConnected ↔ ∀ u v : V, G.Reachable u v := by
  sorry

-- Exercise
lemma exists_central_vertex_if_connected [Fintype V] [Nonempty V]
    (hG : G.PreConnected) :
    ∃ v : V, ∀ w : V, ∃ (p : G.Walk v w), p.length ≤ Fintype.card V - 1 := by
  sorry


end Walk
end SimpleGraph
end FAA
