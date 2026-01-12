import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Graph Connectivity using Mathlib's SimpleGraph

This file reformulates the educational graph theory examples using Mathlib's
built-in `SimpleGraph` infrastructure, which provides paths, reachability,
and the key lemma that paths have bounded length.

## Key Mathlib definitions used:
- `SimpleGraph V` : A simple graph on vertex type V
- `SimpleGraph.Walk u v` : A walk from u to v
- `SimpleGraph.Walk.IsPath` : Predicate that a walk has no repeated vertices
- `SimpleGraph.Walk.toPath` : Converts any walk to a path with same endpoints
- `SimpleGraph.Reachable u v` : Nonempty (G.Walk u v)
- `SimpleGraph.Preconnected` : ∀ u v, G.Reachable u v
-/

namespace MathlibGraphs

variable {V : Type*} (G : SimpleGraph V)

-- ============================================================================
-- BASIC WALK OPERATIONS (these mirror your educational examples)
-- ============================================================================

section WalkBasics

variable {G}

-- Mathlib already provides Walk.length, Walk.append, Walk.reverse
-- Here we show they exist:

#check SimpleGraph.Walk.length
#check SimpleGraph.Walk.append
#check SimpleGraph.Walk.reverse

-- And the lemmas you proved are already in Mathlib:
#check SimpleGraph.Walk.length_reverse
#check SimpleGraph.Walk.length_append

end WalkBasics

-- ============================================================================
-- TRIANGLE EXAMPLE
-- ============================================================================

section TriangleExample

/-- A triangle graph on 3 vertices using Mathlib's SimpleGraph -/
def triangle : SimpleGraph (Fin 3) where
  Adj := fun u v =>
    (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨
    (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) ∨
    (u = 2 ∧ v = 0) ∨ (u = 0 ∧ v = 2)
  symm := by aesop_graph
  loopless := by simp_all [Irreflexive]

/-- A walk from 0 to 2 via vertex 1 -/
def triangle_walk : triangle.Walk 0 2 :=
  SimpleGraph.Walk.cons (by simp [triangle] : triangle.Adj 0 1)
    (SimpleGraph.Walk.cons (by simp [triangle] : triangle.Adj 1 2)
      SimpleGraph.Walk.nil)

#check triangle_walk.length  -- Should be 2

end TriangleExample

-- ============================================================================
-- REACHABILITY LEMMAS
-- ============================================================================

section Reachability

variable {G}

-- Mathlib already has these, but we can reprove them for practice:

theorem reachable_symm' {v w : V} (hvw : G.Reachable v w) : G.Reachable w v := by
  obtain ⟨p⟩ := hvw
  exact ⟨p.reverse⟩

theorem reachable_trans' {u v w : V} (huv : G.Reachable u v) (hvw : G.Reachable v w) :
    G.Reachable u w := by
  obtain ⟨p⟩ := huv
  obtain ⟨q⟩ := hvw
  exact ⟨p.append q⟩

-- Mathlib's versions:
#check SimpleGraph.Reachable.symm
#check SimpleGraph.Reachable.trans

end Reachability

-- ============================================================================
-- CONNECTIVITY LEMMAS
-- ============================================================================

section Connectivity

variable {G}

lemma connected_iff_exists_forall_reachable [Nonempty V] :
    G.Preconnected ↔ ∃ v, ∀ w, G.Reachable v w := by
  constructor
  · intro h
    obtain ⟨v⟩ := ‹Nonempty V›
    exact ⟨v, fun w => h v w⟩
  · intro ⟨v, hv⟩
    intro u w
    exact (hv u).symm.trans (hv w)

lemma preconnected_iff_forall_reachable :
    G.Preconnected ↔ ∀ u v : V, G.Reachable u v := by
  rfl  -- This is definitionally true in Mathlib

end Connectivity

-- ============================================================================
-- THE MAIN LEMMA: CENTRAL VERTEX WITH BOUNDED WALKS
-- ============================================================================

section MainLemma

variable {G}

/--
In a connected finite graph, there exists a vertex from which every other vertex
is reachable via a walk of length at most `card V - 1`.

This proof uses two key Mathlib lemmas:
1. `Walk.toPath` : Any walk can be converted to a path (no repeated vertices)
2. `Walk.IsPath.length_lt` : A path in a graph with n vertices has length < n

Note: This lemma requires `DecidableEq V` because `Walk.toPath` needs to check
whether vertices have been visited before.
-/
lemma exists_central_vertex_if_connected [Fintype V] [DecidableEq V] [Nonempty V]
    (hG : G.Preconnected) :
    ∃ v : V, ∀ w : V, ∃ (p : G.Walk v w), p.length ≤ Fintype.card V - 1 := by
  -- Pick any vertex as the "central" vertex
  obtain ⟨v⟩ := ‹Nonempty V›
  use v
  intro w
  -- Get a walk from preconnectedness
  obtain ⟨walk⟩ := hG v w
  -- Convert the walk to a path (this removes any cycles/repeated vertices)
  let path := walk.toPath
  -- Use the path as our witness
  use path.val
  -- A path has length < card V, which means length ≤ card V - 1
  have h_length_lt : path.val.length < Fintype.card V := path.property.length_lt
  omega

/--
Alternative formulation: every pair of vertices can be connected by a short walk.
-/
lemma exists_short_walk_between_any_vertices [Fintype V] [DecidableEq V]
    (hG : G.Preconnected) (u v : V) :
    ∃ (p : G.Walk u v), p.length ≤ Fintype.card V - 1 := by
  obtain ⟨walk⟩ := hG u v
  let path := walk.toPath
  use path.val
  have h := path.property.length_lt
  omega

end MainLemma

-- ============================================================================
-- BONUS: Understanding Walk.toPath
-- ============================================================================

section WalkToPathExplanation

/-!
## How Walk.toPath works

`Walk.toPath` is defined in Mathlib and works by:
1. Walking along the original walk
2. At each step, checking if the next vertex was already visited
3. If yes, it "shortcuts" by skipping the cycle
4. If no, it keeps the edge

This produces a path (walk with no repeated vertices) with the same endpoints.

The key lemma `IsPath.length_lt` proves that a path visiting n distinct vertices
can have at most n-1 edges (since each edge goes to a new vertex).
-/

#check @SimpleGraph.Walk.toPath
#check @SimpleGraph.Walk.IsPath.length_lt

end WalkToPathExplanation

end MathlibGraphs
