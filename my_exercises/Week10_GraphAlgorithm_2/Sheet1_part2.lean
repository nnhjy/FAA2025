import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Combinatorics.SimpleGraph.Metric

structure FinSimpleGraph (V : Type u) [Fintype V] [DecidableEq V]  extends SimpleGraph V

noncomputable
instance fintypeFinSimpleGraph {V : Type u} [Fintype V] [DecidableEq V] (G : FinSimpleGraph V) (v : V):
  Fintype (G.neighborSet v) :=  Fintype.ofFinite ↑(G.neighborSet v)

open Finset SimpleGraph

variable  {V : Type*} [Fintype V] [DecidableEq V]

noncomputable
def bfs_rec
(G : FinSimpleGraph V)
(queue : List V)
(visited : Finset V)
  :=
  match queue with
  | [] => visited
  | v :: queue =>
    let new_neighbors := (G.neighborFinset v) \ visited
    let queue' := queue ++ new_neighbors.toList
    let visited' := visited ∪ new_neighbors
    bfs_rec G queue' visited'
    termination_by (Fintype.card V - #visited, queue.length)
    -- Week09.HW08.Problem1
    decreasing_by sorry

#check bfs_rec.induct

noncomputable def bfs
  (G : FinSimpleGraph V)
  (s : V)
  : Finset V :=
  bfs_rec G {s} {s}

/-
Lemma 1 : s ∈ bfs G s
-/
lemma lemma_1_helper {s} {G : FinSimpleGraph V} (queue : List V) (visited : Finset V) :
  s ∈ visited → s ∈ bfs_rec G queue visited := by
  fun_induction bfs_rec G queue visited <;> all_goals expose_names
  · exact fun x ↦ x
    -- simp
  · intro hs
    apply ih1
    exact mem_union_left new_neighbors hs

#check bfs_rec

lemma lemma_1_s_in_bfs_s {s} {G : FinSimpleGraph V} : s ∈ bfs G s := by
  apply lemma_1_helper {s} {s} (by simp)

  -- # Lecture approach
  -- simp [bfs]
  -- apply aux
  -- intro v
  -- exact fun a ↦ a
  -- aesop

  -- where aux (v : V)(queue : List V) (visited: Finset V)
  --   (h: ∀ x ∈ queue, x ∈ visited)
  --   (h2: v ∈ queue.toFinset ∪ visited) : v ∈ bfs_rec G queue visited := by {
  --   fun_induction bfs_rec G queue visited <;> simp_all; aesop
  -- }

  -- # alternative approach
  -- suffices ∀ queue visited, s ∈ visited → s ∈ bfs_rec G queue visited by
  --   apply this
  --   rw [Finset.mem_singleton]
  -- intro queue visited
  -- fun_induction bfs_rec <;> expose_names
  -- · simp
  -- · intro hmem
  --   apply ih1
  --   exact mem_union_left new_neighbors hmem

  -- # alternative approach not seem to work
  -- unfold bfs
  -- fun_induction bfs_rec G {s} {s} generalizing s
  -- all_goals expose_names
  -- · sorry -- why this doen't work?
  -- · exact ih1

-- The key insight: Strengthen the statement to make it provable by induction.
-- Instead of proving the specific case s ∈ bfs_rec G [s] {s}, we prove a more general invariant that:

-- 1. Holds at the start
-- 2. Is preserved by each recursive call
-- 3. Implies what we want
