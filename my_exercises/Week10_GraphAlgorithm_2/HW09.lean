import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Combinatorics.SimpleGraph.Metric

structure FinSimpleGraph (V : Type u) [Fintype V] [DecidableEq V] extends SimpleGraph V

noncomputable
instance  fintypeFinSimpleGraph {V : Type u} [Fintype V] [DecidableEq V] (G : FinSimpleGraph V) (v : V): Fintype (G.neighborSet v) :=  Fintype.ofFinite ↑(G.neighborSet v)

open Finset SimpleGraph

variable  {V : Type*} [Fintype V] [DecidableEq V]

-- We will use the following version of BFS algorithm.
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
## Problem 1: Prove that BFS never returns an empty set.
-/
lemma bfs_rec_nonempty (G : FinSimpleGraph V) (queue : List V) (visited : Finset V)
  (h : visited.Nonempty) : (bfs_rec G queue visited).Nonempty := by
  fun_induction bfs_rec
  all_goals expose_names
  · exact h
  · aesop

theorem Problem1 (G : FinSimpleGraph V) (s : V) :
  (bfs G s).Nonempty := by
  unfold bfs
  apply bfs_rec_nonempty
  exact singleton_nonempty s

/-
## Problem 2: Prove that the visited set only grows during BFS.
-/

theorem Problem2 (G : FinSimpleGraph V) (queue : List V) (visited : Finset V) :
  visited ⊆ bfs_rec G queue visited := by
  intro x hxv
  fun_induction bfs_rec
  all_goals aesop

/-
## Problem 3:
Prove that on a complete graph (where every vertex is connected to every other),
BFS from any vertex s returns all vertices.
-/

-- # Helper lemma from Week10.Sheet1_part3
theorem v_bfs_of_neighbor_bfs (G : FinSimpleGraph (V))
  (queue : List (V))
  (visited : Finset (V))
  (w : V)
  (h_queue_nodes_in_visited : ∀ x ∈ queue, x ∈ visited)
  (h_visited: ∀ x ∈ visited \ queue.toFinset , G.neighborSet x ⊆ visited)
  (h3: w ∈ bfs_rec G queue visited) :
    ∀ v ∈ G.neighborSet w, v ∈ bfs_rec G queue visited := by
  match queue with
  | [] =>
    simp_all [bfs_rec]
    exact fun v a ↦ h_visited w h3 a
  | v :: queue =>
    unfold bfs_rec
    dsimp
    apply v_bfs_of_neighbor_bfs
    · aesop
    · simp
      intro x hx1 hx2 hx3 y hy
      -- According to the `h_visited`
      -- `exact?` would give the proof
      obtain h | h : x = v ∨ x ≠ v := by exact eq_or_ne x v
      all_goals (aesop)
    · apply v_bfs_of_neighbor_bfs_helper
      exact h3
  termination_by (Fintype.card V - #visited, queue.length)
  -- Week09.HW08.Problem1
  decreasing_by sorry

  -- # Also from Week10.Sheet1_part3
  where v_bfs_of_neighbor_bfs_helper (G : FinSimpleGraph (V))
    (queue : List (V))
    (visited : Finset (V))
    (w v: V) :
    let new_neighbors := G.neighborFinset v \ visited
    let queue' := queue ++ new_neighbors.toList
    let visited' := visited ∪ new_neighbors
    w ∈ bfs_rec G (v :: queue) visited → w ∈ bfs_rec G queue' visited' := by {
    match hq_cases : queue with
    | [] => simp_all [bfs_rec]
    | u :: qt =>
      intro new_n q' v' hw
      unfold bfs_rec
      apply v_bfs_of_neighbor_bfs_helper
      show w ∈ bfs_rec G (u :: qt ++ new_n.toList) (visited ∪ new_n)
      unfold bfs_rec at hw
      subst hq_cases
      simp_all only [List.cons_append, union_sdiff_self_eq_union]
      simp_all [new_n]
  }
  termination_by (Fintype.card V - #visited, queue.length)
  -- Week09.HW08.Problem1
  decreasing_by sorry

def FinSimpleGraph.IsComplete (G : FinSimpleGraph V) : Prop :=
  ∀ u v : V, u ≠ v → G.Adj u v

-- # Helper lemma: bfs_rec from any vertex s returns all vertices.
lemma bfs_rec_complete_all_verts (G : FinSimpleGraph V) (queue : List V) (visited : Finset V)
  (hG : G.IsComplete) (h_init : visited.Nonempty)
  (h_queue_in_visited : ∀ x ∈ queue, x ∈ visited)
  (h_visited_closed : ∀ x ∈ visited \ queue.toFinset, G.neighborSet x ⊆ visited)
  : bfs_rec G queue visited = Finset.univ := by
  unfold FinSimpleGraph.IsComplete at hG
  refine eq_univ_of_forall ?_
  intro x
  -- Pick any vertex `v ∈ visited`
  obtain ⟨v, hv⟩ := h_init
  -- Show that `bfs_rec` would contain the `v` at some point
  have hv_bfs : v ∈ bfs_rec G queue visited := by
    apply Problem2; exact hv

  -- Since G is complete, x is a neighbor of v (if x ≠ v)
  obtain hvx | hvx : v = x ∨ v ≠ x := by exact eq_or_ne v x
  -- # or equivalently,
  -- `by_cases hvx : v = x`
  · subst hvx; exact hv_bfs
  · have hadj : x ∈ G.neighborSet v := by
      unfold SimpleGraph.neighborSet
      simp
      exact hG v x hvx
    -- Apply v_bfs_of_neighbor_bfs
    exact v_bfs_of_neighbor_bfs G queue visited v h_queue_in_visited h_visited_closed hv_bfs x hadj

theorem Problem3 (G : FinSimpleGraph V) (s : V) (hG : G.IsComplete) :
  bfs G s = Finset.univ := by
  unfold bfs
  apply bfs_rec_complete_all_verts
  · exact hG
  · exact singleton_nonempty s
  · intro x
    exact fun a ↦ a
  · intro x hx
    simp at hx

    exfalso
    obtain ⟨h1, h2⟩ := hx
    subst h1
    exact h2 (Finset.mem_singleton_self x)

    -- cases hx with
    -- | intro h1 h2 =>
    --   exfalso
    --   subst h1
    --   exact h2 (Finset.mem_singleton_self x)
