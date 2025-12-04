import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Combinatorics.SimpleGraph.Metric

structure FinSimpleGraph (V : Type u) [Fintype V] [DecidableEq V]  extends SimpleGraph V

noncomputable
instance  fintypeFinSimpleGraph {V : Type u} [Fintype V] [DecidableEq V] (G : FinSimpleGraph V) (v : V): Fintype (G.neighborSet v) :=  Fintype.ofFinite ↑(G.neighborSet v)

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

theorem v_bfs_of_neighbor_bfs_helper (G : FinSimpleGraph (V))
  (queue : List (V))
  (visited : Finset (V))
  (w v: V) :
  let new_neighbors := G.neighborFinset v \ visited
  let queue' := queue ++ new_neighbors.toList
  let visited' := visited ∪ new_neighbors
  w ∈ bfs_rec G (v :: queue) visited → w ∈ bfs_rec G queue' visited' := by
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
  termination_by (Fintype.card V - #visited, queue.length)
  -- Week09.HW08.Problem1
  decreasing_by sorry

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
    · simp_all
      aesop
    -- # `aesop?` gives the structure below, which turns out hard to work with
    -- · simp
    --   intro x hx1 hx2 hx3
    --   simp_all only [
    --     List.mem_cons, forall_eq_or_imp, List.toFinset_cons, mem_sdiff,
    --     mem_insert, List.mem_toFinset, not_or, and_imp]
    --   obtain ⟨left, right⟩ := h_queue_nodes_in_visited
    --   cases hx1 with
    --   | inl h =>
    --     simp_all only [implies_true]
    --     intro y hy
    --     by_cases hv : v ≠ x
    --     · aesop
    --     · simp at hv
    --       subst hv
    --       simp_all only [mem_neighborSet, Set.mem_union, mem_coe, mem_neighborFinset, or_true]
    --   | inr h_1 =>
    --     simp_all only [forall_const]
    --     intro y hy
    --     by_cases hv : v ≠ x
    --     · aesop
    --     · simp at hv
    --       subst hv
    --       simp only [Set.mem_union, mem_coe, mem_neighborFinset]
    --       simp_all
    · simp
      intro x hx1 hx2 hx3 y hy
      -- According to the `h_visited`
      -- `exact?` would give the proof
      obtain h | h : x = v ∨ x ≠ v := by exact eq_or_ne x v
      all_goals (aesop)
      -- · simp_all
      -- · simp_all
      --   have hx_visited : x ∈ visited := by
      --     cases hx1
      --     all_goals expose_names
      --     · exact h_1
      --     · apply hx3; exact h_1
      --   replace h_visited : G.neighborSet x ⊆ ↑visited := by simp_all
      --   left
      --   apply h_visited
      --   exact hy
    · apply v_bfs_of_neighbor_bfs_helper
      exact h3
  termination_by (Fintype.card V - #visited, queue.length)
  -- Week09.HW08.Problem1
  decreasing_by sorry

/-
Lemma 2 : u ∈ bfs G s ∧ v ∈ G.neighborFinset u → v ∈ bfs G s
-/
lemma lemma2_u_bfs_so_are_neighbors (G : FinSimpleGraph V) (s u v) :
  u ∈ bfs G s ∧ v ∈ G.neighborSet u → v ∈ bfs G s := by
  simp only [mem_neighborSet, and_imp, bfs]
  intro h1 h2
  apply v_bfs_of_neighbor_bfs G {s} {s} u
  · exact fun x a ↦ a
  · intro h hx
    simp at hx
    obtain ⟨ hs, hns ⟩ := hx
    subst hs
    -- # How the following work?
    rw [List.singleton_eq] at hns
    simp_all
  · exact h1
  · simp_all
