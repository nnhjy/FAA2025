import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Tactic

structure FinSimpleGraph (V : Type u) [Fintype V] [DecidableEq V]  extends SimpleGraph V

noncomputable
instance  fintypeFinSimpleGraph {V : Type u} [Fintype V] [DecidableEq V] (G : FinSimpleGraph V) (v : V): Fintype (G.neighborSet v) :=  Fintype.ofFinite ↑(G.neighborSet v)

open Finset SimpleGraph

variable  {V : Type*} [Fintype V] [DecidableEq V]

-- (20 pt): Prove that BFS terminates
-- You can use basic facts about Finset and any helper lemmas from Mathlib

theorem Problem1 (G : FinSimpleGraph V) (visited : Finset V) (v : V) :
  let n := Fintype.card V
  n - #(visited ∪ G.neighborFinset v) < n - #visited ∨
  n - #(visited ∪ G.neighborFinset v) = n - #visited ∧ G.neighborFinset v ⊆ visited := by
  simp only
  have h_subset : G.neighborFinset v \ visited ⊆ G.neighborFinset v := by
    simp only [sdiff_subset]
  have h_card_nonneg : 0 ≤ #(G.neighborFinset v \ visited) := by
    exact Nat.zero_le _
  have h_card_le : #(G.neighborFinset v \ visited) ≤ #(G.neighborFinset v) := by
    exact Finset.card_mono h_subset
  have h_card_pos : #(G.neighborFinset v) ≤ Fintype.card V := by
    exact Finset.card_le_univ _

  by_cases h : G.neighborFinset v ⊆ visited
  · right
    constructor
    · have h_union : visited ∪ G.neighborFinset v = visited := by
        ext x
        simp only [Finset.mem_union]
        exact ⟨fun hx => hx.elim id (fun hnf => h hnf), fun hv => Or.inl hv⟩
      simp [h_union]
    · exact h
  · left
    push_neg at h
    have h_diff_nonempty : G.neighborFinset v \ visited ≠ ∅ := by
      by_contra hempty
      apply h
      intro x hx
      by_contra hnv
      have : x ∈ G.neighborFinset v \ visited := Finset.mem_sdiff.mpr ⟨hx, hnv⟩
      rw [Finset.eq_empty_iff_forall_notMem] at hempty
      exact absurd this (hempty x)
    have h_pos : 0 < #(G.neighborFinset v \ visited) := by
      exact Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h_diff_nonempty)
    have h_disjoint : Disjoint visited (G.neighborFinset v \ visited) := by
      exact disjoint_left.mpr fun x hxv hxdiff => (Finset.mem_sdiff.mp hxdiff).2 hxv
    have h_union_card : #(visited ∪ G.neighborFinset v \ visited) = #visited + #(G.neighborFinset v \ visited) := by
      rw [Finset.card_union_of_disjoint h_disjoint]
    have h_union_eq : visited ∪ G.neighborFinset v \ visited = visited ∪ G.neighborFinset v := by
      exact union_sdiff_self_eq_union
    have h_union_card' : #(visited ∪ G.neighborFinset v) = #visited + #(G.neighborFinset v \ visited) := by
      rw [← h_union_eq]
      exact h_union_card
    rw [h_union_card']
    have h_visited_le : #visited ≤ Fintype.card V := by
      exact Finset.card_le_univ visited
    have h_neighbor_le : #(G.neighborFinset v) ≤ Fintype.card V := by
      exact Finset.card_le_univ _
    have h_sum_le : #visited + #(G.neighborFinset v \ visited) ≤ Fintype.card V := by
      have h_union_le : #(visited ∪ G.neighborFinset v) ≤ Fintype.card V := Finset.card_le_univ _
      rw [← h_union_card']
      exact h_union_le
    omega


-- the following set up is given for you. You don't have to edit this part
theorem bfs_termination_proof (G : FinSimpleGraph V)(visited : Finset V) (v : V) (queue : List V) :
  let n := Fintype.card V
  Prod.Lex (fun a₁ a₂ ↦ a₁ < a₂) (fun a₁ a₂ ↦ a₁ < a₂)
    (n - #(visited ∪ G.neighborFinset v \ visited), (queue ++ (G.neighborFinset v \ visited).toList).length)
    (n - #visited, (v :: queue).length) := by

    simp only [union_sdiff_self_eq_union, List.length_append, length_toList, List.length_cons]
    refine Prod.lex_iff.mpr ?_
    simp only [add_lt_add_iff_left, Nat.lt_one_iff, card_eq_zero, sdiff_eq_empty_iff_subset]
    exact Problem1 G visited v

-- We will use the following BFS algorithm
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
    decreasing_by apply bfs_termination_proof

noncomputable
def bfs
  (G : FinSimpleGraph V)
  (s : V)
  : Finset V :=
  bfs_rec G {s} {s}

-- Problem 2 and 3, you are asked to prove the following simple properties of BFS algorithms

-- (20 pts): Prove the following theorem
theorem Problem2 {G : FinSimpleGraph V}
  {v : V}
  (queue : List V)
  (visited : Finset V)
  (h_queue_nodes_in_visited : ∀ x ∈ queue, x ∈ visited)
  (h: v ∈ queue.toFinset ∪ visited):
  v ∈ bfs_rec G queue visited := by
  fun_induction bfs_rec
  · simp_all
  · expose_names
    simp_all
    cases h
    · expose_names
      apply ih1; clear ih1
      · aesop
      · have v_in_queue' : v ∈ queue' := by simp_all [queue']
        left
        exact v_in_queue'
    · expose_names
      apply ih1; clear ih1
      · aesop
      · have v_in_visited' : v ∈ visited' := by simp_all [visited']
        right
        exact v_in_visited'

-- (20 pts): Prove the following theorem
theorem Problem3 (G : FinSimpleGraph V)
  (queue : List V)
  (visited : Finset V)
  (w v: V) :
  let new_neighbors := G.neighborFinset v \ visited
  let queue' := queue ++ new_neighbors.toList
  let visited' := visited ∪ new_neighbors
  w ∈ bfs_rec G (v :: queue) visited → w ∈ bfs_rec G queue' visited' := by
  simp_all
  intro h_w
  simp_all [bfs_rec]
