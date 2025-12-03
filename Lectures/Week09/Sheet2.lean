import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Combinatorics.SimpleGraph.Metric

structure FinSimpleGraph (V : Type u) [Fintype V] [DecidableEq V]  extends SimpleGraph V

noncomputable
instance  fintypeFinSimpleGraph {V : Type u} [Fintype V] [DecidableEq V] (G : FinSimpleGraph V) (v : V): Fintype (G.neighborSet v) :=  Fintype.ofFinite ↑(G.neighborSet v)

open Finset SimpleGraph

variable  {V : Type*} [Fintype V] [DecidableEq V]

<<<<<<< HEAD
<<<<<<< HEAD
=======
#check Finset

>>>>>>> official_repo/main
=======
#check Finset

>>>>>>> official_repo/main
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
<<<<<<< HEAD
<<<<<<< HEAD

 noncomputable def bfs
=======
=======
>>>>>>> official_repo/main
    termination_by (Fintype.card V - #visited + queue.length) decreasing_by sorry

-- We leave the termination proof as an exercise

#check bfs_rec.induct

noncomputable def bfs
<<<<<<< HEAD
>>>>>>> official_repo/main
=======
>>>>>>> official_repo/main
  (G : FinSimpleGraph V)
  (s : V)
  : Finset V :=
  bfs_rec G {s} {s}

lemma bfs_result_reachable (v : V) : v ∈ bfs G s → G.Reachable s v := by
  intro h_v_in_bfs
  unfold bfs at h_v_in_bfs
  apply bfs_rec_preserves_reachable_and_invariants s [s] {s} ; all_goals (aesop)

  where  bfs_rec_preserves_reachable_and_invariants
  (s_orig : V)
  -- Arguments for the current call to bfs_rec:
  (queue : List V)
  (visited : Finset V)
  -- Preconditions (Inductive Invariants) for *this specific call*:
  (h_visited_is_reachable : ∀ x ∈ visited, G.Reachable s_orig x)
  (h_queue_nodes_in_visited : ∀ x ∈ queue, x ∈ visited)
  -- Conclusion: All nodes in the list returned by this call to bfs_rec are reachable.
  : ∀ x ∈ (bfs_rec G queue visited), G.Reachable s_orig x :=  by {
  match hq_cases : queue with
<<<<<<< HEAD
<<<<<<< HEAD
  | [] => sorry
=======
  | [] =>
    simp only [bfs_rec]
    assumption
>>>>>>> official_repo/main
=======
  | [] =>
    simp only [bfs_rec]
    assumption
>>>>>>> official_repo/main

  | v :: qt => -- Inductive step of bfs_rec (queue = v :: qt)
    unfold bfs_rec
    dsimp only [union_sdiff_self_eq_union, List.concat_eq_append]

    let new_neighbors := G.neighborFinset v \ visited
    let queue' := qt ++ new_neighbors.toList
    let visited' := visited ∪ new_neighbors

    apply bfs_rec_preserves_reachable_and_invariants
    · show ∀ x ∈ visited', G.Reachable s_orig x
<<<<<<< HEAD
<<<<<<< HEAD
      have new_neighbors_are_reachable : ∀ nn ∈ new_neighbors, G.Reachable s_orig nn := by
        -- Exercise -- fill this proof
        sorry
      intro x hx_mem_visited'
      rw [Finset.mem_union] at hx_mem_visited'
      aesop
    · sorry
  }
=======
=======
>>>>>>> official_repo/main
      -- Exercise to fill in this proof.
      have new_neighbors_are_reachable : ∀ nn ∈ new_neighbors, G.Reachable s_orig nn := sorry
      intro x hx_mem_visited'
      rw [Finset.mem_union] at hx_mem_visited'
      aesop
    · -- Exercise
      sorry
  }
  termination_by (Fintype.card V - #visited, queue.length) decreasing_by sorry

-- # Exercise: Prove the same statement using functional induction
<<<<<<< HEAD
>>>>>>> official_repo/main
=======
>>>>>>> official_repo/main

-- the termination proof is the same
#check connected_iff_exists_forall_reachable

<<<<<<< HEAD
<<<<<<< HEAD
-- Exercise.
theorem spanning_imp_connected (G : FinSimpleGraph V)(s : V): #(bfs G s) = Fintype.card V → G.Connected := by
=======
theorem spanning_imp_connected (G : FinSimpleGraph V)(s : V): #(bfs G s) = Fintype.card V → G.Connected := by
  -- Direction 1: (bfs G s).length = n → G.Connected
>>>>>>> official_repo/main
=======
theorem spanning_imp_connected (G : FinSimpleGraph V)(s : V): #(bfs G s) = Fintype.card V → G.Connected := by
  -- Direction 1: (bfs G s).length = n → G.Connected
>>>>>>> official_repo/main
  intro h_bfs_len_eq_n
  -- If length is n and no duplicates, then the set of elements has cardinality n.
  observe h_bfs_covers_all_nodes : (bfs G s) = Finset.univ
  -- Now, prove G is connected.
<<<<<<< HEAD
<<<<<<< HEAD
=======
  -- G is connected if all pairs of nodes are reachable from each other.
  -- We'll show all nodes are reachable from `s`.
>>>>>>> official_repo/main
=======
  -- G is connected if all pairs of nodes are reachable from each other.
  -- We'll show all nodes are reachable from `s`.
>>>>>>> official_repo/main
  sorry
