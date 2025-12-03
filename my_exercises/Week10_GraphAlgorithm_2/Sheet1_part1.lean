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

/- We will use the following notion of graph distance -/
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Metric.html#SimpleGraph.dist

-- The extended distance between two vertices is the length of the shortest walk between them. It is ⊤ if no such walk exists.
#check SimpleGraph.edist
#print SimpleGraph.edist

/- # Assume available, proof in part2
- Lemma 1 : s ∈ bfs G s
-/
lemma lemma_1_s_in_bfs_s {s} {G : FinSimpleGraph V} : s ∈ bfs G s := by sorry

/- # Assume available, proof in part3
- Lemma 2 : u ∈ bfs G s ∧ v ∈ G.neighborFinset u → v ∈ bfs G s
-/
lemma lemma2_u_bfs_so_are_neighbors (G : FinSimpleGraph V) (s u v) :
  u ∈ bfs G s ∧ v ∈ G.neighborSet u → v ∈ bfs G s := sorry

/-- A helper lemma for you to use-/
theorem edist_le_of_reachable {G : FinSimpleGraph (V)} {s : V} (v : V) (h_neq : ¬s = v)(h: G.Reachable s v) :
  let n := Fintype.card V
  G.edist s v ≤ n -1  := by
  have d0: G.edist s v < ⊤ := by
    by_contra!
    rw [@top_le_iff] at this
    rw [← @edist_ne_top_iff_reachable] at h
    contradiction
  have d1: G.dist s v ≠ 0:= by
    by_contra!
    rw [propext (Reachable.dist_eq_zero_iff h)] at this
    subst this
    exact h_neq rfl

  apply Reachable.exists_path_of_dist at h
  obtain ⟨p,hp1,hp2⟩ := h
  apply Walk.IsPath.length_lt at hp1
  intro n
  observe: p.length ≤ n-1
  have: G.dist s v = G.edist s v := Eq.symm ((fun {m} {n} hn ↦ (ENat.toNat_eq_iff hn).mp) d1 rfl)
  rw [← this]
  norm_cast
  aesop

-- Exercise
theorem exists_eq_cons_of_ne'.{u} {V : Type u} {G : SimpleGraph V} {u v : V} (hne : u ≠ v) :
  ∀ (p : G.Walk u v), ∃ (w : V) (p' : G.Walk u w) (h : G.Adj w v) , p =  p'.concat h := by
  sorry

/-- A helper lemma for you to use-/
theorem exists_edist_le_and_of_edist_eq {G : FinSimpleGraph (V)} {s : V} (k : ℕ) (v : V)
  (h : G.edist s v = ↑(k + 1)) : ∃ w, G.edist s w ≤ ↑k ∧ G.Adj w v := by
  have sneqv: s ≠ v := by
    by_contra!
    subst this
    simp at h
    absurd h
    exact ne_of_beq_false rfl
  apply exists_walk_of_edist_eq_coe at h
  obtain ⟨p,hp⟩ := h
  apply exists_eq_cons_of_ne' at sneqv
  specialize sneqv p
  obtain ⟨w,p',h1,hp2⟩ := sneqv
  use w
  refine ⟨?_,h1⟩
  have lp': p'.length = p.length -1 := by
    subst hp2
    simp_all only [ne_eq, Walk.length_concat, Nat.add_right_cancel_iff, add_tsub_cancel_right]
  calc
    G.edist s w ≤ p'.length  := Walk.edist_le p'
    _ = p.length -1  := by exact congrArg Nat.cast lp'
    _ = k := by norm_cast; omega


/--
Lemma 3: If a node `v` is reachable from `s`, then `v` will be in the list returned by `bfs G s`.
(This implies BFS is complete for the connected component of `s`).
-/
lemma bfs_visits_all_reachable (v : V) : G.Reachable s v → v ∈ bfs G s := by
  if h:s = v then
    subst h
    intro h
    unfold bfs
    apply lemma_1_s_in_bfs_s
  else
    intro h'
    let n := Fintype.card V
    have: G.edist s v ≤ n-1 := edist_le_of_reachable v h h'
    apply bfs_dist_k_reachable (n-1) v this

-- Translate the informal proof into Lean proof
  where bfs_dist_k_reachable (k :ℕ) (v : V): G.edist s v ≤ k → v ∈ bfs G s := by
  {
    simp [bfs]
    induction' k with k ih generalizing v
    · intro h
      simp_all only [CharP.cast_eq_zero, nonpos_iff_eq_zero, edist_eq_zero_iff]
      apply lemma_1_s_in_bfs_s
    · intro h

      -- # Lecture approach
      obtain h | h : G.edist s v < ↑(k+1) ∨ G.edist s v = ↑(k+1) := Decidable.lt_or_eq_of_le h
      all_goals expose_names
      · apply ih
        simp_all
        exact ENat.lt_coe_add_one_iff.mp h
      · apply exists_edist_le_and_of_edist_eq at h
        obtain ⟨ w, hd ⟩ := h
        have h_neighbor : v ∈ G.neighborSet w := by simp_all
        have h_w : w ∈ bfs G s := by simp_all [bfs]
        rw [← bfs] -- optional, `apply` automatically handles this step
        apply lemma2_u_bfs_so_are_neighbors G s w v
        simp_all
        -- constructor
        -- · exact h_w
        -- · exact h_neighbor

      -- # My approach
      -- by_cases h: G.edist s v < ↑(k + 1)
      -- all_goals expose_names
      -- · apply ih
      --   simp_all
      --   exact ENat.lt_coe_add_one_iff.mp h
      -- · apply Decidable.lt_or_eq_of_le at h_1
      --   replace h : G.edist s v = ↑(k + 1) := by grind
      --   apply exists_edist_le_and_of_edist_eq at h
      --   obtain ⟨ w, hd ⟩ := h
      --   have h_neighbor : v ∈ G.neighborSet w := by simp_all
      --   have h_w : w ∈ bfs G s := by simp_all [bfs]
      --   apply lemma2_u_bfs_so_are_neighbors G s w v
      --   simp_all
  }

-- Exercise: Show that BFS solves the connectivity problem

#check connected_iff_exists_forall_reachable
#check reachable_comm
#check Reachable.trans


/-
****************************************************************************************************
# From Week09.Sheet2 begin
****************************************************************************************************
-/
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
  | [] =>
    simp only [bfs_rec]
    assumption

  | v :: qt => -- Inductive step of bfs_rec (queue = v :: qt)
    unfold bfs_rec
    dsimp only [union_sdiff_self_eq_union, List.concat_eq_append]

    let new_neighbors := G.neighborFinset v \ visited
    let queue' := qt ++ new_neighbors.toList
    let visited' := visited ∪ new_neighbors

    apply bfs_rec_preserves_reachable_and_invariants
    · show ∀ x ∈ visited', G.Reachable s_orig x
      have new_neighbors_are_reachable : ∀ nn ∈ new_neighbors, G.Reachable s_orig nn := by

        intro nn hnn_mem_new_neighbors
        rcases Finset.mem_sdiff.mp hnn_mem_new_neighbors with ⟨h_nn_is_neighbor_of_v, _⟩
        rw [SimpleGraph.mem_neighborFinset] at h_nn_is_neighbor_of_v
        have sv:  G.Reachable s_orig v := by exact h_visited_is_reachable v (h_queue_nodes_in_visited v (List.Mem.head qt))
        have vnn: G.Reachable v nn := by exact Adj.reachable h_nn_is_neighbor_of_v
        exact Reachable.trans sv vnn

      intro x hx_mem_visited'
      rw [Finset.mem_union] at hx_mem_visited'
      aesop
    · aesop
  }
  termination_by (Fintype.card V - #visited, queue.length)
  -- Week09.HW08.Problem1
  decreasing_by sorry

theorem spanning_imp_connected (G : FinSimpleGraph V)(s : V): #(bfs G s) = Fintype.card V → G.Connected := by
  -- Direction 1: (bfs G s).length = n → G.Connected
  intro h_bfs_len_eq_n
  -- If length is n and no duplicates, then the set of elements has cardinality n.
  observe h_bfs_covers_all_nodes : (bfs G s) = Finset.univ
  -- Now, prove G is connected.
  -- G is connected if all pairs of nodes are reachable from each other.
  -- We'll show all nodes are reachable from `s`.
  rw [@connected_iff_exists_forall_reachable]
  use s
  intro u
  apply bfs_result_reachable
  rw [h_bfs_covers_all_nodes]
  exact mem_univ u
/-
****************************************************************************************************
# From Week09.Sheet2 end
****************************************************************************************************
-/

theorem spanning_iff_connected (G : FinSimpleGraph V)(s : V): #(bfs G s) = Fintype.card V ↔ G.Connected := by
  constructor
  · -- Done in the previous week; no need to prove this here
    apply spanning_imp_connected
  · -- Direction 2: G.Connected → (bfs G s).length = n
    intro h_connected

    -- If G is connected, every node is reachable from s.
    have s_reaches_all_nodes : ∀ (v : V), G.Reachable s v := by
      rw [@connected_iff_exists_forall_reachable] at h_connected
      obtain ⟨u,hu⟩ := h_connected
      have us:= hu s
      intro v
      have uv:= hu v
      rw [@reachable_comm] at us
      exact Reachable.trans us (hu v)
    -- By Lemma 3, BFS visits all reachable nodes.
    have all_nodes_in_bfs_list : ∀ (v : V), v ∈ bfs G s := by
      intro v_node
      exact bfs_visits_all_reachable v_node (s_reaches_all_nodes v_node)
    -- If all n nodes are in the list and the list has no duplicates, its length is n.
    -- This means the finset corresponding to the list is Finset.univ.
    have bfs_finset_eq_univ : (bfs G s) = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro x -- x : Fin n
      exact all_nodes_in_bfs_list x

    -- The length of a nodup list is the cardinality of its finset.
    simp at bfs_finset_eq_univ
    rw [bfs_finset_eq_univ]
    simp only [card_univ]
