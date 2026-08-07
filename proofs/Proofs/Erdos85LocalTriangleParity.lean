import Proofs.Erdos85BranchDeficitSymmetry

/-!
# Local triangle matching parity without regularity

In a `C₄`-free graph the graph induced on any open neighborhood has maximum
degree one.  Its nonisolated vertices are exactly the incident edges that lie
in triangles, while the remaining neighbors are `triangleFreeNeighbors`.
This gives the local identity

`TF(x) + 2 * |E(G[N(x)])| = degree(x)`

without a global regularity hypothesis.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Triangle-free neighbors plus the local induced degree sum partition the
open neighborhood of a vertex. -/
theorem card_triangleFreeNeighbors_add_localDegreeSum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (x : V) :
    (triangleFreeNeighbors G x).card +
      (∑ y : {z : V // z ∈ G.neighborSet x},
        (G.induce (G.neighborSet x)).degree y) = G.degree x := by
  classical
  let H := G.induce (G.neighborSet x)
  let N := {z : V // z ∈ G.neighborSet x}
  have hle : ∀ y : N, H.degree y ≤ 1 := by
    intro y
    change (G.induce (G.neighborSet x)).degree y ≤ 1
    rw [degree_induce_neighborSet_eq_card_common]
    exact common_le_one_of_not_containsC4 hfree x y.1 (G.ne_of_adj y.2)
  have hNcard : Fintype.card N = G.degree x := by
    rw [Fintype.card_subtype]
    have heq : Finset.univ.filter (fun z => z ∈ G.neighborSet x) =
        G.neighborFinset x := by ext z; simp
    rw [heq, G.card_neighborFinset_eq_degree]
  have hsumNonzero : (∑ y : N, H.degree y) =
      (Finset.univ.filter fun y : N => H.degree y ≠ 0).card := by
    calc
      (∑ y : N, H.degree y) =
          ∑ y : N, if H.degree y ≠ 0 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro y _
        have hy := hle y
        by_cases hzero : H.degree y = 0 <;> simp [hzero] <;> omega
      _ = _ := by
        simpa using (Finset.sum_boole (R := ℕ)
          (fun y : N => H.degree y ≠ 0) Finset.univ)
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset N)) (p := fun y => H.degree y = 0)
  have hnot : (Finset.univ.filter fun y : N => ¬H.degree y = 0) =
      Finset.univ.filter fun y : N => H.degree y ≠ 0 := by
    ext y
    simp
  rw [hnot, Finset.card_univ, hNcard, ← hsumNonzero] at hpartition
  have hisolated :
      (Finset.univ.filter fun y : N => H.degree y = 0).card =
        (triangleFreeNeighbors G x).card := by
    apply Finset.card_bij (fun y _ => y.1)
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      apply (mem_triangleFreeNeighbors G x y.1).mpr
      refine ⟨y.2, ?_⟩
      rw [← degree_induce_neighborSet_eq_card_common]
      exact hy
    · intro a ha b hb hab
      exact Subtype.ext hab
    · intro y hy
      have hyData := (mem_triangleFreeNeighbors G x y).mp hy
      let Y : N := ⟨y, hyData.1⟩
      refine ⟨Y, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [degree_induce_neighborSet_eq_card_common]
      exact hyData.2
  rw [← hisolated]
  exact hpartition

/-- Exact local triangle-edge identity. -/
theorem card_triangleFreeNeighbors_add_two_mul_localEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (x : V) :
    (triangleFreeNeighbors G x).card +
      2 * (G.induce (G.neighborSet x)).edgeFinset.card = G.degree x := by
  have hlocal := card_triangleFreeNeighbors_add_localDegreeSum G hfree x
  have hhand := (G.induce (G.neighborSet x)).sum_degrees_eq_twice_card_edges
  rw [hhand] at hlocal
  exact hlocal

/-- The triangle-free incident-edge count has the same parity as the actual
degree, with no regularity assumption. -/
theorem triangleFreeNeighbors_card_mod_two_eq_vertexDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (x : V) :
    (triangleFreeNeighbors G x).card % 2 = G.degree x % 2 := by
  have h := card_triangleFreeNeighbors_add_two_mul_localEdges G hfree x
  omega

/-- Every odd-degree vertex has a triangle-free incident edge. -/
theorem triangleFreeNeighbors_nonempty_of_odd_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {x : V} (hodd : Odd (G.degree x)) :
    (triangleFreeNeighbors G x).Nonempty := by
  rw [← Finset.card_pos]
  have hmod := triangleFreeNeighbors_card_mod_two_eq_vertexDegree G hfree x
  apply Nat.pos_of_ne_zero
  intro hzero
  rw [hzero] at hmod
  exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_iff.mpr (by omega))

/-- At a degree-seven vertex there are at most three local triangle edges,
and at least one incident edge is triangle-free. -/
theorem localTriangleEdges_le_three_of_degree_seven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {x : V} (hx : G.degree x = 7) :
    (G.induce (G.neighborSet x)).edgeFinset.card ≤ 3 ∧
      (triangleFreeNeighbors G x).Nonempty := by
  have hid := card_triangleFreeNeighbors_add_two_mul_localEdges G hfree x
  have hnonempty := triangleFreeNeighbors_nonempty_of_odd_degree
    G hfree (x := x) (by rw [hx]; norm_num)
  rw [hx] at hid
  constructor
  · have hpos := Finset.card_pos.mpr hnonempty
    omega
  · exact hnonempty

end

end Erdos85
