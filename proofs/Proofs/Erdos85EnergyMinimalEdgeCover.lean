import Proofs.Erdos85EdgeSlideMinimizerExistence
import Proofs.Erdos85MinimalWitness

/-!
# Energy-minimal witnesses are edge covered by tight vertices

Deleting an edge strictly lowers the sum of squared degrees.  Consequently,
a degree-square minimizer subject to a minimum-degree floor cannot contain an
edge whose two endpoints both lie strictly above that floor.
-/

open SimpleGraph

namespace Erdos85

theorem deleteEdge_neighborFinset_left
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    (G.deleteEdges {s(u,v)}).neighborFinset u =
      (G.neighborFinset u).erase v := by
  ext w
  simp [SimpleGraph.deleteEdges_adj, Sym2.eq_iff] <;> aesop

theorem degree_deleteEdge_left
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V)
    (huv : G.Adj u v) :
    (G.deleteEdges {s(u,v)}).degree u = G.degree u - 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree,
    deleteEdge_neighborFinset_left G u v, Finset.card_erase_of_mem]
  exact (G.mem_neighborFinset u v).mpr huv

/-- Deleting an edge strictly decreases degree-square energy. -/
theorem degreeSquareEnergy_deleteEdge_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V)
    (huv : G.Adj u v) :
    degreeSquareEnergy (G.deleteEdges {s(u,v)}) < degreeSquareEnergy G := by
  have hdeg_le : ∀ w : V,
      (G.deleteEdges {s(u,v)}).degree w ≤ G.degree w := by
    intro w
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro z hz
    exact (G.mem_neighborFinset w z).mpr
      (G.deleteEdges_le _ ((G.deleteEdges {s(u,v)}).mem_neighborFinset w z |>.mp hz))
  have hsquare_le : ∀ w ∈ (Finset.univ : Finset V),
      (G.deleteEdges {s(u,v)}).degree w *
          (G.deleteEdges {s(u,v)}).degree w ≤
        G.degree w * G.degree w := by
    intro w _
    exact Nat.mul_le_mul (hdeg_le w) (hdeg_le w)
  have hupos : 0 < G.degree u :=
    Finset.card_pos.mpr ⟨v, (G.mem_neighborFinset u v).mpr huv⟩
  have hstrict :
      (G.deleteEdges {s(u,v)}).degree u *
          (G.deleteEdges {s(u,v)}).degree u <
        G.degree u * G.degree u := by
    rw [degree_deleteEdge_left G u v huv]
    have hsub : G.degree u - 1 + 1 = G.degree u := by omega
    nlinarith
  have hsum := Finset.sum_lt_sum hsquare_le
    ⟨u, Finset.mem_univ u, hstrict⟩
  simpa only [degreeSquareEnergy] using hsum

/-- Every edge of an energy-minimal witness meets the degree-`d` layer. -/
theorem degreeSquareMinimizer_tightEdgeCover
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hfree : ¬ containsC4 V G) (hmin : d ≤ G.minDegree)
    (hminimal : IsDegreeSquareMinimizer G d) :
    ∀ ⦃u v⦄, G.Adj u v → G.degree u = d ∨ G.degree v = d := by
  intro u v huv
  by_contra htight
  push Not at htight
  have huMin : d ≤ G.degree u := hmin.trans (G.minDegree_le_degree u)
  have hvMin : d ≤ G.degree v := hmin.trans (G.minDegree_le_degree v)
  have hu : d < G.degree u := lt_of_le_of_ne huMin (Ne.symm htight.1)
  have hv : d < G.degree v := lt_of_le_of_ne hvMin (Ne.symm htight.2)
  have hHfree : ¬ containsC4 V (G.deleteEdges {s(u,v)}) :=
    fun hc4 ↦ hfree (containsC4_mono (G.deleteEdges_le _) hc4)
  have hHmin : d ≤ (G.deleteEdges {s(u,v)}).minDegree :=
    le_minDegree_deleteEdge_of_lt_degrees G u v hmin hu hv
  have hle : degreeSquareEnergy G ≤
      degreeSquareEnergy (G.deleteEdges {s(u,v)}) :=
    hminimal (G.deleteEdges {s(u,v)}) hHfree hHmin
  have hlt : degreeSquareEnergy (G.deleteEdges {s(u,v)}) <
      degreeSquareEnergy G := degreeSquareEnergy_deleteEdge_lt G u v huv
  omega

/-- A witness can simultaneously be chosen energy-minimal, edge-covered by
tight vertices, and saturated against every admissible deleted-edge slide. -/
theorem exists_degreeSquareMinimizer_with_tightCover_and_slideSaturation
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G₀ : SimpleGraph V) [DecidableRel G₀.Adj] {d : ℕ}
    (hfree₀ : ¬ containsC4 V G₀) (hmin₀ : d ≤ G₀.minDegree) :
    ∃ (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      ¬ containsC4 V G ∧ d ≤ G.minDegree ∧
      IsDegreeSquareMinimizer G d ∧
      (∀ ⦃u v⦄, G.Adj u v →
        G.degree u = d ∨ G.degree v = d) ∧
      ∀ x y z : V, y ≠ z → G.Adj x z → ¬ G.Adj y z →
        G.degree y + 1 < G.degree x →
          HasThreeEdgeWalk (G.deleteEdges {s(x,z)}) y z := by
  obtain ⟨G, hdec, hfree, hmin, hminimal⟩ :=
    exists_degreeSquareMinimizer G₀ hfree₀ hmin₀
  refine ⟨G, hdec, hfree, hmin, hminimal,
    degreeSquareMinimizer_tightEdgeCover G hfree hmin hminimal, ?_⟩
  intro x y z hyz hxz hnot hgap
  exact hasThreeEdgeWalk_deleteEdge_of_degreeSquareMinimizer
    G hfree hmin hminimal x y z hyz hxz hnot hgap

end Erdos85
