import Proofs.Erdos85FinalDyadicEmptyBlockCutProfile

/-!
# Defect boundary of an empty-center block

An empty-center neighborhood is independent in the second-order defect graph:
two of its points already share the empty center as a graph neighbor.  The
negative-high cut profile therefore gives an exact shore-boundary mass for
each block.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A point of an empty-center block has no defect neighbor in that block. -/
theorem emptyCenterBlock_defectNeighbor_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {e v : V}
    (hv : v ∈ G.neighborFinset e) :
    Disjoint ((secondOrderDefectGraph G).neighborFinset v)
      (G.neighborFinset e) := by
  rw [Finset.disjoint_left]
  intro x hxD hxB
  have hvxD : (secondOrderDefectGraph G).Adj v x :=
    ((secondOrderDefectGraph G).mem_neighborFinset v x).mp hxD
  have hvxNe : v ≠ x := fun h => by
    subst x
    exact (secondOrderDefectGraph G).loopless.irrefl v hvxD
  have hzero := (secondOrderDefectGraph_adj_iff_card_common_eq_zero
    G hfree hvxNe).mp hvxD
  have heCommon : e ∈ G.neighborFinset v ∩ G.neighborFinset x := by
    exact Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset v e).mpr
        ((G.mem_neighborFinset e v).mp hv).symm,
      (G.mem_neighborFinset x e).mpr
        ((G.mem_neighborFinset e x).mp hxB).symm⟩
  have : (G.neighborFinset v ∩ G.neighborFinset x).Nonempty := ⟨e, heCommon⟩
  exact (Finset.card_ne_zero.mpr this) hzero

/-- Every empty-center block is independent in the second-order defect graph. -/
theorem emptyCenterBlock_defect_independent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {e : V} :
    ∀ v ∈ G.neighborFinset e,
      ((secondOrderDefectGraph G).neighborFinset v ∩
        G.neighborFinset e).card = 0 := by
  intro v hv
  exact Finset.card_eq_zero.mpr
    (Finset.disjoint_iff_inter_eq_empty.mp
      (emptyCenterBlock_defectNeighbor_disjoint G hfree hv))

/-- The total defect incidence from one empty-center block into the shore is
exactly `q * (2^j + r)`. -/
theorem finalDyadic_emptyBlock_defectBoundary_sum_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r c : ℕ} (hq : 8 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j)
    (hsupport : (exceptionalSignedSupport G S q).card = c)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    {e : V} (he : e ∈ emptyLineCenters G S) :
    (∑ v ∈ G.neighborFinset e,
      ((secondOrderDefectGraph G).neighborFinset v ∩ S).card) =
        q * (2 ^ j + r) := by
  calc
    _ = ∑ _v ∈ G.neighborFinset e, (2 ^ j + r) := by
      apply Finset.sum_congr rfl
      intro v hv
      exact finalDyadic_emptyBlock_defectCut_card_eq
        G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
          hsupport hemptyClique he hv
    _ = (G.neighborFinset e).card * (2 ^ j + r) := by simp
    _ = q * (2 ^ j + r) := by
      rw [G.card_neighborFinset_eq_degree, hreg]

end

end Erdos85

#print axioms Erdos85.emptyCenterBlock_defectNeighbor_disjoint
#print axioms Erdos85.emptyCenterBlock_defect_independent
#print axioms Erdos85.finalDyadic_emptyBlock_defectBoundary_sum_eq
