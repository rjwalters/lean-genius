import Proofs.Erdos85FinalDyadicEmptyNeighborhoodPartition

/-!
# Empty-center blocks and their defect-cut profile

The saturated negative-high class is a literal disjoint union of the graph
neighborhoods of the empty centers.  Every point of every block has the
negative-high defect-cut degree.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Distinct empty centers have disjoint graph neighborhoods. -/
theorem finalDyadic_emptyCenter_neighborFinset_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (S : Finset V)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    {e f : V} (he : e ∈ emptyLineCenters G S)
    (hf : f ∈ emptyLineCenters G S) (hef : e ≠ f) :
    Disjoint (G.neighborFinset e) (G.neighborFinset f) := by
  rw [Finset.disjoint_iff_inter_eq_empty]
  apply Finset.card_eq_zero.mp
  exact (secondOrderDefectGraph_adj_iff_card_common_eq_zero
    G hfree hef).mp (hemptyClique he hf hef)

/-- Every negative-high vertex has a unique empty-center owner. -/
theorem finalDyadic_negativeHigh_existsUnique_empty_owner
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r : ℕ} (hq : 8 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j)
    {v : V} (hv : v ∈ finalDyadicNegativeHighCutCenters G S j r) :
    ∃! e, e ∈ emptyLineCenters G S ∧ v ∈ G.neighborFinset e := by
  have hone := finalDyadic_negativeHigh_exact_empty_neighbor
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf v hv
  have hnonempty :
      (G.neighborFinset v ∩ emptyLineCenters G S).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨e, he⟩ := hnonempty
  have heData := Finset.mem_inter.mp he
  refine ⟨e, ⟨heData.2, ?_⟩, ?_⟩
  · exact (G.mem_neighborFinset e v).mpr
      ((G.mem_neighborFinset v e).mp heData.1).symm
  · intro f hfData
    have hf : f ∈ G.neighborFinset v ∩ emptyLineCenters G S :=
      Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset v f).mpr
          ((G.mem_neighborFinset f v).mp hfData.2).symm,
        hfData.1⟩
    have hsingle : G.neighborFinset v ∩ emptyLineCenters G S = {e} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      exact ⟨he, fun x hx => by
        have hcardOne : (G.neighborFinset v ∩ emptyLineCenters G S).card = 1 := hone
        obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcardOne
        have hxa : x = a := Finset.mem_singleton.mp (ha ▸ hx)
        have hea : e = a := Finset.mem_singleton.mp (ha ▸ he)
        exact hxa.trans hea.symm⟩
    have : f ∈ ({e} : Finset V) := by simpa [hsingle] using hf
    exact Finset.mem_singleton.mp this

/-- A point in an empty-center block has exactly the negative-high defect-cut
degree into the shore. -/
theorem finalDyadic_emptyBlock_defectCut_card_eq
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
    {e v : V} (he : e ∈ emptyLineCenters G S)
    (hv : v ∈ G.neighborFinset e) :
    ((secondOrderDefectGraph G).neighborFinset v ∩ S).card = 2 ^ j + r := by
  have hvM := finalDyadic_emptyCenter_neighborFinset_subset_negativeHigh
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
      hsupport hemptyClique he hv
  exact (Finset.mem_filter.mp hvM).2

end

end Erdos85

#print axioms Erdos85.finalDyadic_emptyCenter_neighborFinset_disjoint
#print axioms Erdos85.finalDyadic_negativeHigh_existsUnique_empty_owner
#print axioms Erdos85.finalDyadic_emptyBlock_defectCut_card_eq
