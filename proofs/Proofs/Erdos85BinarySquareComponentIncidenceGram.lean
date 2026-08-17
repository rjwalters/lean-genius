import Proofs.Erdos85BinarySquareComponentIncidence
import Proofs.Erdos85BinarySquareSizeTwoSelectorGraph

/-!
# Diagonal Gram block of component-neighbor incidence

Together with the already proved cross-component all-ones Gram, this gives the
full block Gram system for defect-component selector coordinates.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The self Gram of one component incidence matrix is `qI` plus the
loopless complement of the induced defect graph. -/
theorem transpose_defectComponentNeighborIncidenceMatrix_mul_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ x, G.degree x = q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    (defectComponentNeighborIncidenceMatrix (K := ℤ) G c).transpose *
      defectComponentNeighborIncidenceMatrix (K := ℤ) G c =
      Matrix.diagonal (fun _ : c.supp => (q : ℤ)) +
        (componentDefectComplementGraph (secondOrderDefectGraph G) c).adjMatrix ℤ := by
  ext x y
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, defectComponentNeighborIncidenceMatrix,
    ite_mul, one_mul, zero_mul]
  have hsum :
      (∑ z : V, if G.Adj z x.1 then if G.Adj z y.1 then (1 : ℤ) else 0 else 0) =
        ((G.neighborFinset x.1 ∩ G.neighborFinset y.1).card : ℤ) := by
    calc
      (∑ z : V, if G.Adj z x.1 then if G.Adj z y.1 then (1 : ℤ) else 0 else 0) =
          ∑ z : V, if G.Adj x.1 z ∧ G.Adj y.1 z then (1 : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro z _hz
        by_cases hzx : G.Adj z x.1 <;> by_cases hzy : G.Adj z y.1 <;>
          simp [hzx, hzy, G.adj_comm]
      _ = ((G.neighborFinset x.1 ∩ G.neighborFinset y.1).card : ℤ) := by
        rw [Finset.sum_boole]
        have hfilt : (Finset.univ : Finset V).filter
            (fun z => G.Adj x.1 z ∧ G.Adj y.1 z) =
            G.neighborFinset x.1 ∩ G.neighborFinset y.1 := by
          ext z
          simp [SimpleGraph.mem_neighborFinset]
        rw [hfilt]
  rw [hsum]
  by_cases hxy : x = y
  · subst y
    rw [Finset.inter_self, G.card_neighborFinset_eq_degree, hreg]
    simp [Matrix.add_apply,
      componentDefectComplementGraph, SimpleGraph.adjMatrix_apply]
  · have hxyval : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
    have hcommon := card_common_eq_if_secondOrderDefect
      G hfree x.1 y.1 hxyval
    by_cases hD : (secondOrderDefectGraph G).Adj x.1 y.1
    · have hmem : y.1 ∈ (secondOrderDefectGraph G).neighborFinset x.1 :=
        ((secondOrderDefectGraph G).mem_neighborFinset x.1 y.1).mpr hD
      rw [if_pos hmem] at hcommon
      rw [hcommon]
      simp [Matrix.add_apply,
        componentDefectComplementGraph,
        SimpleGraph.adjMatrix_apply, hxy, hD]
    · have hnotmem : y.1 ∉ (secondOrderDefectGraph G).neighborFinset x.1 := by
        simpa [SimpleGraph.mem_neighborFinset] using hD
      rw [if_neg hnotmem] at hcommon
      rw [hcommon]
      simp [Matrix.add_apply,
        componentDefectComplementGraph,
        SimpleGraph.adjMatrix_apply, hxy, hD]

/-- In a normalized size-two component, the diagonal Gram block is exactly
`qI + A(L_c)`. -/
theorem binarySquare_regular_sizeTwo_incidenceGram_eq_selector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) :
    (defectComponentNeighborIncidenceMatrix (K := ℤ) G c).transpose *
      defectComponentNeighborIncidenceMatrix (K := ℤ) G c =
      Matrix.diagonal (fun _ : c.supp => (q : ℤ)) +
        (sizeTwoSelectorGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ := by
  rw [transpose_defectComponentNeighborIncidenceMatrix_mul_self G hfree hreg]
  congr 1
  have hgraph :=
    binarySquare_regular_sizeTwoSelectorGraph_eq_componentDefectComplementGraph
      G hfree hq hreg hcard c hc
  ext x y
  have hadj :
      (sizeTwoSelectorGraph G (secondOrderDefectGraph G) c).Adj x y =
        (componentDefectComplementGraph (secondOrderDefectGraph G) c).Adj x y :=
    congrArg (fun H : SimpleGraph c.supp => H.Adj x y) hgraph
  simp only [SimpleGraph.adjMatrix_apply]
  have hadjIff :
      (sizeTwoSelectorGraph G (secondOrderDefectGraph G) c).Adj x y ↔
        (componentDefectComplementGraph (secondOrderDefectGraph G) c).Adj x y :=
    Iff.of_eq hadj
  by_cases hcAdj :
      (componentDefectComplementGraph (secondOrderDefectGraph G) c).Adj x y
  · by_cases hs : (sizeTwoSelectorGraph G (secondOrderDefectGraph G) c).Adj x y
    · simp only [if_pos hcAdj, if_pos hs]
    · exact (hs (hadjIff.mpr hcAdj)).elim
  · by_cases hs : (sizeTwoSelectorGraph G (secondOrderDefectGraph G) c).Adj x y
    · exact (hcAdj (hadjIff.mp hs)).elim
    · simp only [if_neg hcAdj, if_neg hs]

end

end Erdos85
