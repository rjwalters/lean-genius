import Proofs.Erdos85BinarySquareComponentIncidence
import Proofs.Erdos85BinarySquareSizeTwoStarPerfectMatching

/-! # The self-indexed diagonal selector block -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Restrict the ambient/component incidence matrix to rows whose labels lie
inside the same defect component. -/
def defectComponentSelfIncidenceMatrix
    {K V : Type*} [Fintype V] [DecidableEq V] [Zero K] [One K]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    Matrix c.supp c.supp K :=
  fun x y => defectComponentNeighborIncidenceMatrix G c x.1 y

/-- **Self-indexed block identity.**  The diagonal block of component
incidence is exactly adjacency of the ambient graph induced on that component.
This is the datum that an abstract ODC does not remember. -/
theorem defectComponentSelfIncidenceMatrix_eq_induced_adjMatrix
    {K V : Type*} [Fintype V] [DecidableEq V] [Semiring K]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    defectComponentSelfIncidenceMatrix (K := K) G c =
      (G.induce c.supp).adjMatrix K := by
  ext x y
  simp only [defectComponentSelfIncidenceMatrix,
    defectComponentNeighborIncidenceMatrix, SimpleGraph.adjMatrix_apply]
  rfl

/-- Membership form: the selector of an internal label consists exactly of
its neighbors in the induced ambient block. -/
theorem mem_componentNeighborFinset_internal_iff_induced_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent) (x y : c.supp) :
    y.1 ∈ componentNeighborFinset G (secondOrderDefectGraph G) c x.1 ↔
      (G.induce c.supp).Adj x y := by
  simp only [componentNeighborFinset, Finset.mem_filter,
    SimpleGraph.mem_neighborFinset, SimpleGraph.induce_adj]
  have hyc : (secondOrderDefectGraph G).connectedComponentMk y.1 = c :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff c y.1).mp y.2
  simp [hyc]

/-- In a normalized size-two component the self-indexed incidence/adjacency
block is a 2-regular graph, hence its distinguished internal labels form the
cycle 2-factor required by the selector-cube model. -/
theorem binarySquare_regular_sizeTwoPart_selfIndexedBlock_package
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
    defectComponentSelfIncidenceMatrix (K := ℤ) G c =
        (G.induce c.supp).adjMatrix ℤ ∧
      ∀ x : c.supp, (G.induce c.supp).degree x = 2 := by
  refine ⟨defectComponentSelfIncidenceMatrix_eq_induced_adjMatrix G c, ?_⟩
  intro x
  exact binarySquare_regular_degree_induce_defectComponent_eq_part
    G hfree hq hreg hcard c hc x

end

end Erdos85
