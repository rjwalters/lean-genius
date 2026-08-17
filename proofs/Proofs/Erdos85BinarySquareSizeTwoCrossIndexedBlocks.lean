import Proofs.Erdos85BinarySquareSizeTwoSelfIndexedBlock

/-! # Cross-indexed selector blocks -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Restrict the target-`d` incidence matrix to ambient row labels in `c`. -/
def defectComponentCrossIncidenceMatrix
    {K V : Type*} [Fintype V] [DecidableEq V] [Zero K] [One K]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c d : (secondOrderDefectGraph G).ConnectedComponent) :
    Matrix c.supp d.supp K :=
  fun x y => defectComponentNeighborIncidenceMatrix G d x.1 y

/-- The cross-selector block is the transpose of the reverse block because
all blocks come from the same undirected ambient adjacency matrix. -/
theorem defectComponentCrossIncidenceMatrix_transpose
    {K V : Type*} [Fintype V] [DecidableEq V] [Semiring K]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c d : (secondOrderDefectGraph G).ConnectedComponent) :
    (defectComponentCrossIncidenceMatrix (K := K) G c d).transpose =
      defectComponentCrossIncidenceMatrix (K := K) G d c := by
  ext x y
  by_cases hxy : G.Adj x.1 y.1
  · simp [defectComponentCrossIncidenceMatrix,
      defectComponentNeighborIncidenceMatrix, hxy, hxy.symm]
  · have hyx : ¬G.Adj y.1 x.1 := fun hyx => hxy hyx.symm
    simp [defectComponentCrossIncidenceMatrix,
      defectComponentNeighborIncidenceMatrix, hxy, hyx]

/-- Neighbors of a row point in a target component, retaining the target
subtype. -/
def componentCrossNeighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {c : (secondOrderDefectGraph G).ConnectedComponent}
    (d : (secondOrderDefectGraph G).ConnectedComponent) (x : c.supp) :
    Finset d.supp :=
  Finset.univ.filter fun y => G.Adj x.1 y.1

/-- The subtype-valued cross row has the same cardinality as the canonical
ambient component selector. -/
theorem card_componentCrossNeighborFinset_eq_componentNeighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    {c : (secondOrderDefectGraph G).ConnectedComponent}
    (d : (secondOrderDefectGraph G).ConnectedComponent) (x : c.supp) :
    (componentCrossNeighborFinset G d x).card =
      (componentNeighborFinset G (secondOrderDefectGraph G) d x.1).card := by
  apply Finset.card_bij (fun y _ => y.1)
  · intro y hy
    have hy' := Finset.mem_filter.mp hy
    rw [componentNeighborFinset]
    exact Finset.mem_filter.mpr
      ⟨(G.mem_neighborFinset x.1 y.1).mpr hy'.2,
        (SimpleGraph.ConnectedComponent.mem_supp_iff d y.1).mp y.2⟩
  · intro y₁ h₁ y₂ h₂ hy
    exact Subtype.ext hy
  · intro y hy
    have hy' := Finset.mem_filter.mp hy
    have hySupp : y ∈ d.supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff d y).mpr hy'.2
    refine ⟨⟨y, hySupp⟩, ?_, rfl⟩
    rw [componentCrossNeighborFinset, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (G.mem_neighborFinset x.1 y).mp hy'.1⟩

/-- Between two normalized size-two coordinates, every row and every column
of the cross-indexed incidence block has exactly two ones.  Together with
transpose symmetry, the off-diagonal block is a 2-regular bipartite cycle
system. -/
theorem binarySquare_regular_twoSizeTwoParts_crossIndexedBlock_package
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c d : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (hd : d.supp.ncard = q * 2) :
    (defectComponentCrossIncidenceMatrix (K := ℤ) G c d).transpose =
        defectComponentCrossIncidenceMatrix (K := ℤ) G d c ∧
      (∀ x : c.supp, (componentCrossNeighborFinset G d x).card = 2) ∧
      (∀ y : d.supp, (componentCrossNeighborFinset G c y).card = 2) := by
  refine ⟨defectComponentCrossIncidenceMatrix_transpose G c d, ?_, ?_⟩
  · intro x
    rw [card_componentCrossNeighborFinset_eq_componentNeighborFinset]
    exact binarySquare_regular_sizeTwoPart_selector_card
      G hfree hq hreg hcard d hd x.1
  · intro y
    rw [card_componentCrossNeighborFinset_eq_componentNeighborFinset]
    exact binarySquare_regular_sizeTwoPart_selector_card
      G hfree hq hreg hcard c hc y.1

end

end Erdos85
