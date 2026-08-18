import Proofs.Erdos85BinarySquareComponentToAllOwnerSpectrum

/-!
# Transfer component adjacency spectra to all owner colors

At square order every induced defect component is `(q - 1)`-regular, so an
adjacency eigenvalue `μ` gives the Laplacian eigenvalue `q - 1 - μ`.  Composing
this elementary conversion with the centered-incidence transfer gives the
simultaneous spectrum of all component-owner graphs.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- On a square-order defect component, adjacency eigenvalue `μ` converts to
Laplacian eigenvalue `q - 1 - μ`. -/
theorem binarySquare_component_lapMatrix_eigenvector_of_adjMatrix_eigenvector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (v : c.supp → ℝ) (μ : ℝ)
    (hv : (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℝ).mulVec v =
      μ • v) :
    (((secondOrderDefectGraph G).induce c.supp).lapMatrix ℝ).mulVec v =
      (((q - 1 : ℕ) : ℝ) - μ) • v := by
  let H := (secondOrderDefectGraph G).induce c.supp
  ext x
  rw [H.lapMatrix_mulVec_apply]
  have hxdeg : H.degree x = q - 1 := by
    simpa [H] using binarySquare_regular_inducedDefectComponent_degree
      G hfree hq hreg hcard c x
  have hvx := congrFun hv x
  change (H.adjMatrix ℝ).mulVec v x = μ * v x at hvx
  rw [H.adjMatrix_mulVec_apply] at hvx
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hxdeg]
  rw [hvx]
  ring

/-- A nonzero adjacency eigenvector of one defect component transfers to a
simultaneous eigenvector of every owner graph.  Its own color has eigenvalue
`q - 1 - μ - m c`; every other color acts by its bottom eigenvalue `-m d`. -/
theorem componentAdjacency_eigenvector_to_all_componentOwnerGraphs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = q * m c)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (v : c.supp → ℝ) (μ : ℝ)
    (hv : (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℝ).mulVec v =
      μ • v) (hv0 : v ≠ 0)
    (hμ : (((q - 1 : ℕ) : ℝ) - μ) ≠ 0) :
    let w := (realCenteredDefectComponentNeighborIncidenceMatrix G q c).mulVec v
    w ≠ 0 ∧
      ((componentOwnerGraph G
        (secondOrderDefectGraph G) c).adjMatrix ℝ).mulVec w =
          (((q - 1 : ℕ) : ℝ) - μ - m c) • w ∧
      ∀ d : (secondOrderDefectGraph G).ConnectedComponent, d ≠ c →
        ((componentOwnerGraph G
          (secondOrderDefectGraph G) d).adjMatrix ℝ).mulVec w =
            (-(m d : ℝ)) • w := by
  have hL := binarySquare_component_lapMatrix_eigenvector_of_adjMatrix_eigenvector
    G hfree hq hreg hcard c v μ hv
  exact componentLaplacian_eigenvector_to_all_componentOwnerGraphs
    G hfree hq hreg hcard m hm c v (((q - 1 : ℕ) : ℝ) - μ) hL hv0 hμ

end

end Erdos85
