import Proofs.Erdos85BinarySquareRegularParity
import Proofs.Erdos85DefectComponentBlockCommute
import Proofs.Erdos85NegativeDegreeEigenvectorRigidity
import Proofs.Erdos85CommutingShiftedEigenvector

/-! # Joint eigenvalue production from a connected size-two internal factor

This isolates the honest production hypothesis behind the signed-vector
support method.  On a normalized size-two defect component, the internal
ambient graph is 2-regular.  If it is connected and carries a signed
negative-degree vector, that eigenspace is an integral line.  Commutation
therefore forces the induced defect block to act by an integer scalar on the
same vector.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A connected internal size-two factor turns its signed `-2` eigenvector
into a joint integral eigenvector for the induced defect block. -/
theorem binarySquare_regular_sizeTwo_connectedInternal_signed_jointEigenvector
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
    (hc : c.supp.ncard = q * 2)
    (hconn : (G.induce c.supp).Connected)
    (v : c.supp → ℤ) (hvSign : ∀ x, v x = -1 ∨ v x = 1)
    (hvInternal : ∀ x,
      ∑ y ∈ (G.induce c.supp).neighborFinset x, v y = -2 * v x) :
    ∃ mu : ℤ, ∀ x,
      ∑ y ∈ ((secondOrderDefectGraph G).induce c.supp).neighborFinset x, v y =
        mu * v x := by
  let H := G.induce c.supp
  let D := (secondOrderDefectGraph G).induce c.supp
  have hHreg : ∀ x, H.degree x = 2 := by
    intro x
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree hq hreg hcard c (m := 2) hc x
  have hHv : (H.adjMatrix ℤ).mulVec v = (-2 : ℤ) • v := by
    funext x
    rw [SimpleGraph.adjMatrix_mulVec_apply]
    simpa [Pi.smul_apply, smul_eq_mul] using hvInternal x
  have hline : ∀ w : c.supp → ℤ,
      (H.adjMatrix ℤ).mulVec w = (-2 : ℤ) • w →
        ∃ scalar : ℤ, w = scalar • v := by
    intro w hw
    apply negativeDegree_eigenvector_eq_smul_of_signed
      H hconn 2 hHreg v hvSign hvInternal w
    intro x
    have hx := congrFun hw x
    rw [SimpleGraph.adjMatrix_mulVec_apply] at hx
    simpa [Pi.smul_apply, smul_eq_mul] using hx
  have hcommHD : H.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * H.adjMatrix ℤ := by
    exact adjMatrix_comm_secondOrderDefect_induce_component_of_regular
      G hfree hreg c
  obtain ⟨mu, hmu⟩ := commuting_mulVec_eq_smul_of_eigenline
    (D.adjMatrix ℤ) (H.adjMatrix ℤ) hcommHD.symm v (-2) hHv hline
  refine ⟨mu, fun x => ?_⟩
  have hx := congrFun hmu x
  rw [SimpleGraph.adjMatrix_mulVec_apply] at hx
  simpa [Pi.smul_apply, smul_eq_mul] using hx

end


#print axioms
  Erdos85.binarySquare_regular_sizeTwo_connectedInternal_signed_jointEigenvector

end Erdos85
