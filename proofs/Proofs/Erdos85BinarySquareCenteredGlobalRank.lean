import Proofs.Erdos85BinarySquareCenteredComponentRank
import Proofs.Erdos85ResidueSignedCount

/-!
# Global centered-component dimension ledger

The real centered incidence blocks retain the integral cross orthogonality.
Their exact ranks therefore have a fixed global sum: all `q²` defect vertices,
minus one constant direction for each defect component.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Distinct real centered component-incidence blocks have zero cross Gram. -/
theorem transpose_realCenteredDefectComponentNeighborIncidenceMatrix_mul_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c d : (secondOrderDefectGraph G).ConnectedComponent) (hcd : c ≠ d) :
    (realCenteredDefectComponentNeighborIncidenceMatrix G q c).transpose *
        realCenteredDefectComponentNeighborIncidenceMatrix G q d = 0 := by
  have hz :=
    transpose_centeredDefectComponentNeighborIncidenceMatrix_mul_eq_zero
      G hfree hreg hcard c d hcd
  have hr := congrArg
    (fun M : Matrix c.supp d.supp ℤ => M.map (Int.castRingHom ℝ)) hz
  rw [Matrix.map_mul, Matrix.transpose_map] at hr
  have hzero : (0 : Matrix c.supp d.supp ℤ).map (Int.castRingHom ℝ) =
      (0 : Matrix c.supp d.supp ℝ) := by
    ext x y
    simp [Matrix.map_apply]
  rw [hzero] at hr
  exact hr

/-- The sum of the exact centered-block ranks is the ambient square order minus
the number of defect components. -/
theorem sum_realCenteredDefectComponentNeighborIncidenceMatrix_rank
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) :
    (∑ c : (secondOrderDefectGraph G).ConnectedComponent,
        (realCenteredDefectComponentNeighborIncidenceMatrix G q c).rank) =
      q * q - Fintype.card (secondOrderDefectGraph G).ConnectedComponent := by
  let D := secondOrderDefectGraph G
  change (∑ c : D.ConnectedComponent,
      (realCenteredDefectComponentNeighborIncidenceMatrix G q c).rank) =
    q * q - Fintype.card D.ConnectedComponent
  have hrank (c : D.ConnectedComponent) :
      (realCenteredDefectComponentNeighborIncidenceMatrix G q c).rank =
        c.supp.ncard - 1 := by
    simpa only [Set.fintypeCard_eq_ncard] using
      realCenteredDefectComponentNeighborIncidenceMatrix_rank
        G hfree hq hreg hcard c
  simp_rw [hrank]
  have hpos (c : D.ConnectedComponent) : 1 ≤ c.supp.ncard := by
    have := c.nonempty_supp.ncard_pos
    omega
  have hsumPlus :
      (∑ c : D.ConnectedComponent, (c.supp.ncard - 1)) +
          Fintype.card D.ConnectedComponent =
        ∑ c : D.ConnectedComponent, c.supp.ncard := by
    have hones : (∑ _c : D.ConnectedComponent, 1) =
        Fintype.card D.ConnectedComponent := by simp
    rw [← hones, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    exact Nat.sub_add_cancel (hpos c)
  have hparts : (∑ c : D.ConnectedComponent, c.supp.ncard) = q * q := by
    rw [sum_connectedComponent_supp_ncard D, hcard]
  omega

end

end Erdos85
