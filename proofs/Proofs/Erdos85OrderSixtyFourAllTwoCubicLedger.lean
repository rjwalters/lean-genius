import Proofs.Erdos85BinarySquareCenteredOwnerCubicTrace
import Proofs.Erdos85OrderSixtyFourOwnerResidualThirdCoefficient

/-!
# Cubic trace ledger for the order-64 all-two stratum

If every defect component has order 16, there are exactly four components.
Specializing the uniform owner/defect cubic resolution at `q=8` and
`m_c=2` gives the exact graph-dependent trace budget `24192`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Four order-16 defect components exhaust an order-64 vertex set. -/
theorem orderSixtyFour_card_defectComponents_eq_four_of_all_sizeSixteen
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [Fintype D.ConnectedComponent]
    (hcard : Fintype.card V = 64)
    (hm : ∀ c : D.ConnectedComponent, c.supp.ncard = 16) :
    Fintype.card D.ConnectedComponent = 4 := by
  have hparts := sum_connectedComponent_supp_ncard D
  rw [hcard] at hparts
  simp_rw [hm] at hparts
  simp only [Finset.sum_const, Finset.card_univ] at hparts
  norm_num at hparts
  omega

/-- **Exact all-two cubic ledger.**  The four owner adjacency-cube traces
plus the defect adjacency-cube trace equal `24192`.  Dividing by six in the
triangle interpretation gives the scout's total triangle budget `4032`. -/
theorem orderSixtyFour_all_sizeSixteen_owner_defect_cube_trace_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (hm : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16) :
    (∑ c : (secondOrderDefectGraph G).ConnectedComponent,
      Matrix.trace
        ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ *
          (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ *
          (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ)) +
      Matrix.trace
        ((secondOrderDefectGraph G).adjMatrix ℤ *
          (secondOrderDefectGraph G).adjMatrix ℤ *
          (secondOrderDefectGraph G).adjMatrix ℤ) = 24192 := by
  let D := secondOrderDefectGraph G
  have hccard : Fintype.card D.ConnectedComponent = 4 :=
    orderSixtyFour_card_defectComponents_eq_four_of_all_sizeSixteen
      D hcard hm
  let m : D.ConnectedComponent → ℕ := fun _ => 2
  have hm' : ∀ c : D.ConnectedComponent, c.supp.ncard = 8 * m c := by
    intro c
    simpa [m] using hm c
  have hsum : ∑ c : D.ConnectedComponent, m c = 8 := by
    simp [m, hccard]
  have h := binarySquare_regular_owner_defect_cube_trace_eq
    G hfree (q := 8) (by omega) hreg (by simpa using hcard) m hm' hsum
  dsimp [m] at h
  simp only [Finset.sum_add_distrib] at h
  simp only [Finset.sum_const, Finset.card_univ, hccard] at h
  norm_num at h
  linarith

end

end Erdos85
