import Proofs.Erdos85BinarySquareComponentAdjacencyToAllOwnerSpectrum
import Proofs.Erdos85OrderSixtyFourRegularPartition

/-!
# Simultaneous owner spectrum in the four-component order-64 branch

Four defect components at order 64 all have order sixteen, hence normalized
owner multiplicity two.  The general component-to-owner transfer therefore
specializes to the exact eigenvalues `5 - μ` in the distinguished owner color
and `-2` in every other color.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **Exact four-component owner transfer at order 64.** -/
theorem orderSixtyFour_regular_fourComponent_componentEigenvector_to_allOwners
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (v : c.supp → ℝ) (μ : ℝ)
    (hv : (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℝ).mulVec v =
      μ • v) (hv0 : v ≠ 0) (hμ : (7 : ℝ) - μ ≠ 0) :
    let w := (realCenteredDefectComponentNeighborIncidenceMatrix G 8 c).mulVec v
    w ≠ 0 ∧
      ((componentOwnerGraph G
        (secondOrderDefectGraph G) c).adjMatrix ℝ).mulVec w =
          (5 - μ) • w ∧
      ∀ d : (secondOrderDefectGraph G).ConnectedComponent, d ≠ c →
        ((componentOwnerGraph G
          (secondOrderDefectGraph G) d).adjMatrix ℝ).mulVec w =
            (-2 : ℝ) • w := by
  let m : (secondOrderDefectGraph G).ConnectedComponent → ℕ := fun _ => 2
  have horders := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount
  have hm : ∀ d, d.supp.ncard = 8 * m d := by
    intro d
    simp [m, horders d]
  have htransfer := componentAdjacency_eigenvector_to_all_componentOwnerGraphs
    G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm c v μ hv hv0 (by
      norm_num
      exact hμ)
  dsimp only at htransfer ⊢
  refine ⟨htransfer.1, ?_, ?_⟩
  · rw [show (5 : ℝ) - μ = 7 - μ - 2 by ring]
    simpa [m] using htransfer.2.1
  · intro d hdc
    have hd := htransfer.2.2 d hdc
    simpa [m] using hd

end

end Erdos85
