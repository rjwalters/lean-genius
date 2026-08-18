import Proofs.Erdos85OrderSixtyFourDefectSecondMoment
import Proofs.Erdos85HermitianNonprincipalFactorSecondMoment

/-! # The factorwise second-moment budget on the H16 defect block -/

open SimpleGraph Polynomial

namespace Erdos85

noncomputable section

/-- Every genuine nonprincipal characteristic factor of the distinguished
H16 defect block has second root-power sum at most `63`.  The explicit
factorization hypothesis ensures that `(X - 7)` remains in the complement;
no simultaneous-spectrum assertion is assumed. -/
theorem orderSixtyFour_seven_defect_components_defect_factor_secondMoment
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 7) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16 ∧
      ∀ f r : ℂ[X], f ≠ 0 → r ≠ 0 →
        (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℂ).charpoly =
          f * (X - C 7) * r →
        (complexRootPowerSum f 2).re ≤ 63 := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨c, hc16, _htraceZ, _hbudgetZ, htraceC, _hbudgetC⟩ :=
    orderSixtyFour_seven_defect_components_defect_secondMoment
      G hfree hmin hcover hcount
  let A := (D.induce c.supp).adjMatrix ℂ
  have hherm : A.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp [A, SimpleGraph.adjMatrix_apply, D.adj_comm]
  refine ⟨c, hc16, ?_⟩
  intro f r hf hr hfactor
  have hbound :=
    complexRootPowerSum_two_re_le_trace_sq_sub_principal_seven
      A hherm hf hr hfactor
  have htrace : (Matrix.trace (A ^ 2)).re = 112 := by
    simpa [A, pow_two] using congrArg Complex.re htraceC
  linarith

end

end Erdos85
