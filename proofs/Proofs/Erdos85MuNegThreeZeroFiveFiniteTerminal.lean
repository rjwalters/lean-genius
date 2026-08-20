import Proofs.Erdos85MuNegThreeZeroFiveOwnerCnfSemantics
import Proofs.Erdos85MuNegThreeZeroFiveOwnerCubeRouter
import Proofs.Erdos85MuNegThreeZeroFiveMixedCubeRouter
import Proofs.Erdos85MuNegThreeZeroFiveOneOneCubeRouter

/-!
# Unified checked finite terminal for h305

This packages the three normalized shore modes and both sign phases behind one
graph-facing constraint record.  A realization only needs to supply the
structural nonzero fact and the genuine exact-three count on cross row zero.
-/

namespace Erdos85

open Std Sat

theorem muNegThreeZeroFiveOwnerConstraintSemantics_false
    {uTri vTri sigma : Bool} {val : DimacsValuation}
    (hmode : (uTri = false ∧ vTri = false) ∨
      (uTri = false ∧ vTri = true) ∨
      (uTri = true ∧ vTri = true))
    (hnz : ∀ clause ∈
      muNegThreeZeroFiveOwnerDimacsClauses uTri vTri sigma,
      DimacsClauseNonzero clause)
    (hsem : MuNegThreeZeroFiveOwnerConstraintSemantics
      uTri vTri sigma val)
    (hcount : (if sigma then [val 1, val 3, val 5, val 7]
      else [val 2, val 4, val 6, val 8]).count true = 3) : False := by
  have hsat := muNegThreeZeroFiveOwnerConstraintSemantics_formulaSatisfied hsem
  rcases hmode with hzz | hmixed | hone
  · rcases hzz with ⟨rfl, rfl⟩
    cases sigma with
    | false =>
        exact muNegThreeZeroFiveCorrectZZS0_false_of_formula_exactOpp
          val hnz hsat (by simpa using hcount)
    | true =>
        exact muNegThreeZeroFiveCorrectZZS1_false_of_formula_exactOpp
          val hnz hsat (by simpa using hcount)
  · rcases hmixed with ⟨rfl, rfl⟩
    cases sigma with
    | false =>
        exact muNegThreeZeroFiveCorrectMixedS0_false_of_formula_exactOpp
          val hnz hsat (by simpa using hcount)
    | true =>
        exact muNegThreeZeroFiveCorrectMixedS1_false_of_formula_exactOpp
          val hnz hsat (by simpa using hcount)
  · rcases hone with ⟨rfl, rfl⟩
    cases sigma with
    | false =>
        exact muNegThreeZeroFiveCorrectOneOneS0_false_of_formula_exactOpp
          val hnz hsat (by simpa using hcount)
    | true =>
        exact muNegThreeZeroFiveCorrectOneOneS1_false_of_formula_exactOpp
          val hnz hsat (by simpa using hcount)

end Erdos85

#print axioms Erdos85.muNegThreeZeroFiveOwnerConstraintSemantics_false
