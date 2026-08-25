import Proofs.Erdos85MuNegThreeZeroFiveCorrectFiniteSemantics
import Proofs.Erdos85MuNegThreeZeroFiveCorrectOwnerNonzero

/-! # Certificate-independent finite reduction for honest h305 -/

namespace Erdos85

open Std Sat

theorem muNegThreeZeroFiveCorrectFiniteSemantics_false_of_unsat
    {uTri vTri sigma : Bool} {D X : Nat → Nat → Bool}
    (hunsat : (muNegThreeZeroFiveCorrectOwnerSatCnf
      uTri vTri sigma).Unsat)
    (hrowSame : ∀ i, i < 8 →
      (((List.range 8).filter fun j =>
        muNegOneSign sigma i == muNegOneSign sigma (8 + j)).countP
          fun j => D i j) = 2)
    (hrowOpp : ∀ i, i < 8 →
      (((List.range 8).filter fun j =>
        !(muNegOneSign sigma i == muNegOneSign sigma (8 + j))).countP
          fun j => D i j) = 3)
    (hcolSame : ∀ j, j < 8 →
      (((List.range 8).filter fun i =>
        muNegOneSign sigma i == muNegOneSign sigma (8 + j)).countP
          fun i => D i j) = 2)
    (hcolOpp : ∀ j, j < 8 →
      (((List.range 8).filter fun i =>
        !(muNegOneSign sigma i == muNegOneSign sigma (8 + j))).countP
          fun i => D i j) = 3)
    (hsem : MuNegThreeZeroFiveCorrectNonCrossSemantics
      uTri vTri sigma D X) : False := by
  have hformula := muNegThreeZeroFiveCorrectOwnerDimacsClauses_satisfied
    hrowSame hrowOpp hcolSame hcolOpp hsem
  have hsat : (muNegThreeZeroFiveCorrectOwnerSatCnf
      uTri vTri sigma).Sat
      (satAssignmentOfDimacs
        (muNegThreeZeroFiveCorrectValOfRelations uTri vTri D X)) := by
    simpa only [muNegThreeZeroFiveCorrectOwnerSatCnf] using
      satCnf_of_dimacsFormulaSatisfied
        (muNegThreeZeroFiveCorrectOwnerDimacsClauses_nonzero_of_mem
          uTri vTri sigma)
        hformula
  have hfalse := hunsat
    (satAssignmentOfDimacs
      (muNegThreeZeroFiveCorrectValOfRelations uTri vTri D X))
  rw [CNF.sat_def] at hsat
  rw [hsat] at hfalse
  contradiction

end Erdos85

#print axioms Erdos85.muNegThreeZeroFiveCorrectFiniteSemantics_false_of_unsat
