import Proofs.Erdos85MuNegThreeZeroFiveCorrectFiniteSat
import Proofs.Erdos85MuNegThreeZeroFiveCorrectOwnerCertificate

/-! # Checked finite contradiction for the honest 88-owner h305 endpoint -/

namespace Erdos85

open Std Sat

theorem muNegThreeZeroFiveCorrectFiniteSemantics_false
    {uTri vTri sigma : Bool} {D X : Nat → Nat → Bool}
    (hcanon : (uTri = false ∧ vTri = false) ∨
      (uTri = false ∧ vTri = true) ∨ (uTri = true ∧ vTri = true))
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
  have hunsat : (muNegThreeZeroFiveCorrectOwnerSatCnf
      uTri vTri sigma).Unsat := by
    rcases hcanon with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      cases sigma
    · exact h305Owner88TfTfS0_unsat
    · exact h305Owner88TfTfS1_unsat
    · exact h305Owner88TfTriS0_unsat
    · exact h305Owner88TfTriS1_unsat
    · exact h305Owner88TriTriS0_unsat
    · exact h305Owner88TriTriS1_unsat
  exact muNegThreeZeroFiveCorrectFiniteSemantics_false_of_unsat
    hunsat hrowSame hrowOpp hcolSame hcolOpp hsem

end Erdos85

#print axioms Erdos85.muNegThreeZeroFiveCorrectFiniteSemantics_false
