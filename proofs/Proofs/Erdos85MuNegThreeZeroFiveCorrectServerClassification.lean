import Proofs.Erdos85MuNegThreeZeroFiveCorrectGraphActivity
import Proofs.Erdos85MuNegOneOneFourServerClassification

/-!
# Corrected h305 server classification

The first step is the exact completeness of the honest 88-owner table.  The
three lemmas below include the antipodal difference `4`, which is precisely
the case omitted by the old h114 table and its server-classification theorem.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxRecDepth 12000 in
theorem muNegThreeZeroFiveCorrect_within_left_mem_table :
    ∀ (uTri vTri : Bool) (x y : Fin 8), x.val < y.val →
      let d := (y.val : ZMod 8) - (x.val : ZMod 8)
      (if uTri then d = 1 ∨ d = 4 ∨ d = 7
       else d = 3 ∨ d = 4 ∨ d = 5) →
      ∃ f : Fin 88,
        muNegThreeZeroFiveCorrectOwnerAt uTri vTri f = (x.val, y.val) := by
  decide

set_option maxRecDepth 12000 in
theorem muNegThreeZeroFiveCorrect_within_right_mem_table :
    ∀ (uTri vTri : Bool) (x y : Fin 8), x.val < y.val →
      let d := (y.val : ZMod 8) - (x.val : ZMod 8)
      (if vTri then d = 1 ∨ d = 4 ∨ d = 7
       else d = 3 ∨ d = 4 ∨ d = 5) →
      ∃ f : Fin 88,
        muNegThreeZeroFiveCorrectOwnerAt uTri vTri f =
          (8 + x.val, 8 + y.val) := by
  decide

set_option maxRecDepth 12000 in
theorem muNegThreeZeroFiveCorrect_cross_mem_table :
    ∀ (uTri vTri : Bool) (x y : Fin 8),
      ∃ f : Fin 88,
        muNegThreeZeroFiveCorrectOwnerAt uTri vTri f =
          (x.val, 8 + y.val) := by
  decide

end


end Erdos85

#print axioms Erdos85.muNegThreeZeroFiveCorrect_within_left_mem_table
#print axioms Erdos85.muNegThreeZeroFiveCorrect_within_right_mem_table
#print axioms Erdos85.muNegThreeZeroFiveCorrect_cross_mem_table
