import Proofs.Erdos85MinimumDefectCutResidue
import Proofs.Erdos85TwoSeparatorResidueArithmetic

/-!
# Oriented residues for two complementary minimum-cut shores

The individual minimum-cut theorem gives residues `+1` or `-1`.  When the
two shores exhaust the square-order vertex set after deleting two vertices,
their total size forces both choices to be `-1`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Two complementary `q-1` defect cuts on `q²-2` vertices both have shore
cardinality congruent to `q-1` modulo `q`. -/
theorem binarySquare_two_predCuts_both_card_mod_eq_pred
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 8 ≤ q)
    (hqEven : Even q) (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) (S T : Finset V)
    (hcards : S.card + T.card = q * q - 2)
    (hcutS : finsetGraphCutSize (secondOrderDefectGraph G) S = q - 1)
    (hcutT : finsetGraphCutSize (secondOrderDefectGraph G) T = q - 1) :
    S.card % q = q - 1 ∧ T.card % q = q - 1 := by
  have hS := binarySquare_pred_defectCut_card_mod_eq_one_or_pred
    G hfree (by omega : 4 ≤ q) hqEven hreg hcard S hcutS
  have hT := binarySquare_pred_defectCut_card_mod_eq_one_or_pred
    G hfree (by omega : 4 ≤ q) hqEven hreg hcard T hcutT
  exact twoSeparator_both_residue_sub_one q S.card T.card hq hcards hS hT

#print axioms binarySquare_two_predCuts_both_card_mod_eq_pred

end

end Erdos85
