import Proofs.Erdos85ThreeSeparatorExceptionalDefectNeighborhood
import Proofs.Erdos85ThreeSeparatorPositiveSpikeSmallSideLocation

/-!
# Separator-located exceptional point

After excluding `c ∈ X`, the branch `c ∈ W` has only one or two defect
attachments into `X`.  The B16 location balance and B17' neighborhood
identity give `1 + m_c + r_X ≤ 3`, while separator minimality gives
`m_c ≥ 1`.  This forces the exact alternatives in (B17W).
-/

open Finset SimpleGraph

namespace Erdos85

/-- Subtraction-safe arithmetic core of B17W. -/
theorem exceptionalPoint_W_attachment_cases
    {q m n rX : ℕ} (hq : 3 ≤ q)
    (hsum : m + n = q - 1) (hmin : 1 ≤ m)
    (hlocation : 1 + m + rX ≤ 3) :
    (m = 1 ∧ n = q - 2) ∨
      (m = 2 ∧ n = q - 3 ∧ rX = 0) := by
  omega

/-- Graph-facing B17W interface, with `m,n` instantiated by the two shore
attachment counts of a separator vertex. -/
theorem exceptionalPoint_W_defect_attachment_cases
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (c : V) (X Y R : Finset V) {q : ℕ} (hq : 3 ≤ q)
    (hsum : (D.neighborFinset c ∩ X).card +
      (D.neighborFinset c ∩ Y).card = q - 1)
    (hmin : 1 ≤ (D.neighborFinset c ∩ X).card)
    (hlocation : 1 + (D.neighborFinset c ∩ X).card + (R ∩ X).card ≤ 3) :
    ((D.neighborFinset c ∩ X).card = 1 ∧
      (D.neighborFinset c ∩ Y).card = q - 2) ∨
    ((D.neighborFinset c ∩ X).card = 2 ∧
      (D.neighborFinset c ∩ Y).card = q - 3 ∧ (R ∩ X).card = 0) := by
  exact exceptionalPoint_W_attachment_cases hq hsum hmin hlocation

#print axioms exceptionalPoint_W_attachment_cases
#print axioms exceptionalPoint_W_defect_attachment_cases

end Erdos85
