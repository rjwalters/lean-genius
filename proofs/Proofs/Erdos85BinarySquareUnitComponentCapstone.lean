import Proofs.Erdos85BinarySquareRegularCapstone
import Proofs.Erdos85BinarySquareRegularParity

/-! # A precise uniform unit-component target for A-REG -/

open SimpleGraph

namespace Erdos85

/-- A proposed q-generic structural strengthening of A-REG.  It is packaged
as a proposition, not introduced as a Lean axiom: every binary square-order
regular candidate has a defect component of the minimum possible normalized
size one. -/
def BinarySquareUnitComponentPrinciple : Prop :=
  ∀ k : Nat, 3 ≤ k →
    ∀ (G : SimpleGraph (Fin (2 ^ k * 2 ^ k)))
      (_ : DecidableRel G.Adj),
      ¬ containsC4 (Fin (2 ^ k * 2 ^ k)) G →
      (∀ x, G.degree x = 2 ^ k) →
      ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
        c.supp.ncard = 2 ^ k

/-- The proposed unit-component principle closes A-REG uniformly: the
existing parity theorem forbids such a component at every even degree. -/
theorem binarySquareRegularExclusion_of_unitComponentPrinciple
    (hunit : BinarySquareUnitComponentPrinciple) :
    BinarySquareRegularExclusion := by
  intro k hk hex
  rcases hex with ⟨G, hdec, hfree, hreg⟩
  letI := hdec
  classical
  obtain ⟨c, hc⟩ := hunit k hk G hdec hfree hreg
  have hq : 3 ≤ 2 ^ k := by
    calc
      3 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hqEven : Even (2 ^ k) :=
    (Nat.even_pow' (by omega)).mpr even_two
  exact (binarySquare_regular_no_sizeQ_defectComponent_of_even
    G hfree (q := 2 ^ k) hq hqEven hreg (by simp) c) hc

/-- Consequently the same structural principle implies the negative answer
to Erdős 85 through the already verified binary-square capstone. -/
theorem not_erdos85Question_of_binarySquareUnitComponentPrinciple
    (hunit : BinarySquareUnitComponentPrinciple) : ¬ Erdos85Question :=
  not_erdos85Question_of_binarySquareRegularExclusion
    (binarySquareRegularExclusion_of_unitComponentPrinciple hunit)

end Erdos85

#print axioms Erdos85.binarySquareRegularExclusion_of_unitComponentPrinciple
#print axioms Erdos85.not_erdos85Question_of_binarySquareUnitComponentPrinciple
