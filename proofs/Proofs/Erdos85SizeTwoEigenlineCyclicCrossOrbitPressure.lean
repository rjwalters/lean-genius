import Proofs.Erdos85SizeTwoEigenlineCyclicSelectedOrbitSupport
import Proofs.Erdos85SizeTwoEigenlineCyclicMultiOrbitCollisionUpper

/-!
# Sharp-support Cauchy forces cross-orbit pressure

After cancelling the positive allowed-support size from the sharpened Cauchy
inequality, the exact collision decomposition and the elementary within-orbit
cap give a lower-pressure inequality on the ordered cross-orbit term.  This
pinpoints the aggregate quantity that a packing refutation must improve.
-/

namespace Erdos85

noncomputable section

/-- Cancellation form of sharp-support Cauchy. -/
theorem sizeTwoCyclicSelectedOrbitMultiplicity_collision_pressure
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (hq : 2 < q) (hq1 : (1 : ZMod q) ≠ 0)
    (ha : a ≠ -1 - a)
    (T : Finset (sizeTwoAllowedDifference q a)) :
    T.card * T.card * (q * (q - 2)) ≤
      T.card * (q * (q - 2)) +
        2 * ∑ e : SizeTwoCyclicAbsoluteGridEdge q,
          (sizeTwoCyclicSelectedOrbitMultiplicity code T e).choose 2 := by
  have h :=
    sizeTwoCyclicSelectedOrbitMultiplicity_choose_two_lower_allowedSupport
      code hq1 ha T
  have hqpos : 0 < q := by omega
  have hqsub : 0 < q - 2 := by omega
  have hsupport : 0 < q * (q - 2) := Nat.mul_pos hqpos hqsub
  have hleft :
      (T.card * (q * (q - 2))) ^ 2 =
        (q * (q - 2)) * (T.card * T.card * (q * (q - 2))) := by ring
  rw [hleft] at h
  exact le_of_mul_le_mul_left h hsupport

/-- The sharp-support lower bound cannot be absorbed by the sum of the
within-orbit caps: the displayed ordered cross term must carry the remainder. -/
theorem sizeTwoCyclicMatchingOrbitMultiplicity_cross_pressure
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (hq : 2 < q) (hq1 : (1 : ZMod q) ≠ 0)
    (ha : a ≠ -1 - a)
    (T : Finset (sizeTwoAllowedDifference q a)) :
    T.card * T.card * (q * (q - 2)) ≤
      T.card * (q * (q - 2)) + T.card * (q * (q - 1)) +
        ∑ p ∈ T.offDiag, ∑ e : SizeTwoCyclicAbsoluteGridEdge q,
          sizeTwoCyclicMatchingOrbitMultiplicity code p.1 e *
            sizeTwoCyclicMatchingOrbitMultiplicity code p.2 e := by
  have hlower := sizeTwoCyclicSelectedOrbitMultiplicity_collision_pressure
    code hq hq1 ha T
  rw [sizeTwoCyclicSelectedOrbitMultiplicity_choose_two_sum_decomposition]
    at hlower
  have hup := Nat.add_le_add_left
    (Nat.add_le_add_right
      (two_mul_sizeTwoCyclicMatchingOrbitMultiplicity_choose_two_sum_selected_le
        code T)
      (∑ p ∈ T.offDiag, ∑ e : SizeTwoCyclicAbsoluteGridEdge q,
        sizeTwoCyclicMatchingOrbitMultiplicity code p.1 e *
          sizeTwoCyclicMatchingOrbitMultiplicity code p.2 e))
    (T.card * (q * (q - 2)))
  exact hlower.trans (by simpa [Nat.add_assoc] using hup)

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicSelectedOrbitMultiplicity_collision_pressure
#print axioms Erdos85.sizeTwoCyclicMatchingOrbitMultiplicity_cross_pressure
