import Mathlib

/-!
# Strongly-regular parameters of a proper binary-square owner color

For an owner color belonging to a normalized defect component of order
`q * m`, the owner degree is `m * (q - 1)` and its forced bottom adjacency
root is `-m`.  The bottom-root equation and the standard strongly-regular
parameter equation uniquely determine the two codegrees.  This file keeps
that nonlinear integer calculation separate from the graph/matrix bridge.
-/

namespace Erdos85

/-- The strongly-regular parameter equation and the forced root `-m`
uniquely give `lambda = q + m^2 - 3m` and `mu = m(m-1)` for a proper owner
color (`m < q`).  The hypotheses are written over `ℤ` to avoid truncated
subtraction at the graph-facing interface. -/
theorem properOwner_srg_parameters_of_bottom_root
    {q m lambda mu : ℤ} (hq : 2 ≤ q) (hm : 2 ≤ m)
    (hroot :
      m * lambda - (m - 1) * mu = m * (q - m - 1))
    (hparam :
      (m * (q - 1)) * (m * (q - 1) - lambda - 1) =
        (q * q - m * (q - 1) - 1) * mu) :
    lambda = q + m * m - 3 * m ∧ mu = m * (m - 1) := by
  have hmuFactor : q * (q - 1) * (mu - m * (m - 1)) = 0 := by
    nlinarith [hroot, hparam]
  have hq0 : q ≠ 0 := by omega
  have hq10 : q - 1 ≠ 0 := by omega
  have hmu : mu = m * (m - 1) := by
    rcases mul_eq_zero.mp hmuFactor with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact (hq0 h).elim
      · exact (hq10 h).elim
    · nlinarith
  constructor
  · rw [hmu] at hroot
    nlinarith
  · exact hmu

/-- Substituting the forced codegrees into the SRG adjacency-square identity
gives the shifted-owner identity `M² = qM + m(m-1)J`.  This scalar lemma is
the coefficient calculation used by the matrix bridge. -/
theorem properOwner_shifted_srg_coefficients
    {q m lambda mu : ℤ}
    (hlambda : lambda = q + m * m - 3 * m)
    (hmu : mu = m * (m - 1)) :
    m * (q - 1) - mu + m * m = q * m ∧
      lambda - mu + 2 * m = q := by
  constructor <;> nlinarith

#print axioms properOwner_srg_parameters_of_bottom_root

#print axioms properOwner_shifted_srg_coefficients

end Erdos85
