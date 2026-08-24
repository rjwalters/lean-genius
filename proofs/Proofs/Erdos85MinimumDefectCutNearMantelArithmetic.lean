import Proofs.Erdos85MinimumDefectCutCappedSquare

/-!
# Near-Mantel lower bound from the minimum-cut identity

This is the numeric bridge from equation (7) and the sharp capped-square
bound to the induced-edge lower bound used by the two-separator terminal.
-/

open Finset

namespace Erdos85

/-- Equation (7), regular handshaking, and the minimum-shore boundary cap
force the associated low set to have near-Mantel density.  We parameterize
the even degree as `q = 2(r+1)`, so the boundary cap is exactly `r`. -/
theorem nearMantel_lower_of_cutIdentity_of_capped_boundary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℕ) {q r cutZ e : ℕ}
    (hr : 2 ≤ r) (hq : q = 2 * (r + 1))
    (hbound : ∀ i, d i ≤ r)
    (hsum : ∑ i, d i = q - 1)
    (hcutIdentity : cutZ = q - 1 + ∑ i, (d i) ^ 2)
    (hhandshake : cutZ + 2 * e = q * (q - 1)) :
    q ^ 2 - 4 ≤ 4 * e := by
  have hpred : q - 1 = 2 * r + 1 := by omega
  have hsum' : ∑ i, d i = 2 * r + 1 := by omega
  have hsquares : (∑ i, (d i) ^ 2) ≤ 2 * r ^ 2 + 1 :=
    sum_sq_le_two_mul_sq_add_one_of_bound_of_sum d hr hbound hsum'
  rw [hpred] at hcutIdentity hhandshake
  rw [hq]
  simp only [pow_two] at hsquares hcutIdentity hhandshake ⊢
  have hraw : 2 * (r + 1) * (2 * (r + 1)) ≤ 4 * e + 4 := by
    nlinarith
  omega

end Erdos85

#print axioms Erdos85.nearMantel_lower_of_cutIdentity_of_capped_boundary
