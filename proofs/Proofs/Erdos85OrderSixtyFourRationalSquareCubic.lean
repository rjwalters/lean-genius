import Proofs.Erdos85OrderSixtyFourColoredSupport

/-! # Rational square-sector cubic terminal at order 64 -/

namespace Erdos85

set_option maxHeartbeats 800000

/-- Arithmetic core of the order-16 rational square-sector exclusion.

For a 7-regular graph on 16 vertices, remove the principal eigenvalue `7`
and let `m6`, `m3`, and `mn2` be the multiplicities of the defect
eigenvalues `6`, `3`, and `-2`.  The remaining adjacency-spectrum moments
give `hcauchy`.  The integers `s6`, `s3`, `sn2` are the signed
multiplicities of the square roots `±1`, `±2`, and `±3`.  Even without using
their parity constraints, total residual trace `-8` is incompatible with a
residual cubic trace in `[-32, 0]`. -/
theorem orderSixteen_rational_square_sectors_cubic_impossible
    (m6 m3 mn2 : ℕ) (s6 s3 sn2 : ℤ)
    (hmass : m6 + m3 + mn2 ≤ 15)
    (hsquareMass : 36 * m6 + 9 * m3 + 4 * mn2 ≤ 63)
    (hcauchy :
      ((-7 : ℤ) - 6 * m6 - 3 * m3 + 2 * mn2) ^ 2 ≤
        ((15 : ℤ) - m6 - m3 - mn2) *
          ((63 : ℤ) - 36 * m6 - 9 * m3 - 4 * mn2))
    (hs6lo : -(m6 : ℤ) ≤ s6) (hs6hi : s6 ≤ m6)
    (hs3lo : -(m3 : ℤ) ≤ s3) (hs3hi : s3 ≤ m3)
    (hsn2lo : -(mn2 : ℤ) ≤ sn2) (hsn2hi : sn2 ≤ mn2)
    (htrace : s6 + 2 * s3 + 3 * sn2 = -8)
    (hcubeLo : -32 ≤ s6 + 8 * s3 + 27 * sn2)
    (hcubeHi : s6 + 8 * s3 + 27 * sn2 ≤ 0) : False := by
  have hm6 : m6 ≤ 1 := by omega
  have hm3 : m3 ≤ 7 := by omega
  have hmn2 : mn2 ≤ 15 := by omega
  interval_cases m6 <;>
    interval_cases m3 <;>
      interval_cases mn2 <;>
        norm_num at * <;>
        omega

end Erdos85
