import Proofs.Erdos85DegreeTwelveResolvent

/-!
# Exact resolvent factors for the degree-six single-cycle boundary

For a single defect cycle of order 33, the component-orthogonal spectral
parameter is `5-X²`.  We exploit `C₃₃ = C₃ ∘ C₁₁` and
`C₃(Z)-2 = (Z-2)(Z+1)²` to keep every checked identity small.
-/

namespace Erdos85

open Polynomial Polynomial.Chebyshev

noncomputable def degreeSixSpectralSubstitution : ℤ[X] := 5 - X ^ 2
noncomputable def degreeSixFactor2 : ℤ[X] := X ^ 2 - 6
noncomputable def degreeSixFactor10 : ℤ[X] :=
  X ^ 10 - 26 * X ^ 8 + 266 * X ^ 6 - 1337 * X ^ 4 +
    3298 * X ^ 2 - 3191
noncomputable def degreeSixFactor20 : ℤ[X] :=
  X ^ 20 - 49 * X ^ 18 + 1070 * X ^ 16 - 13710 * X ^ 14 +
    114134 * X ^ 12 - 644986 * X ^ 10 + 2505607 * X ^ 8 -
    6606933 * X ^ 6 + 11317332 * X ^ 4 - 11372458 * X ^ 2 +
    5091241

/-- A triangle contributes two component-orthogonal roots governed by
`X²-6`. -/
theorem degreeSix_cycle3_resolvent_factorization :
    (C ℤ 3 - 2).comp degreeSixSpectralSubstitution =
      (3 - X ^ 2) * degreeSixFactor2 ^ 2 := by
  have hC := chebyshev_C_nat_eq_vietaLucasNat 3
  norm_num at hC
  rw [hC]
  norm_num [vietaLucasNat, degreeSixSpectralSubstitution, degreeSixFactor2]
  ring

theorem degreeSix_cycle11_minus_two_factorization :
    (C ℤ 11 - 2).comp degreeSixSpectralSubstitution =
      (3 - X ^ 2) * degreeSixFactor10 ^ 2 := by
  have hC := chebyshev_C_nat_eq_vietaLucasNat 11
  norm_num at hC
  rw [hC]
  norm_num [vietaLucasNat, degreeSixSpectralSubstitution, degreeSixFactor10]
  ring_nf

theorem degreeSix_cycle11_plus_one_factorization :
    (C ℤ 11 + 1).comp degreeSixSpectralSubstitution =
      -degreeSixFactor2 * degreeSixFactor20 := by
  have hC := chebyshev_C_nat_eq_vietaLucasNat 11
  norm_num at hC
  rw [hC]
  norm_num [vietaLucasNat, degreeSixSpectralSubstitution,
    degreeSixFactor2, degreeSixFactor20]
  ring_nf

theorem degreeSix_cycle33_resolvent_factorization :
    (C ℤ 33 - 2).comp degreeSixSpectralSubstitution =
      (3 - X ^ 2) * degreeSixFactor2 ^ 2 *
        degreeSixFactor10 ^ 2 * degreeSixFactor20 ^ 2 := by
  have hdecomp :
      (C ℤ 33 - 2).comp degreeSixSpectralSubstitution =
        ((C ℤ 11 - 2).comp degreeSixSpectralSubstitution) *
          ((C ℤ 11 + 1).comp degreeSixSpectralSubstitution) ^ 2 := by
    rw [show (33 : ℤ) = 3 * 11 by norm_num, C_mul]
    have hC3 := chebyshev_C_nat_eq_vietaLucasNat 3
    norm_num at hC3
    rw [hC3]
    norm_num [vietaLucasNat]
    ring
  rw [hdecomp, degreeSix_cycle11_minus_two_factorization,
    degreeSix_cycle11_plus_one_factorization]
  ring

end Erdos85
