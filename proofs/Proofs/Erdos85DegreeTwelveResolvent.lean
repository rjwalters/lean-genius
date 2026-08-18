import Proofs.Erdos85CycleResolvent

/-!
# Exact cycle-resolvent factors for the degree-twelve exception

At `d = 12`, substituting `11-X²` into the characteristic polynomials of
the defect cycles `C₁₅` and `C₆₀` gives the explicit even factors below.
-/

namespace Erdos85

open Polynomial Polynomial.Chebyshev

/-- Natural-index implementation of the rescaled Chebyshev recurrence. -/
noncomputable def vietaLucasNat : ℕ → ℤ[X]
  | 0 => 2
  | 1 => X
  | n + 2 => X * vietaLucasNat (n + 1) - vietaLucasNat n

theorem chebyshev_C_nat_eq_vietaLucasNat (n : ℕ) :
    C ℤ (n : ℤ) = vietaLucasNat n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [vietaLucasNat]
  | one => simp [vietaLucasNat]
  | more n hn hn1 =>
      rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by norm_num,
        C_add_two, show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by norm_num,
        hn1, hn]
      rfl

noncomputable def degreeTwelveSpectralSubstitution : ℤ[X] := 11 - X ^ 2

noncomputable def degreeTwelveFactor2a : ℤ[X] := X ^ 2 - 12
noncomputable def degreeTwelveFactor2b : ℤ[X] := X ^ 2 - 13
noncomputable def degreeTwelveFactor2c : ℤ[X] := X ^ 2 - 11
noncomputable def degreeTwelveFactor2d : ℤ[X] := X ^ 2 - 10

noncomputable def degreeTwelveFactor4a : ℤ[X] := X ^ 4 - 23 * X ^ 2 + 131
noncomputable def degreeTwelveFactor4b : ℤ[X] := X ^ 4 - 22 * X ^ 2 + 118
noncomputable def degreeTwelveFactor4c : ℤ[X] := X ^ 4 - 21 * X ^ 2 + 109

noncomputable def degreeTwelveFactor8a : ℤ[X] :=
  X ^ 8 - 43 * X ^ 6 + 689 * X ^ 4 - 4877 * X ^ 2 + 12871
noncomputable def degreeTwelveFactor8b : ℤ[X] :=
  X ^ 8 - 45 * X ^ 6 + 755 * X ^ 4 - 5595 * X ^ 2 + 15445
noncomputable def degreeTwelveFactor8c : ℤ[X] :=
  X ^ 8 - 44 * X ^ 6 + 721 * X ^ 4 - 5214 * X ^ 2 + 14041

noncomputable def degreeTwelveFactor16 : ℤ[X] :=
  X ^ 16 - 88 * X ^ 14 + 3381 * X ^ 12 - 74074 * X ^ 10 +
    1012179 * X ^ 8 - 8833132 * X ^ 6 + 48076559 * X ^ 4 -
    149207586 * X ^ 2 + 202161961

theorem degreeTwelve_cycle15_resolvent_factorization :
    (C ℤ 15 - 2).comp degreeTwelveSpectralSubstitution =
      (9 - X ^ 2) * degreeTwelveFactor2a ^ 2 *
        degreeTwelveFactor4a ^ 2 * degreeTwelveFactor8a ^ 2 := by
  have hC := chebyshev_C_nat_eq_vietaLucasNat 15
  norm_num at hC
  rw [hC]
  norm_num [vietaLucasNat, degreeTwelveSpectralSubstitution,
    degreeTwelveFactor2a, degreeTwelveFactor4a, degreeTwelveFactor8a]
  ring_nf

theorem degreeTwelve_cycle15_value_factorization :
    (C ℤ 15).comp degreeTwelveSpectralSubstitution =
      -degreeTwelveFactor2c * degreeTwelveFactor4b *
        degreeTwelveFactor8c * degreeTwelveFactor16 := by
  have hC := chebyshev_C_nat_eq_vietaLucasNat 15
  norm_num at hC
  rw [hC]
  norm_num [vietaLucasNat, degreeTwelveSpectralSubstitution,
    degreeTwelveFactor2c, degreeTwelveFactor4b,
    degreeTwelveFactor8c, degreeTwelveFactor16]
  ring_nf

theorem degreeTwelve_cycle15_plus_two_factorization :
    (C ℤ 15 + 2).comp degreeTwelveSpectralSubstitution =
      -degreeTwelveFactor2b * degreeTwelveFactor2d ^ 2 *
        degreeTwelveFactor4c ^ 2 * degreeTwelveFactor8b ^ 2 := by
  have hC := chebyshev_C_nat_eq_vietaLucasNat 15
  norm_num at hC
  rw [hC]
  norm_num [vietaLucasNat, degreeTwelveSpectralSubstitution,
    degreeTwelveFactor2b, degreeTwelveFactor2d,
    degreeTwelveFactor4c, degreeTwelveFactor8b]
  ring_nf

theorem degreeTwelve_cycle60_resolvent_factorization :
    (C ℤ 60 - 2).comp degreeTwelveSpectralSubstitution =
      -(9 - X ^ 2) * degreeTwelveFactor2b *
        degreeTwelveFactor2a ^ 2 * degreeTwelveFactor2c ^ 2 *
        degreeTwelveFactor2d ^ 2 * degreeTwelveFactor4a ^ 2 *
        degreeTwelveFactor4b ^ 2 * degreeTwelveFactor4c ^ 2 *
        degreeTwelveFactor8b ^ 2 * degreeTwelveFactor8c ^ 2 *
        degreeTwelveFactor8a ^ 2 * degreeTwelveFactor16 ^ 2 := by
  let Z := (C ℤ 15).comp degreeTwelveSpectralSubstitution
  have hdecomp :
      (C ℤ 60 - 2).comp degreeTwelveSpectralSubstitution =
        Z ^ 2 * ((C ℤ 15 - 2).comp degreeTwelveSpectralSubstitution) *
          ((C ℤ 15 + 2).comp degreeTwelveSpectralSubstitution) := by
    rw [show (60 : ℤ) = 4 * 15 by norm_num, C_mul]
    have hC4 := chebyshev_C_nat_eq_vietaLucasNat 4
    norm_num at hC4
    rw [hC4]
    norm_num [vietaLucasNat, Z]
    ring
  rw [hdecomp]
  dsimp only [Z]
  rw [degreeTwelve_cycle15_value_factorization,
    degreeTwelve_cycle15_resolvent_factorization,
    degreeTwelve_cycle15_plus_two_factorization]
  ring

end Erdos85
