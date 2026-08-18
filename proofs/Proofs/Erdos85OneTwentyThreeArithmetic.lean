import Proofs.Erdos85OneTwentyThreeResultantFactorization
import Proofs.Erdos85ChebyshevConductor

/-!
# Nonsquare cycle factors at scalar 123

The conductor-one factor `X - 2` is the designated square sector and is
explicitly excluded.  Every other monic irreducible factor of a relevant
cycle Chebyshev polynomial evaluates to a nonsquare at `123`.
-/

open Polynomial

namespace Erdos85

noncomputable section

theorem not_isSquare_oneTwentyFive_rat : ¬ IsSquare (125 : ℚ) := by
  norm_num

/-- Conductor two has trace `-2`, hence scalar-123 value `125`. -/
theorem conductor_neg_one_eval_oneTwentyThree_not_isSquare
    {z : AlgebraicClosure ℚ} (hz2 : z = -1) :
    ¬ IsSquare ((minpoly ℚ (z + z⁻¹)).eval 123) := by
  subst hz2
  have hmp : minpoly ℚ ((-1 : AlgebraicClosure ℚ) + (-1)⁻¹) =
      Polynomial.X - Polynomial.C (-2 : ℚ) := by
    rw [show ((-1 : AlgebraicClosure ℚ))⁻¹ = -1 by norm_num,
      show (-1 : AlgebraicClosure ℚ) + -1 = -2 by norm_num,
      show (-2 : AlgebraicClosure ℚ) =
          algebraMap ℚ (AlgebraicClosure ℚ) (-2) by simp]
    exact minpoly.eq_X_sub_C (AlgebraicClosure ℚ) (-2 : ℚ)
  have hval : (Polynomial.X - Polynomial.C (-2 : ℚ)).eval 123 = 125 := by
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    norm_num
  rw [hmp, hval]
  exact not_isSquare_oneTwentyFive_rat

/-- Conductor one is exactly the designated factor `X - 2`. -/
theorem minpoly_add_inv_eq_X_sub_two_of_order_one
    {z : AlgebraicClosure ℚ} (hz1 : z = 1) :
    minpoly ℚ (z + z⁻¹) = Polynomial.X - Polynomial.C (2 : ℚ) := by
  subst hz1
  rw [inv_one, show (1 : AlgebraicClosure ℚ) + 1 = 2 by norm_num,
    show (2 : AlgebraicClosure ℚ) =
        algebraMap ℚ (AlgebraicClosure ℚ) 2 by simp]
  exact minpoly.eq_X_sub_C (AlgebraicClosure ℚ) (2 : ℚ)

/-- **Scalar-123 arithmetic hypothesis for residual trace escape.**
Every monic irreducible cycle factor except `X - 2` evaluates to a
nonsquare throughout the full parent-boundary range. -/
theorem oneTwentyThree_cycleFactor_eval_nonsquare_except_two :
    ∀ r : ℕ, 3 ≤ r → r ≤ 15255 →
      ∀ f : Polynomial ℚ, f.Monic → Irreducible f →
        f ∣ (Chebyshev.C ℤ (r : ℤ) - 2).map (algebraMap ℤ ℚ) →
        f ≠ Polynomial.X - Polynomial.C (2 : ℚ) →
        ¬ IsSquare (f.eval 123) := by
  intro r hr3 hrmax f hmonic hirr hdvd hfne
  obtain ⟨z, ℓ, hdvdr, hℓ0, hpow, hord, hzr, hf⟩ :=
    cyclePoly_factor_conductor hr3 hmonic hirr hdvd
  subst hf
  have hℓmax : ℓ ≤ 15255 :=
    le_trans (Nat.le_of_dvd (by omega) hdvdr) hrmax
  rcases Nat.lt_or_ge ℓ 3 with hlt | hge
  · have hℓ1 : 1 ≤ ℓ := Nat.one_le_iff_ne_zero.mpr hℓ0
    interval_cases ℓ
    · exfalso
      apply hfne
      exact minpoly_add_inv_eq_X_sub_two_of_order_one
        (orderOf_eq_one_iff.mp hord)
    · have hzsq : z ^ 2 = 1 := hpow
      have hzne1 : z ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hord
        omega
      have hzneg : z = -1 := by
        have hfactor : (z - 1) * (z + 1) = 0 := by
          linear_combination hzsq
        rcases mul_eq_zero.mp hfactor with h | h
        · exact absurd (sub_eq_zero.mp h) hzne1
        · exact eq_neg_of_add_eq_zero_left h
      exact conductor_neg_one_eval_oneTwentyThree_not_isSquare hzneg
  · exact minpoly_add_inv_eval_oneTwentyThree_not_isSquare hge hℓmax
      (hord ▸ IsPrimitiveRoot.orderOf z)

end

end Erdos85
