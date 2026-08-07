import Proofs.Erdos85DegreeTenResultantFactorization
import Proofs.Erdos85UniformTraceSplitKill

/-!
# The degree-10 boundary kill

Degree `10` is blocked for the direct nonsquare-certificate template: the
conductor-`4` value `R_4(9) = 9 = 3²` is a perfect square.  The
uniform trace-split kill absorbs exactly one designated square sector, and
at `d = 10` the designated sector is conductor `4` (`μ₀ = 0`,
`t = 3`, `3 ∤ 10`).

This file discharges the arithmetic hypothesis: every monic irreducible
rational factor of a boundary cycle polynomial *other than* the designated
factor `X - C 0` evaluates to a nonsquare at `9`:

* conductor one gives `X - 2` with value `7`, nonsquare;
* conductor two gives `X + 2` with value `11`, nonsquare;
* conductor `4` gives exactly the designated factor, excluded;
* the remaining conductors `3 ≤ ℓ ≤ 93` are handled by the resultant
  bridge and the native nonsquare certificate `R_ℓ(9)`.

Together with `¬ IsSquare 7` (for the principal trace) and `3 ∤ 10`,
the uniform trace-split kill destroys the exact boundary order
`93 = 10·9 + 3`.
-/

open Polynomial

namespace Erdos85

open SimpleGraph

noncomputable section

/-- **Resultant bridge on the algebraic closure** at `9`. -/
theorem minpoly_add_inv_eval_nine_mul_self {ℓ : ℕ} (h3 : 3 ≤ ℓ)
    {z : AlgebraicClosure ℚ} (hz : IsPrimitiveRoot z ℓ) :
    (minpoly ℚ (z + z⁻¹)).eval 9 * (minpoly ℚ (z + z⁻¹)).eval 9 =
      (degreeTenCyclotomicResultant ℓ : ℚ) := by
  haveI : NeZero ℓ := ⟨by omega⟩
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
    AlgebraicClosure.isAlgebraic ℚ
  haveI : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) :=
    Algebra.IsAlgebraic.isIntegral
  haveI : IsCyclotomicExtension {ℓ} ℚ (IntermediateField.adjoin ℚ
      ({z} : Set (AlgebraicClosure ℚ))) :=
    hz.intermediateField_adjoin_isCyclotomicExtension ℚ
  set L := IntermediateField.adjoin ℚ ({z} : Set (AlgebraicClosure ℚ)) with hL
  haveI : CharZero L :=
    charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  set z' : L := ⟨z, IntermediateField.mem_adjoin_simple_self ℚ z⟩ with hz'def
  have hz' : IsPrimitiveRoot z' ℓ := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff (B := IntermediateField ℚ
      (AlgebraicClosure ℚ)) (N := L)]
    exact hz
  have hpeer := primitiveTrace_minpoly_eval_nine_sq_eq_cyclotomic_resultant
    hz' h3
  rw [degreeTenCyclotomicResultant_rat_eq_intCast] at hpeer
  have hval : (L.val : L →ₐ[ℚ] AlgebraicClosure ℚ) (z' + z'⁻¹) = z + z⁻¹ := by
    rw [map_add, map_inv₀]
    rfl
  have hmp : minpoly ℚ (z' + z'⁻¹) = minpoly ℚ (z + z⁻¹) := by
    rw [← hval]
    exact (minpoly.algHom_eq L.val (fun a b h => Subtype.ext h) (z' + z'⁻¹)).symm
  rw [hmp] at hpeer
  exact hpeer

/-- The conductor value at `9` is nonsquare throughout the boundary range,
for conductors at least three other than the designated conductor `4`. -/
theorem minpoly_add_inv_eval_nine_not_isSquare_of_three_le {ℓ : ℕ}
    (h3 : 3 ≤ ℓ) (h93 : ℓ ≤ 93) (hne4 : ℓ ≠ 4)
    {z : AlgebraicClosure ℚ} (hz : IsPrimitiveRoot z ℓ) :
    ¬ IsSquare ((minpoly ℚ (z + z⁻¹)).eval 9) := by
  have hsq := minpoly_add_inv_eval_nine_mul_self h3 hz
  rw [degreeTenCyclotomicResultant_eq_sq ℓ h3 h93] at hsq
  push_cast at hsq
  set e : ℚ := (minpoly ℚ (z + z⁻¹)).eval 9 with he
  set c' : ℚ := ((primitiveRealNormCandidateNine ℓ : ℕ) : ℚ) with hc
  have hcases : e = c' ∨ e = -c' := by
    have hzero : (e - c') * (e + c') = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp hzero with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hnotsq : ¬ IsSquare c' := by
    rw [hc, Rat.isSquare_natCast_iff]
    exact primitiveRealNormCandidateNine_not_isSquare h3 h93 hne4
  have hcpos : 0 < c' := by
    rw [hc]
    exact_mod_cast Nat.pos_of_ne_zero
      (primitiveRealNormCandidateNine_ne_zero h3 h93)
  rcases hcases with h | h
  · rw [h]
    exact hnotsq
  · rw [h]
    rintro ⟨r, hr⟩
    nlinarith [mul_self_nonneg r]

/-- The two rational conductor endpoints are nonsquare. -/
theorem not_isSquare_seven_rat : ¬ IsSquare (7 : ℚ) := by norm_num

theorem not_isSquare_eleven_rat : ¬ IsSquare (11 : ℚ) := by norm_num

/-- Conductor-one endpoint: the factor is `X - 2`, with value `7`. -/
theorem conductor_one_eval_nine_not_isSquare {z : AlgebraicClosure ℚ}
    (hz1 : z = 1) : ¬ IsSquare ((minpoly ℚ (z + z⁻¹)).eval 9) := by
  subst hz1
  have hmp : minpoly ℚ ((1 : AlgebraicClosure ℚ) + 1⁻¹) =
      Polynomial.X - Polynomial.C (2 : ℚ) := by
    rw [inv_one, show (1 : AlgebraicClosure ℚ) + 1 = 2 by norm_num,
      show (2 : AlgebraicClosure ℚ) = algebraMap ℚ (AlgebraicClosure ℚ) 2 by
        simp]
    exact minpoly.eq_X_sub_C (AlgebraicClosure ℚ) (2 : ℚ)
  have hval : (Polynomial.X - Polynomial.C (2 : ℚ)).eval 9 = 7 := by
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    norm_num
  rw [hmp, hval]
  exact not_isSquare_seven_rat

/-- Conductor-two endpoint: the factor is `X + 2`, with value `11`. -/
theorem conductor_neg_one_eval_nine_not_isSquare {z : AlgebraicClosure ℚ}
    (hz2 : z = -1) : ¬ IsSquare ((minpoly ℚ (z + z⁻¹)).eval 9) := by
  subst hz2
  have hmp : minpoly ℚ ((-1 : AlgebraicClosure ℚ) + (-1)⁻¹) =
      Polynomial.X - Polynomial.C (-2 : ℚ) := by
    rw [show ((-1 : AlgebraicClosure ℚ))⁻¹ = -1 by norm_num,
      show (-1 : AlgebraicClosure ℚ) + -1 = -2 by norm_num,
      show (-2 : AlgebraicClosure ℚ) =
          algebraMap ℚ (AlgebraicClosure ℚ) (-2) by simp]
    exact minpoly.eq_X_sub_C (AlgebraicClosure ℚ) (-2 : ℚ)
  have hval : (Polynomial.X - Polynomial.C (-2 : ℚ)).eval 9 = 11 := by
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    norm_num
  rw [hmp, hval]
  exact not_isSquare_eleven_rat

/-- **The arithmetic hypothesis of the degree-10 kill.**  Every monic
irreducible rational factor of every relevant cycle polynomial in the
boundary range, other than the designated factor `X - C 0`, evaluates
to a nonsquare at `9`. -/
theorem degreeTen_cycleFactor_eval_nonsquare_except :
    ∀ r : ℕ, 3 ≤ r → r ≤ 93 →
      ∀ f : Polynomial ℚ, f.Monic → Irreducible f →
        f ∣ (Chebyshev.C ℤ (r : ℤ) - 2).map (algebraMap ℤ ℚ) →
        f ≠ X - C (0 : ℚ) → ¬ IsSquare (f.eval 9) := by
  intro r hr3 hr93 f hmonic hirr hdvd hne
  obtain ⟨z, ℓ, hdvdr, hℓ0, hpow, hord, hzr, hf⟩ :=
    cyclePoly_factor_conductor hr3 hmonic hirr hdvd
  subst hf
  have hℓ93 : ℓ ≤ 93 :=
    le_trans (Nat.le_of_dvd (by omega) hdvdr) hr93
  rcases Nat.lt_or_ge ℓ 3 with hlt | hge
  · have hℓ1 : 1 ≤ ℓ := Nat.one_le_iff_ne_zero.mpr hℓ0
    interval_cases ℓ
    · exact conductor_one_eval_nine_not_isSquare (orderOf_eq_one_iff.mp hord)
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
      exact conductor_neg_one_eval_nine_not_isSquare hzneg
  · by_cases hℓdes : ℓ = 4
    · -- the designated conductor: the factor is `X - C 0`, excluded
      exfalso
      apply hne
      subst hℓdes
      have hz0 : z ≠ 0 := by
        intro h
        rw [h] at hpow
        norm_num at hpow
      have hz2ne : z ^ 2 ≠ 1 := by
        intro h
        have hdvd := orderOf_dvd_of_pow_eq_one h
        rw [hord] at hdvd
        omega
      have hz2 : z ^ 2 = -1 := by
        have hfac : (z ^ 2 - 1) * (z ^ 2 + 1) = 0 := by
          linear_combination hpow
        rcases mul_eq_zero.mp hfac with h | h
        · exact absurd (sub_eq_zero.mp h) hz2ne
        · exact eq_neg_of_add_eq_zero_left h
      have hzinv : z⁻¹ = -z := by
        apply inv_eq_of_mul_eq_one_right
        rw [mul_neg, ← pow_two, hz2, neg_neg]
      have hsum : z + z⁻¹ = 0 := by
        rw [hzinv]
        ring
      rw [hsum, show (0 : AlgebraicClosure ℚ) =
        algebraMap ℚ (AlgebraicClosure ℚ) 0 by simp]
      exact minpoly.eq_X_sub_C (AlgebraicClosure ℚ) (0 : ℚ)
    · exact minpoly_add_inv_eval_nine_not_isSquare_of_three_le hge hℓ93
        hℓdes (hord ▸ IsPrimitiveRoot.orderOf z)

/-- **The degree-10 boundary is killed.**  There is no `C₄`-free graph
of minimum degree at least `10` on exactly `93 = 10·9 + 3` vertices:
the plateau boundary at `d = 10` is destroyed by the unique-square-sector
trace split with `μ₀ = 0`, `t = 3`. -/
theorem degreeTen_boundary_killed
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : 10 ≤ G.minDegree)
    (hcard : Fintype.card V = 93) : False := by
  have hcard' : Fintype.card V = 10 * (10 - 1) + 3 := by norm_num [hcard]
  have hnsq : ¬ IsSquare (10 - 3 : ℕ) := by
    rw [show (10 - 3 : ℕ) = 7 from rfl]
    rintro ⟨k, hk⟩
    have hk' : k ≤ 7 := by nlinarith
    interval_cases k <;> omega
  refine uniform_trace_split_kill G hfree (d := 10) (t := 3) (μ0 := 0)
    (by norm_num) (by decide) hmin hcard' (by norm_num) (by norm_num)
    (by norm_num) hnsq (by decide) ?_
  intro n h3 hn f hmonic hirr hdvd hne
  have hn93 : n ≤ 93 := by omega
  have hc : ((10 : ℕ) : ℚ) - 1 = 9 := by norm_num
  rw [hc]
  exact degreeTen_cycleFactor_eval_nonsquare_except n h3 hn93
    f hmonic hirr hdvd hne

end

end Erdos85
