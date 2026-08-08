import Proofs.Erdos85DegreeEighteenResultantFactorization
import Proofs.Erdos85UniformTraceSplitKill

/-!
# The degree-18 boundary kill

Degree `18` is blocked for the direct nonsquare-certificate template: the
conductor-`6` value `R_6(17) = 16 = 4²` is a perfect square.  The
uniform trace-split kill absorbs exactly one designated square sector, and
at `d = 18` the designated sector is conductor `6` (`μ₀ = 1`,
`t = 4`, `4 ∤ 18`).

This file discharges the arithmetic hypothesis: every monic irreducible
rational factor of a boundary cycle polynomial *other than* the designated
factor `X - C 1` evaluates to a nonsquare at `17`:

* conductor one gives `X - 2` with value `15`, nonsquare;
* conductor two gives `X + 2` with value `19`, nonsquare;
* conductor `6` gives exactly the designated factor, excluded;
* the remaining conductors `3 ≤ ℓ ≤ 309` are handled by the resultant
  bridge and the native nonsquare certificate `R_ℓ(17)`.

Together with `¬ IsSquare 15` (for the principal trace) and `4 ∤ 18`,
the uniform trace-split kill destroys the exact boundary order
`309 = 18·17 + 3`.
-/

open Polynomial

namespace Erdos85

open SimpleGraph

noncomputable section

/-- **Resultant bridge on the algebraic closure** at `17`. -/
theorem minpoly_add_inv_eval_seventeen_mul_self {ℓ : ℕ} (h3 : 3 ≤ ℓ)
    {z : AlgebraicClosure ℚ} (hz : IsPrimitiveRoot z ℓ) :
    (minpoly ℚ (z + z⁻¹)).eval 17 * (minpoly ℚ (z + z⁻¹)).eval 17 =
      (degreeEighteenCyclotomicResultant ℓ : ℚ) := by
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
  have hpeer := primitiveTrace_minpoly_eval_seventeen_sq_eq_cyclotomic_resultant
    hz' h3
  rw [degreeEighteenCyclotomicResultant_rat_eq_intCast] at hpeer
  have hval : (L.val : L →ₐ[ℚ] AlgebraicClosure ℚ) (z' + z'⁻¹) = z + z⁻¹ := by
    rw [map_add, map_inv₀]
    rfl
  have hmp : minpoly ℚ (z' + z'⁻¹) = minpoly ℚ (z + z⁻¹) := by
    rw [← hval]
    exact (minpoly.algHom_eq L.val (fun a b h => Subtype.ext h) (z' + z'⁻¹)).symm
  rw [hmp] at hpeer
  exact hpeer

/-- The conductor value at `17` is nonsquare throughout the boundary range,
for conductors at least three other than the designated conductor `6`. -/
theorem minpoly_add_inv_eval_seventeen_not_isSquare_of_three_le {ℓ : ℕ}
    (h3 : 3 ≤ ℓ) (h309 : ℓ ≤ 309) (hne6 : ℓ ≠ 6)
    {z : AlgebraicClosure ℚ} (hz : IsPrimitiveRoot z ℓ) :
    ¬ IsSquare ((minpoly ℚ (z + z⁻¹)).eval 17) := by
  have hsq := minpoly_add_inv_eval_seventeen_mul_self h3 hz
  rw [degreeEighteenCyclotomicResultant_eq_sq ℓ h3 h309] at hsq
  push_cast at hsq
  set e : ℚ := (minpoly ℚ (z + z⁻¹)).eval 17 with he
  set c' : ℚ := ((primitiveRealNormCandidateSeventeen ℓ : ℕ) : ℚ) with hc
  have hcases : e = c' ∨ e = -c' := by
    have hzero : (e - c') * (e + c') = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp hzero with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hnotsq : ¬ IsSquare c' := by
    rw [hc, Rat.isSquare_natCast_iff]
    exact primitiveRealNormCandidateSeventeen_not_isSquare h3 h309 hne6
  have hcpos : 0 < c' := by
    rw [hc]
    exact_mod_cast Nat.pos_of_ne_zero
      (primitiveRealNormCandidateSeventeen_ne_zero h3 h309)
  rcases hcases with h | h
  · rw [h]
    exact hnotsq
  · rw [h]
    rintro ⟨r, hr⟩
    nlinarith [mul_self_nonneg r]

/-- The two rational conductor endpoints are nonsquare. -/
theorem not_isSquare_fifteen_rat : ¬ IsSquare (15 : ℚ) := by norm_num

theorem not_isSquare_nineteen_rat : ¬ IsSquare (19 : ℚ) := by norm_num

/-- Conductor-one endpoint: the factor is `X - 2`, with value `15`. -/
theorem conductor_one_eval_seventeen_not_isSquare {z : AlgebraicClosure ℚ}
    (hz1 : z = 1) : ¬ IsSquare ((minpoly ℚ (z + z⁻¹)).eval 17) := by
  subst hz1
  have hmp : minpoly ℚ ((1 : AlgebraicClosure ℚ) + 1⁻¹) =
      Polynomial.X - Polynomial.C (2 : ℚ) := by
    rw [inv_one, show (1 : AlgebraicClosure ℚ) + 1 = 2 by norm_num,
      show (2 : AlgebraicClosure ℚ) = algebraMap ℚ (AlgebraicClosure ℚ) 2 by
        simp]
    exact minpoly.eq_X_sub_C (AlgebraicClosure ℚ) (2 : ℚ)
  have hval : (Polynomial.X - Polynomial.C (2 : ℚ)).eval 17 = 15 := by
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    norm_num
  rw [hmp, hval]
  exact not_isSquare_fifteen_rat

/-- Conductor-two endpoint: the factor is `X + 2`, with value `19`. -/
theorem conductor_neg_one_eval_seventeen_not_isSquare {z : AlgebraicClosure ℚ}
    (hz2 : z = -1) : ¬ IsSquare ((minpoly ℚ (z + z⁻¹)).eval 17) := by
  subst hz2
  have hmp : minpoly ℚ ((-1 : AlgebraicClosure ℚ) + (-1)⁻¹) =
      Polynomial.X - Polynomial.C (-2 : ℚ) := by
    rw [show ((-1 : AlgebraicClosure ℚ))⁻¹ = -1 by norm_num,
      show (-1 : AlgebraicClosure ℚ) + -1 = -2 by norm_num,
      show (-2 : AlgebraicClosure ℚ) =
          algebraMap ℚ (AlgebraicClosure ℚ) (-2) by simp]
    exact minpoly.eq_X_sub_C (AlgebraicClosure ℚ) (-2 : ℚ)
  have hval : (Polynomial.X - Polynomial.C (-2 : ℚ)).eval 17 = 19 := by
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    norm_num
  rw [hmp, hval]
  exact not_isSquare_nineteen_rat

/-- **The arithmetic hypothesis of the degree-18 kill.**  Every monic
irreducible rational factor of every relevant cycle polynomial in the
boundary range, other than the designated factor `X - C 1`, evaluates
to a nonsquare at `17`. -/
theorem degreeEighteen_cycleFactor_eval_nonsquare_except :
    ∀ r : ℕ, 3 ≤ r → r ≤ 309 →
      ∀ f : Polynomial ℚ, f.Monic → Irreducible f →
        f ∣ (Chebyshev.C ℤ (r : ℤ) - 2).map (algebraMap ℤ ℚ) →
        f ≠ X - C (1 : ℚ) → ¬ IsSquare (f.eval 17) := by
  intro r hr3 hr309 f hmonic hirr hdvd hne
  obtain ⟨z, ℓ, hdvdr, hℓ0, hpow, hord, hzr, hf⟩ :=
    cyclePoly_factor_conductor hr3 hmonic hirr hdvd
  subst hf
  have hℓ309 : ℓ ≤ 309 :=
    le_trans (Nat.le_of_dvd (by omega) hdvdr) hr309
  rcases Nat.lt_or_ge ℓ 3 with hlt | hge
  · have hℓ1 : 1 ≤ ℓ := Nat.one_le_iff_ne_zero.mpr hℓ0
    interval_cases ℓ
    · exact conductor_one_eval_seventeen_not_isSquare (orderOf_eq_one_iff.mp hord)
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
      exact conductor_neg_one_eval_seventeen_not_isSquare hzneg
  · by_cases hℓdes : ℓ = 6
    · -- the designated conductor: the factor is `X - C 1`, excluded
      exfalso
      apply hne
      subst hℓdes
      have hz0 : z ≠ 0 := by
        intro h
        rw [h] at hpow
        norm_num at hpow
      have hz3ne : z ^ 3 ≠ 1 := by
        intro h
        have hdvd := orderOf_dvd_of_pow_eq_one h
        rw [hord] at hdvd
        omega
      have hz3 : z ^ 3 = -1 := by
        have hfac : (z ^ 3 - 1) * (z ^ 3 + 1) = 0 := by
          linear_combination hpow
        rcases mul_eq_zero.mp hfac with h | h
        · exact absurd (sub_eq_zero.mp h) hz3ne
        · exact eq_neg_of_add_eq_zero_left h
      have hz1ne : z ≠ -1 := by
        intro h
        have h2 : z ^ 2 = 1 := by
          rw [h]
          ring
        have hdvd := orderOf_dvd_of_pow_eq_one h2
        rw [hord] at hdvd
        omega
      have hquad : z ^ 2 - z + 1 = 0 := by
        have hfac : (z + 1) * (z ^ 2 - z + 1) = 0 := by
          linear_combination hz3
        rcases mul_eq_zero.mp hfac with h | h
        · exact absurd (eq_neg_of_add_eq_zero_left h) hz1ne
        · exact h
      have hzinv : z⁻¹ = 1 - z := by
        apply inv_eq_of_mul_eq_one_right
        linear_combination -hquad
      have hsum : z + z⁻¹ = 1 := by
        rw [hzinv]
        ring
      rw [hsum, show (1 : AlgebraicClosure ℚ) =
        algebraMap ℚ (AlgebraicClosure ℚ) 1 by simp]
      exact minpoly.eq_X_sub_C (AlgebraicClosure ℚ) (1 : ℚ)
    · exact minpoly_add_inv_eval_seventeen_not_isSquare_of_three_le hge hℓ309
        hℓdes (hord ▸ IsPrimitiveRoot.orderOf z)

/-- **The degree-18 boundary is killed.**  There is no `C₄`-free graph
of minimum degree at least `18` on exactly `309 = 18·17 + 3` vertices:
the plateau boundary at `d = 18` is destroyed by the unique-square-sector
trace split with `μ₀ = 1`, `t = 4`. -/
theorem degreeEighteen_boundary_killed
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : 18 ≤ G.minDegree)
    (hcard : Fintype.card V = 309) : False := by
  have hcard' : Fintype.card V = 18 * (18 - 1) + 3 := by norm_num [hcard]
  have hnsq : ¬ IsSquare (18 - 3 : ℕ) := by
    rw [show (18 - 3 : ℕ) = 15 from rfl]
    rintro ⟨k, hk⟩
    have hk' : k ≤ 15 := by nlinarith
    interval_cases k <;> omega
  refine uniform_trace_split_kill G hfree (d := 18) (t := 4) (μ0 := 1)
    (by norm_num) (by decide) hmin hcard' (by norm_num) (by norm_num)
    (by norm_num) hnsq (by decide) ?_
  intro n h3 hn f hmonic hirr hdvd hne
  have hn309 : n ≤ 309 := by omega
  have hc : ((18 : ℕ) : ℚ) - 1 = 17 := by norm_num
  rw [hc]
  exact degreeEighteen_cycleFactor_eval_nonsquare_except n h3 hn309
    f hmonic hirr hdvd hne

end

end Erdos85
