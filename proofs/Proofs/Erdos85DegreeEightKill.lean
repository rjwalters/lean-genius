import Proofs.Erdos85DegreeEightResultantFactorization
import Proofs.Erdos85UniformTraceSplitKill

/-!
# The degree-eight boundary kill

Degree eight is the first plateau degree blocked for the direct
nonsquare-certificate template: the conductor-two value `7 + 2 = 9 = 3²`
is a perfect square.  The uniform trace-split kill absorbs exactly one
designated square sector, and at `d = 8` the designated sector is the
rational conductor two (`μ₀ = -2`, `t = 3`, `3 ∤ 8`).

This file discharges the arithmetic hypothesis: every monic irreducible
rational factor of a boundary cycle polynomial *other than* `X + 2`
evaluates to a nonsquare at `7`:

* conductor one gives `X - 2` with value `5`, nonsquare;
* conductor two gives exactly the designated factor `X + 2`, excluded;
* conductors `3 ≤ ℓ ≤ 59` are handled by the resultant bridge and the
  native nonsquare certificate `R_ℓ(7)`.

Together with `¬ IsSquare 5` (for the principal trace) and `3 ∤ 8`, the
uniform trace-split kill destroys the exact boundary order
`59 = 8·7 + 3`.
-/

open Polynomial

namespace Erdos85

open SimpleGraph

noncomputable section

/-- **Resultant bridge on the algebraic closure.**  For a primitive `ℓ`-th
root of unity `z` in `AlgebraicClosure ℚ` with `ℓ ≥ 3`, the square of the
minimal-polynomial value at `7` of the real trace `z + z⁻¹` is the integral
cyclotomic resultant. -/
theorem minpoly_add_inv_eval_seven_mul_self {ℓ : ℕ} (h3 : 3 ≤ ℓ)
    {z : AlgebraicClosure ℚ} (hz : IsPrimitiveRoot z ℓ) :
    (minpoly ℚ (z + z⁻¹)).eval 7 * (minpoly ℚ (z + z⁻¹)).eval 7 =
      (degreeEightCyclotomicResultant ℓ : ℚ) := by
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
  have hpeer := primitiveTrace_minpoly_eval_seven_sq_eq_cyclotomic_resultant
    hz' h3
  rw [degreeEightCyclotomicResultant_rat_eq_intCast] at hpeer
  have hval : (L.val : L →ₐ[ℚ] AlgebraicClosure ℚ) (z' + z'⁻¹) = z + z⁻¹ := by
    rw [map_add, map_inv₀]
    rfl
  have hmp : minpoly ℚ (z' + z'⁻¹) = minpoly ℚ (z + z⁻¹) := by
    rw [← hval]
    exact (minpoly.algHom_eq L.val (fun a b h => Subtype.ext h) (z' + z'⁻¹)).symm
  rw [hmp] at hpeer
  exact hpeer

/-- The conductor value at `7` is nonsquare throughout the boundary range,
for conductors at least three. -/
theorem minpoly_add_inv_eval_seven_not_isSquare_of_three_le {ℓ : ℕ}
    (h3 : 3 ≤ ℓ) (h59 : ℓ ≤ 59) {z : AlgebraicClosure ℚ}
    (hz : IsPrimitiveRoot z ℓ) :
    ¬ IsSquare ((minpoly ℚ (z + z⁻¹)).eval 7) := by
  have hsq := minpoly_add_inv_eval_seven_mul_self h3 hz
  rw [degreeEightCyclotomicResultant_eq_sq ℓ h3 h59] at hsq
  push_cast at hsq
  set e : ℚ := (minpoly ℚ (z + z⁻¹)).eval 7 with he
  set c : ℚ := ((primitiveRealNormCandidateSeven ℓ : ℕ) : ℚ) with hc
  have hcases : e = c ∨ e = -c := by
    have hzero : (e - c) * (e + c) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp hzero with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hnotsq : ¬ IsSquare c := by
    rw [hc, Rat.isSquare_natCast_iff]
    exact primitiveRealNormCandidateSeven_not_isSquare h3 h59
  have hcpos : 0 < c := by
    rw [hc]
    exact_mod_cast Nat.pos_of_ne_zero
      (primitiveRealNormCandidateSeven_ne_zero h3 h59)
  rcases hcases with h | h
  · rw [h]
    exact hnotsq
  · rw [h]
    rintro ⟨r, hr⟩
    nlinarith [mul_self_nonneg r]

/-- `¬ IsSquare (5 : ℚ)`: the conductor-one endpoint. -/
theorem not_isSquare_five_rat : ¬ IsSquare (5 : ℚ) := by norm_num

/-- Conductor-one endpoint: the factor is `X - 2`, with value `5`. -/
theorem conductor_one_eval_seven_not_isSquare {z : AlgebraicClosure ℚ}
    (hz1 : z = 1) : ¬ IsSquare ((minpoly ℚ (z + z⁻¹)).eval 7) := by
  subst hz1
  have hmp : minpoly ℚ ((1 : AlgebraicClosure ℚ) + 1⁻¹) =
      Polynomial.X - Polynomial.C (2 : ℚ) := by
    rw [inv_one, show (1 : AlgebraicClosure ℚ) + 1 = 2 by norm_num,
      show (2 : AlgebraicClosure ℚ) = algebraMap ℚ (AlgebraicClosure ℚ) 2 by
        simp]
    exact minpoly.eq_X_sub_C (AlgebraicClosure ℚ) (2 : ℚ)
  have hval : (Polynomial.X - Polynomial.C (2 : ℚ)).eval 7 = 5 := by
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    norm_num
  rw [hmp, hval]
  exact not_isSquare_five_rat

/-- **The arithmetic hypothesis of the degree-eight kill.**  Every monic
irreducible rational factor of every relevant cycle polynomial in the
boundary range, other than the designated factor `X + 2`, evaluates to a
nonsquare at `7`. -/
theorem degreeEight_cycleFactor_eval_nonsquare_except :
    ∀ r : ℕ, 3 ≤ r → r ≤ 59 →
      ∀ f : Polynomial ℚ, f.Monic → Irreducible f →
        f ∣ (Chebyshev.C ℤ (r : ℤ) - 2).map (algebraMap ℤ ℚ) →
        f ≠ X - C (-2 : ℚ) → ¬ IsSquare (f.eval 7) := by
  intro r hr3 hr59 f hmonic hirr hdvd hne
  obtain ⟨z, ℓ, hdvdr, hℓ0, hpow, hord, hzr, hf⟩ :=
    cyclePoly_factor_conductor hr3 hmonic hirr hdvd
  subst hf
  have hℓ59 : ℓ ≤ 59 :=
    le_trans (Nat.le_of_dvd (by omega) hdvdr) hr59
  rcases Nat.lt_or_ge ℓ 3 with hlt | hge
  · have hℓ1 : 1 ≤ ℓ := Nat.one_le_iff_ne_zero.mpr hℓ0
    interval_cases ℓ
    · -- conductor one: `z = 1`, trace `2`, value `5`
      exact conductor_one_eval_seven_not_isSquare (orderOf_eq_one_iff.mp hord)
    · -- conductor two: the designated sector `X + 2`, excluded
      exfalso
      apply hne
      have hzsq : z ^ 2 = 1 := hpow
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
      subst hzneg
      rw [show ((-1 : AlgebraicClosure ℚ))⁻¹ = -1 by norm_num,
        show (-1 : AlgebraicClosure ℚ) + -1 = -2 by norm_num,
        show (-2 : AlgebraicClosure ℚ) =
            algebraMap ℚ (AlgebraicClosure ℚ) (-2) by simp]
      exact minpoly.eq_X_sub_C (AlgebraicClosure ℚ) (-2 : ℚ)
  · exact minpoly_add_inv_eval_seven_not_isSquare_of_three_le hge hℓ59
      (hord ▸ IsPrimitiveRoot.orderOf z)

/-- **The degree-eight boundary is killed.**  There is no `C₄`-free graph
of minimum degree at least `8` on exactly `59 = 8·7 + 3` vertices: the
plateau boundary at `d = 8` is destroyed by the unique-square-sector
trace split with `μ₀ = -2`, `t = 3`. -/
theorem degreeEight_boundary_killed
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : 8 ≤ G.minDegree)
    (hcard : Fintype.card V = 59) : False := by
  have hcard' : Fintype.card V = 8 * (8 - 1) + 3 := by norm_num [hcard]
  have hnsq : ¬ IsSquare (8 - 3 : ℕ) := by
    rw [show (8 - 3 : ℕ) = 5 from rfl]
    rintro ⟨k, hk⟩
    have hk5 : k ≤ 5 := by nlinarith
    interval_cases k <;> omega
  refine uniform_trace_split_kill G hfree (d := 8) (t := 3) (μ0 := -2)
    (by norm_num) (by decide) hmin hcard' (by norm_num) (by norm_num)
    (by norm_num) hnsq (by decide) ?_
  intro n h3 hn f hmonic hirr hdvd hne
  have hn59 : n ≤ 59 := by omega
  have h7 : ((8 : ℕ) : ℚ) - 1 = 7 := by norm_num
  rw [h7]
  exact degreeEight_cycleFactor_eval_nonsquare_except n h3 hn59
    f hmonic hirr hdvd hne

end

end Erdos85
