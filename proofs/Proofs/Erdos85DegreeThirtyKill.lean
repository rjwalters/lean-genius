import Proofs.Erdos85DegreeThirtyResultantFactorization
import Proofs.Erdos85DegreeThirtyReduction

/-!
# The degree-thirty boundary kill

This file composes the completed pipeline:

* the conductor identification (`Erdos85ChebyshevConductor`): every monic
  irreducible rational factor of the cycle polynomial `C_r - 2` is the
  minimal polynomial of `z + z⁻¹` for a root of unity `z` of order `ℓ ∣ r`;
* the resultant norm bridge (`Erdos85DegreeThirtyResultantFactorization`):
  for `ℓ ≥ 3` the square of that factor's value at `29` is the integral
  cyclotomic resultant `Res_ℓ` against the quadratic `29X - X² - 1`;
* the strong-induction cancellation: `Res_ℓ = candidate(ℓ)²` in the boundary
  range, with `candidate(ℓ)` the native-certified nonsquare;
* the endpoint conductors `ℓ = 1, 2` give values `27` and `31`, both
  nonsquare.

Together these discharge the arithmetic hypothesis of the degree-thirty
reduction, killing the exact boundary order `873 = 30·29 + 3`.

The neighbouring degree `d = 26` is *not* amenable to this template:
there the conductor-four norm is `R_4(25) = 25 = 5²`, a perfect square,
so the nonsquare certificate fails at cycle lengths divisible by four.
Degree thirty is the next boundary the template kills.
-/

open Polynomial

namespace Erdos85

open SimpleGraph

noncomputable section

/-- **Resultant bridge on the algebraic closure.**  For a primitive `ℓ`-th
root of unity `z` in `AlgebraicClosure ℚ` with `ℓ ≥ 3`, the square of the
minimal-polynomial value at `29` of the real trace `z + z⁻¹` is the integral
cyclotomic resultant. -/
theorem minpoly_add_inv_eval_twentyNine_mul_self {ℓ : ℕ} (h3 : 3 ≤ ℓ)
    {z : AlgebraicClosure ℚ} (hz : IsPrimitiveRoot z ℓ) :
    (minpoly ℚ (z + z⁻¹)).eval 29 * (minpoly ℚ (z + z⁻¹)).eval 29 =
      (degreeThirtyCyclotomicResultant ℓ : ℚ) := by
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
  have hpeer := primitiveTrace_minpoly_eval_twentyNine_sq_eq_cyclotomic_resultant
    hz' h3
  rw [degreeThirtyCyclotomicResultant_rat_eq_intCast] at hpeer
  have hval : (L.val : L →ₐ[ℚ] AlgebraicClosure ℚ) (z' + z'⁻¹) = z + z⁻¹ := by
    rw [map_add, map_inv₀]
    rfl
  have hmp : minpoly ℚ (z' + z'⁻¹) = minpoly ℚ (z + z⁻¹) := by
    rw [← hval]
    exact (minpoly.algHom_eq L.val (fun a b h => Subtype.ext h) (z' + z'⁻¹)).symm
  rw [hmp] at hpeer
  exact hpeer

/-- The conductor value at `29` is nonsquare throughout the boundary range,
for conductors at least three. -/
theorem minpoly_add_inv_eval_twentyNine_not_isSquare_of_three_le {ℓ : ℕ}
    (h3 : 3 ≤ ℓ) (h873 : ℓ ≤ 873) {z : AlgebraicClosure ℚ}
    (hz : IsPrimitiveRoot z ℓ) :
    ¬ IsSquare ((minpoly ℚ (z + z⁻¹)).eval 29) := by
  have hsq := minpoly_add_inv_eval_twentyNine_mul_self h3 hz
  rw [degreeThirtyCyclotomicResultant_eq_sq ℓ h3 h873] at hsq
  push_cast at hsq
  set e : ℚ := (minpoly ℚ (z + z⁻¹)).eval 29 with he
  set c : ℚ := ((primitiveRealNormCandidateTwentyNine ℓ : ℕ) : ℚ) with hc
  have hcases : e = c ∨ e = -c := by
    have hzero : (e - c) * (e + c) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp hzero with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hnotsq : ¬ IsSquare c := by
    rw [hc, Rat.isSquare_natCast_iff]
    exact primitiveRealNormCandidateTwentyNine_not_isSquare h3 h873
  have hcpos : 0 < c := by
    rw [hc]
    exact_mod_cast Nat.pos_of_ne_zero
      (primitiveRealNormCandidateTwentyNine_ne_zero h3 h873)
  rcases hcases with h | h
  · rw [h]
    exact hnotsq
  · rw [h]
    rintro ⟨r, hr⟩
    nlinarith [mul_self_nonneg r]

/-- `¬ IsSquare (27 : ℚ)` and `¬ IsSquare (31 : ℚ)`: the two rational
conductor endpoints. -/
theorem not_isSquare_twentySeven_rat : ¬ IsSquare (27 : ℚ) := by norm_num

theorem not_isSquare_thirtyOne_rat : ¬ IsSquare (31 : ℚ) := by norm_num

/-- Conductor-one endpoint: the factor is `X - 2`, with value `27`. -/
theorem conductor_one_eval_twentyNine_not_isSquare {z : AlgebraicClosure ℚ}
    (hz1 : z = 1) : ¬ IsSquare ((minpoly ℚ (z + z⁻¹)).eval 29) := by
  subst hz1
  have hmp : minpoly ℚ ((1 : AlgebraicClosure ℚ) + 1⁻¹) =
      Polynomial.X - Polynomial.C (2 : ℚ) := by
    rw [inv_one, show (1 : AlgebraicClosure ℚ) + 1 = 2 by norm_num,
      show (2 : AlgebraicClosure ℚ) = algebraMap ℚ (AlgebraicClosure ℚ) 2 by
        simp]
    exact minpoly.eq_X_sub_C (AlgebraicClosure ℚ) (2 : ℚ)
  have hval : (Polynomial.X - Polynomial.C (2 : ℚ)).eval 29 = 27 := by
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    norm_num
  rw [hmp, hval]
  exact not_isSquare_twentySeven_rat

/-- Conductor-two endpoint: the factor is `X + 2`, with value `31`. -/
theorem conductor_neg_one_eval_twentyNine_not_isSquare {z : AlgebraicClosure ℚ}
    (hz2 : z = -1) : ¬ IsSquare ((minpoly ℚ (z + z⁻¹)).eval 29) := by
  subst hz2
  have hmp : minpoly ℚ ((-1 : AlgebraicClosure ℚ) + (-1)⁻¹) =
      Polynomial.X - Polynomial.C (-2 : ℚ) := by
    rw [show ((-1 : AlgebraicClosure ℚ))⁻¹ = -1 by norm_num,
      show (-1 : AlgebraicClosure ℚ) + -1 = -2 by norm_num,
      show (-2 : AlgebraicClosure ℚ) =
          algebraMap ℚ (AlgebraicClosure ℚ) (-2) by simp]
    exact minpoly.eq_X_sub_C (AlgebraicClosure ℚ) (-2 : ℚ)
  have hval : (Polynomial.X - Polynomial.C (-2 : ℚ)).eval 29 = 31 := by
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    norm_num
  rw [hmp, hval]
  exact not_isSquare_thirtyOne_rat

/-- **The arithmetic hypothesis of the degree-thirty reduction.**  Every
monic irreducible rational factor of every relevant cycle polynomial in the
boundary range evaluates to a nonsquare at `29`. -/
theorem degreeThirty_cycleFactor_eval_nonsquare :
    ∀ r : ℕ, 3 ≤ r → r ≤ 873 →
      ∀ f : Polynomial ℚ, f.Monic → Irreducible f →
        f ∣ (Chebyshev.C ℤ (r : ℤ) - 2).map (algebraMap ℤ ℚ) →
        ¬ IsSquare (f.eval 29) := by
  intro r hr3 hr873 f hmonic hirr hdvd
  obtain ⟨z, ℓ, hdvdr, hℓ0, hpow, hord, hzr, hf⟩ :=
    cyclePoly_factor_conductor hr3 hmonic hirr hdvd
  subst hf
  have hℓ873 : ℓ ≤ 873 :=
    le_trans (Nat.le_of_dvd (by omega) hdvdr) hr873
  rcases Nat.lt_or_ge ℓ 3 with hlt | hge
  · have hℓ1 : 1 ≤ ℓ := Nat.one_le_iff_ne_zero.mpr hℓ0
    interval_cases ℓ
    · -- conductor one: `z = 1`, trace `2`, value `27`
      exact conductor_one_eval_twentyNine_not_isSquare (orderOf_eq_one_iff.mp hord)
    · -- conductor two: `z = -1`, trace `-2`, value `31`
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
      exact conductor_neg_one_eval_twentyNine_not_isSquare hzneg
  · exact minpoly_add_inv_eval_twentyNine_not_isSquare_of_three_le hge hℓ873
      (hord ▸ IsPrimitiveRoot.orderOf z)

/-- **The degree-thirty boundary is killed.**  There is no `C₄`-free
graph of minimum degree at least `30` on exactly `873 = 30·29 + 3` vertices:
the plateau boundary for the Erdős–85 girth problem at `d = 30` is
arithmetically obstructed. -/
theorem degreeThirty_boundary_killed
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : 30 ≤ G.minDegree)
    (hcard : Fintype.card V = 873) : False :=
  false_of_degreeThirty_cycleFactor_eval_nonsquare
    degreeThirty_cycleFactor_eval_nonsquare G hfree hmin hcard

end

end Erdos85
