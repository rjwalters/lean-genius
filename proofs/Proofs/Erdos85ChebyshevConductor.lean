import Mathlib.RingTheory.Polynomial.Dickson
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.GroupTheory.OrderOfElement

/-!
# Chebyshev conductor identification for the cycle polynomial

The defect-cycle characteristic polynomial appearing at the exact even
second-order boundary is `Chebyshev.C ℤ r - 2`.  This file identifies its
roots over `AlgebraicClosure ℚ`: every root `μ` is of the form `z + z⁻¹`
for an `r`-th root of unity `z`, so every monic irreducible rational factor
of the mapped cycle polynomial is the minimal polynomial of `z + z⁻¹` with
`orderOf z` a conductor dividing `r`.  The engine is the trace identity
`C_r(z + z⁻¹) = z^r + z⁻ʳ`, available through the Dickson polynomial bridge,
together with `w + w⁻¹ = 2 → (w - 1)² = 0 → w = 1`.
-/

open Polynomial

namespace Erdos85

noncomputable section

variable {K : Type*} [Field K]

/-- Trace identity: the rescaled Chebyshev polynomial evaluates on
`z + z⁻¹` to `z ^ r + z⁻¹ ^ r`. -/
theorem chebyshev_C_eval_add_inv (r : ℕ) {z : K} (hz : z ≠ 0) :
    (Chebyshev.C K (r : ℤ)).eval (z + z⁻¹) = z ^ r + z⁻¹ ^ r := by
  rw [← Polynomial.dickson_one_one_eq_chebyshev_C K r]
  exact Polynomial.dickson_one_one_eval_add_inv z z⁻¹ (mul_inv_cancel₀ hz) r

/-- Evaluation of the mapped integral cycle polynomial in any field. -/
theorem cycle_chebyshev_map_eval (r : ℕ) (μ : K) :
    ((Chebyshev.C ℤ (r : ℤ) - 2).map (algebraMap ℤ K)).eval μ =
      (Chebyshev.C K (r : ℤ)).eval μ - 2 := by
  simp [Polynomial.map_sub]

/-- In a field, `w + w⁻¹ = 2` forces `w = 1` (the square `(w - 1)² = 0`
collapses). -/
theorem eq_one_of_add_inv_eq_two {w : K} (hw : w ≠ 0) (h : w + w⁻¹ = 2) :
    w = 1 := by
  have hsq : w * w + 1 = 2 * w := by
    calc w * w + 1 = (w + w⁻¹) * w := by rw [add_mul, inv_mul_cancel₀ hw]
      _ = 2 * w := by rw [h]
  have hzero : (w - 1) ^ 2 = 0 := by linear_combination hsq
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hzero)

/-- A root of the quadratic `Z² - μZ + 1` is nonzero. -/
theorem quadratic_root_ne_zero {μ z : K} (hz : z * z - μ * z + 1 = 0) :
    z ≠ 0 := by
  intro h0
  rw [h0] at hz
  simp at hz

/-- A root of the quadratic `Z² - μZ + 1` writes `μ` as `z + z⁻¹`. -/
theorem quadratic_root_add_inv {μ z : K} (hz : z * z - μ * z + 1 = 0) :
    μ = z + z⁻¹ := by
  have hone : (μ - z) * z = 1 := by linear_combination -hz
  have hinv : μ - z = z⁻¹ := eq_inv_of_mul_eq_one_left hone
  rw [← hinv]
  ring

/-- **Cycle-polynomial root dichotomy.**  For `μ = z + z⁻¹` (packaged via
the quadratic relation), the Chebyshev value `C_r(μ)` equals `2` exactly
when `z` is an `r`-th root of unity. -/
theorem chebyshev_C_eval_eq_two_iff (r : ℕ) {μ z : K}
    (hz : z * z - μ * z + 1 = 0) :
    (Chebyshev.C K (r : ℤ)).eval μ = 2 ↔ z ^ r = 1 := by
  have hz0 : z ≠ 0 := quadratic_root_ne_zero hz
  rw [quadratic_root_add_inv hz, chebyshev_C_eval_add_inv r hz0]
  constructor
  · intro h
    refine eq_one_of_add_inv_eq_two (pow_ne_zero r hz0) ?_
    rw [← inv_pow]
    exact h
  · intro h
    have hinv : z⁻¹ ^ r = 1 := by rw [inv_pow, h, inv_one]
    rw [h, hinv]
    norm_num

/-- `aeval` form of the dichotomy over the algebraic closure, in the
vocabulary of the boundary-orbit package. -/
theorem cyclePoly_sub_two_root_iff {r : ℕ} (μ z : AlgebraicClosure ℚ)
    (hz : z * z - μ * z + 1 = 0) :
    Polynomial.aeval μ (Chebyshev.C ℤ (r : ℤ)) = 2 ↔ z ^ r = 1 := by
  rw [Polynomial.Chebyshev.aeval_C]
  exact chebyshev_C_eval_eq_two_iff r hz

/-- Quadratic splitting: over the algebraic closure every `μ` is `z + z⁻¹`
for some root `z` of `Z² - μZ + 1`. -/
theorem exists_quadratic_split (μ : AlgebraicClosure ℚ) :
    ∃ z : AlgebraicClosure ℚ, z * z - μ * z + 1 = 0 := by
  obtain ⟨z, hzroot⟩ := IsAlgClosed.exists_root
      (Polynomial.C (1 : AlgebraicClosure ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (-μ) * Polynomial.X + Polynomial.C 1)
      (by rw [Polynomial.degree_quadratic one_ne_zero]; decide)
  rw [Polynomial.IsRoot] at hzroot
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X] at hzroot
  exact ⟨z, by linear_combination hzroot⟩

/-- **Root-of-unity structure.**  Every root of the mapped cycle polynomial
`C_r - 2` over the algebraic closure is `z + z⁻¹` for an `r`-th root of
unity `z`. -/
theorem exists_root_of_unity_of_cyclePoly_root {r : ℕ}
    (μ : AlgebraicClosure ℚ)
    (hroot : ((Chebyshev.C ℤ (r : ℤ) - 2).map
      (algebraMap ℤ (AlgebraicClosure ℚ))).eval μ = 0) :
    ∃ z : AlgebraicClosure ℚ, z ^ r = 1 ∧ μ = z + z⁻¹ := by
  obtain ⟨z, hz⟩ := exists_quadratic_split μ
  have heval : (Chebyshev.C (AlgebraicClosure ℚ) (r : ℤ)).eval μ = 2 := by
    have h : (Chebyshev.C (AlgebraicClosure ℚ) (r : ℤ)).eval μ - 2 = 0 :=
      (cycle_chebyshev_map_eval r μ).symm.trans hroot
    exact sub_eq_zero.mp h
  exact ⟨z, (chebyshev_C_eval_eq_two_iff r hz).mp heval,
    quadratic_root_add_inv hz⟩

/-- Mapping an integral polynomial first to `ℚ` and then to the algebraic
closure gives the same evaluation as mapping it directly. -/
theorem aeval_intMap_eq_eval_map_closure
    (P : Polynomial ℤ) (μ : AlgebraicClosure ℚ) :
    Polynomial.aeval μ (P.map (algebraMap ℤ ℚ)) =
      (P.map (algebraMap ℤ (AlgebraicClosure ℚ))).eval μ := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_map,
    ← Polynomial.eval₂_eq_eval_map,
    IsScalarTower.algebraMap_eq ℤ ℚ (AlgebraicClosure ℚ)]

/-- Conductor extraction: an `r`-th root of unity with `r ≠ 0` has a
well-defined order (its conductor) dividing `r`. -/
theorem exists_conductor_of_pow_eq_one {r : ℕ} (hr : 1 ≤ r)
    {z : AlgebraicClosure ℚ} (hz : z ^ r = 1) :
    ∃ ℓ : ℕ, ℓ ∣ r ∧ ℓ ≠ 0 ∧ z ^ ℓ = 1 ∧ orderOf z = ℓ := by
  refine ⟨orderOf z, orderOf_dvd_of_pow_eq_one hz, ?_,
    pow_orderOf_eq_one z, rfl⟩
  have hfin : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.mpr ⟨r, hr, hz⟩
  exact (orderOf_pos_iff.mpr hfin).ne'

/-- **Chebyshev conductor identification.**  Every monic irreducible
rational factor of the mapped cycle polynomial `C_r - 2` is the minimal
polynomial of `z + z⁻¹` for an `r`-th root of unity `z` — a real cyclotomic
polynomial. -/
theorem chebyshev_conductor_identification {r : ℕ} {f : Polynomial ℚ}
    (hmonic : f.Monic) (hirr : Irreducible f)
    (hdvd : f ∣ (Chebyshev.C ℤ (r : ℤ) - 2).map (algebraMap ℤ ℚ)) :
    ∃ z : AlgebraicClosure ℚ, z ^ r = 1 ∧ f = minpoly ℚ (z + z⁻¹) := by
  obtain ⟨μ, hμroot⟩ := IsAlgClosed.exists_aeval_eq_zero_of_injective
    (AlgebraicClosure ℚ) (algebraMap ℚ (AlgebraicClosure ℚ)).injective f
    hirr.degree_pos.ne'
  obtain ⟨g, hg⟩ := hdvd
  have hcycle : ((Chebyshev.C ℤ (r : ℤ) - 2).map
      (algebraMap ℤ (AlgebraicClosure ℚ))).eval μ = 0 := by
    rw [← aeval_intMap_eq_eval_map_closure, hg, map_mul, hμroot, zero_mul]
  obtain ⟨z, hzr, hμz⟩ := exists_root_of_unity_of_cyclePoly_root μ hcycle
  refine ⟨z, hzr, ?_⟩
  rw [← hμz]
  exact minpoly.eq_of_irreducible_of_monic hirr hμroot hmonic

/-- **Conductor table form.**  Every monic irreducible rational factor of
the mapped cycle polynomial `C_r - 2` (with `r ≥ 3`) is the minimal
polynomial of `z + z⁻¹` where `z` is a root of unity whose order — the
conductor `ℓ` — divides `r`.  This is the exact indexing used by the norm
certificate table. -/
theorem cyclePoly_factor_conductor {r : ℕ} (hr : 3 ≤ r) {f : Polynomial ℚ}
    (hmonic : f.Monic) (hirr : Irreducible f)
    (hdvd : f ∣ (Chebyshev.C ℤ (r : ℤ) - 2).map (algebraMap ℤ ℚ)) :
    ∃ (z : AlgebraicClosure ℚ) (ℓ : ℕ), ℓ ∣ r ∧ ℓ ≠ 0 ∧ z ^ ℓ = 1 ∧
      orderOf z = ℓ ∧ z ^ r = 1 ∧ f = minpoly ℚ (z + z⁻¹) := by
  obtain ⟨z, hzr, hf⟩ := chebyshev_conductor_identification hmonic hirr hdvd
  obtain ⟨ℓ, hdvd', hne, hpow, hord⟩ :=
    exists_conductor_of_pow_eq_one (by omega) hzr
  exact ⟨z, ℓ, hdvd', hne, hpow, hord, hzr, hf⟩

end

end Erdos85
