import Mathlib
import Proofs.SphericalLawOfSines

/-
# Unsquared spherical law of sines: the true proportion of sines

The parent file `SphericalLawOfSines` proves the spherical law of sines in **squared**
ratio form (`spherical_law_of_sines_all_sq`):

  sin²(a)/sin²(α) = sin²(b)/sin²(β) = sin²(c)/sin²(γ),

where `a, b, c` are the side arc-lengths and `α, β, γ` the opposite dihedral (interior)
angles of a spherical triangle with unit-vector vertices `A, B, C`.

This is one square-root short of the textbook statement.  The squared form alone does not
give the genuine proportion `sin(a)/sin(α) = sin(b)/sin(β)`: in principle an equality of
squares `x² = y²` only yields `x = ±y`.  Here the sign ambiguity is killed by a geometric
fact: **every side arc-length and every dihedral angle of the vector model lies in
`[0, π]`, so all of `sin(a), sin(α), …` are non-negative.**  Indeed `arcLen u v` is an
`arccos` (range `[0, π]`) and `dihedralAngle A B C` is either `0` or an `arccos`; in both
cases `sin (arccos t) = √(1 − t²) ≥ 0`.  Taking square roots of non-negative quantities is
unambiguous, so the squared law upgrades to the honest proportion.

This file proves:

* `sin_arcLen_nonneg`, `sin_dihedralAngle_nonneg` — the sines of the model's arc-lengths and
  dihedral angles are non-negative.
* `spherical_law_of_sines` — the full unsquared law of sines (all three ratios equal):
  `sin(a)/sin(α) = sin(b)/sin(β) = sin(c)/sin(γ)`.
* `spherical_law_of_sines_two` — the two-ratio convenience form.

All results are fully machine-verified: 0 sorries, 0 axioms.
-/

namespace SphericalLawOfSinesOQ01

open SphericalLawOfSines

/-! ## Non-negativity of the model's sines -/

/-- The sine of any side arc-length is non-negative: `arcLen u v = arccos (u·v) ∈ [0, π]`,
and `sin (arccos t) = √(1 − t²) ≥ 0`. -/
theorem sin_arcLen_nonneg (u v : Fin 3 → ℝ) : 0 ≤ Real.sin (arcLen u v) := by
  simp only [arcLen, Real.sin_arccos]
  exact Real.sqrt_nonneg _

/-- The sine of any dihedral angle is non-negative.  `dihedralAngle A B C` is either `0`
(degenerate branch, `sin 0 = 0`) or an `arccos` (`sin (arccos t) = √(1 − t²) ≥ 0`). -/
theorem sin_dihedralAngle_nonneg (A B C : Fin 3 → ℝ) :
    0 ≤ Real.sin (dihedralAngle A B C) := by
  simp only [dihedralAngle]
  split_ifs with h
  · rw [Real.sin_zero]
  · rw [Real.sin_arccos]; exact Real.sqrt_nonneg _

/-! ## The unsquared law of sines -/

/-- Take the square root of an equality of squared non-negative ratios.  If
`x² / p² = y² / q²` with `x, p, y, q ≥ 0`, then `x / p = y / q`. -/
private theorem ratio_of_sq_ratio {x p y q : ℝ}
    (hx : 0 ≤ x) (hp : 0 ≤ p) (hy : 0 ≤ y) (hq : 0 ≤ q)
    (h : x ^ 2 / p ^ 2 = y ^ 2 / q ^ 2) : x / p = y / q := by
  have hsq : (x / p) ^ 2 = (y / q) ^ 2 := by rw [div_pow, div_pow]; exact h
  calc x / p = Real.sqrt ((x / p) ^ 2) := (Real.sqrt_sq (div_nonneg hx hp)).symm
    _ = Real.sqrt ((y / q) ^ 2) := by rw [hsq]
    _ = y / q := Real.sqrt_sq (div_nonneg hy hq)

/-- **Spherical Law of Sines** (unsquared, all three ratios equal).

  sin(a)/sin(α) = sin(b)/sin(β) = sin(c)/sin(γ),

the honest proportion behind the parent's squared form.  Obtained by taking square roots,
which is unambiguous because every `sin` appearing is non-negative
(`sin_arcLen_nonneg`, `sin_dihedralAngle_nonneg`). -/
theorem spherical_law_of_sines (A B C : Fin 3 → ℝ)
    (hA : IsUnit3 A) (hB : IsUnit3 B) (hC : IsUnit3 C)
    (hpBA : normSq (projPerp B A) ≠ 0) (hpCA : normSq (projPerp C A) ≠ 0)
    (hpAB : normSq (projPerp A B) ≠ 0) (hpCB : normSq (projPerp C B) ≠ 0)
    (hpAC : normSq (projPerp A C) ≠ 0) (hpBC : normSq (projPerp B C) ≠ 0)
    (hT : tripleProduct A B C ≠ 0) :
    Real.sin (arcLen B C) / Real.sin (dihedralAngle A B C) =
      Real.sin (arcLen A C) / Real.sin (dihedralAngle B A C) ∧
    Real.sin (arcLen A C) / Real.sin (dihedralAngle B A C) =
      Real.sin (arcLen A B) / Real.sin (dihedralAngle C A B) := by
  obtain ⟨h1, h2⟩ := spherical_law_of_sines_all_sq A B C hA hB hC
    hpBA hpCA hpAB hpCB hpAC hpBC hT
  refine ⟨?_, ?_⟩
  · exact ratio_of_sq_ratio (sin_arcLen_nonneg B C) (sin_dihedralAngle_nonneg A B C)
      (sin_arcLen_nonneg A C) (sin_dihedralAngle_nonneg B A C) h1
  · exact ratio_of_sq_ratio (sin_arcLen_nonneg A C) (sin_dihedralAngle_nonneg B A C)
      (sin_arcLen_nonneg A B) (sin_dihedralAngle_nonneg C A B) h2

/-- **Spherical Law of Sines** (unsquared, two-ratio form):
`sin(a)/sin(α) = sin(b)/sin(β)`. -/
theorem spherical_law_of_sines_two (A B C : Fin 3 → ℝ)
    (hA : IsUnit3 A) (hB : IsUnit3 B) (hC : IsUnit3 C)
    (hpBA : normSq (projPerp B A) ≠ 0) (hpCA : normSq (projPerp C A) ≠ 0)
    (hpAB : normSq (projPerp A B) ≠ 0) (hpCB : normSq (projPerp C B) ≠ 0)
    (hpAC : normSq (projPerp A C) ≠ 0) (hpBC : normSq (projPerp B C) ≠ 0)
    (hT : tripleProduct A B C ≠ 0) :
    Real.sin (arcLen B C) / Real.sin (dihedralAngle A B C) =
      Real.sin (arcLen A C) / Real.sin (dihedralAngle B A C) :=
  (spherical_law_of_sines A B C hA hB hC hpBA hpCA hpAB hpCB hpAC hpBC hT).1

/-- Transitively, the first and third ratios agree as well:
`sin(a)/sin(α) = sin(c)/sin(γ)`. -/
theorem spherical_law_of_sines_ac (A B C : Fin 3 → ℝ)
    (hA : IsUnit3 A) (hB : IsUnit3 B) (hC : IsUnit3 C)
    (hpBA : normSq (projPerp B A) ≠ 0) (hpCA : normSq (projPerp C A) ≠ 0)
    (hpAB : normSq (projPerp A B) ≠ 0) (hpCB : normSq (projPerp C B) ≠ 0)
    (hpAC : normSq (projPerp A C) ≠ 0) (hpBC : normSq (projPerp B C) ≠ 0)
    (hT : tripleProduct A B C ≠ 0) :
    Real.sin (arcLen B C) / Real.sin (dihedralAngle A B C) =
      Real.sin (arcLen A B) / Real.sin (dihedralAngle C A B) := by
  obtain ⟨h1, h2⟩ := spherical_law_of_sines A B C hA hB hC
    hpBA hpCA hpAB hpCB hpAC hpBC hT
  rw [h1, h2]

end SphericalLawOfSinesOQ01
