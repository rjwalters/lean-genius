/-
# Spherical Law of Sines — OQ-03: the Four-Parts (Cotangent) Rule

This file proves OQ-03 of the parent gallery entry
`spherical-law-of-sines`.

## The question

For a spherical triangle with unit-vector vertices `A, B, C : Fin 3 → ℝ`,
arc-length sides
  a := arcLen B C,    b := arcLen A C,    c := arcLen A B,
and dihedral angles
  α := dihedralAngle A B C,    β := dihedralAngle B A C,
  γ := dihedralAngle C A B,
prove the cotangent four-parts formula in cleared-of-cotangents
**polynomial form**

  sin α · cos a · sin b
    = sin a · sin α · cos b · cos γ + sin a · cos α · sin γ.

(Dividing through by `sin a · sin α` recovers the classical
`cot a · sin b = cos b · cos γ + sin γ · cot α`. We state the
polynomial form to avoid introducing a local `cot` and to side-step
the `sin a ≠ 0`, `sin α ≠ 0` non-degeneracy hypotheses.)

## Status

* **S1 OBSERVE** (PR #18229, merged 2026-05-12): documented the
  formula, its place in the catalogue, and the proof strategy.
* **S2 SCAFFOLD** (PR #18229 follow-up): create the file with
  imports + helper lemmas + main theorem statement.
* **S3b ACT** (this PR): discharge the main theorem
  `spherical_cotangent_rule_polynomial` **unconditionally** — 0
  sorries, 0 axioms beyond Lean's foundational
  `propext`/`Classical.choice`/`Quot.sound`.  The proof adds two
  reusable, unconditional product identities for the dihedral angle,
  `cos_dihedralAngle_mul` and `sin_dihedralAngle_mul`, that clear the
  `arccos`/`sqrt` denominators in `dihedralAngle` (the degenerate
  branch is handled by showing both sides vanish).  These yield the
  trigonometric law of cosines on two sides and the product form of
  the law of sines; the four-parts rule then follows by
  `linear_combination`, cancelling the common `sin (arcLen A C)`
  factor (with `sin (arcLen A C) = 0` handled directly, both dihedral
  angles collapsing to `0`).

## Proof strategy (Route A: derive from law of cosines)

The cotangent rule follows from two applications of the spherical
law of cosines together with the law of sines:

  (∗)   cos c = cos a · cos b + sin a · sin b · cos γ,
  (∗∗)  cos a = cos b · cos c + sin b · sin c · cos α.

Substituting (∗) into (∗∗), using `sin²b = 1 - cos²b`, multiplying
by `sin α`, and replacing `sin α · sin c` by `sin a · sin γ` (the
product form of the law of sines) yields, after cancelling a common
factor of `sin b`, the boxed polynomial identity.

To avoid the `cos`/`sin` of the dihedral angle and its `arccos`/`sqrt`
denominators, we package the two cross-terms as the unconditional
product identities

  cos (dih A B C) · sin (arcLen A B) · sin (arcLen A C)
      = dot (projPerp B A) (projPerp C A),                  (cos form)
  sin (dih A B C) · sin (arcLen A B) · sin (arcLen A C)
      = |tripleProduct A B C|,                              (sin form)

each proved by a case split on the degenerate branch of the dihedral
`if`.  The local law of cosines `spherical_law_of_cosines_local` then
supplies (∗) and (∗∗) directly in inner-product form, and the sin
form supplies the law of sines.

## Framework

The parent `SphericalLawOfSines.lean` is written in the
`Fin 3 → ℝ` cross-product framework (with `dot`, `normSq`, `arcLen`,
`IsUnit3`, `dihedralAngle`).  The sibling `SphericalLawOfCosines.lean`
uses `EuclideanSpace ℝ (Fin 3)`.  To keep the new content in a single
framework, we state the law of cosines locally as
`spherical_law_of_cosines_local`, in the parent's framework.

## References

* Smart, W. M., *Textbook on Spherical Astronomy* (1977), §3.7.
* Todhunter, I., *Spherical Trigonometry* (1886), §62.
* Bowditch, N., *The American Practical Navigator* (2002), §22.6.
-/

import Proofs.SphericalLawOfSines
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option maxHeartbeats 800000

namespace SphericalLawOfSines

/-! ### Helper lemmas -/

/-- `cos (arcLen u v) = dot u v` for unit vectors `u, v`.

This is the unit-vector form of `Real.cos_arccos`; the hypothesis
`-1 ≤ dot u v ≤ 1` follows from the Cauchy–Schwarz inequality
applied to unit vectors, extracted from the parent's
`lagrange_identity` and `normSq_cross_nonneg`. -/
theorem cos_arcLen (u v : Fin 3 → ℝ) (hu : IsUnit3 u) (hv : IsUnit3 v) :
    Real.cos (arcLen u v) = dot u v := by
  unfold IsUnit3 at hu hv
  unfold arcLen
  have h_lag := lagrange_identity u v
  have h_nn := normSq_cross_nonneg u v
  have h_bound_sq : (dot u v) ^ 2 ≤ 1 := by
    have h : (dot u v) ^ 2 ≤ normSq u * normSq v := by linarith
    rw [hu, hv] at h; linarith
  have h_upper : dot u v ≤ 1 := by
    nlinarith [h_bound_sq, sq_nonneg (dot u v - 1)]
  have h_lower : -1 ≤ dot u v := by
    nlinarith [h_bound_sq, sq_nonneg (dot u v + 1)]
  exact Real.cos_arccos h_lower h_upper

/-- `0 ≤ sin (arcLen u v)` for any pair `u, v : Fin 3 → ℝ`.

Since `arcLen u v = Real.arccos (dot u v)`, the value lies in `[0, π]`
unconditionally on the inputs, by `Real.arccos_nonneg` and
`Real.arccos_le_pi`. -/
theorem sin_arcLen_nonneg (u v : Fin 3 → ℝ) :
    0 ≤ Real.sin (arcLen u v) := by
  unfold arcLen
  exact Real.sin_nonneg_of_nonneg_of_le_pi
    (Real.arccos_nonneg _) (Real.arccos_le_pi _)

/-- The inner-product (general) form of the **spherical law of
cosines** in the parent's `Fin 3 → ℝ` framework.

For unit vectors `A, B, C`, the inner product `dot A B` decomposes
as the diagonal term `dot A C · dot B C` plus the cross term
`dot (projPerp A C) (projPerp B C)`:

  ⟨A, B⟩ = ⟨A, C⟩ · ⟨B, C⟩ + ⟨projPerp A C, projPerp B C⟩. -/
theorem spherical_law_of_cosines_local (A B C : Fin 3 → ℝ) (hC : IsUnit3 C) :
    dot A B = dot A C * dot B C + dot (projPerp A C) (projPerp B C) := by
  have hC' : C 0 * C 0 + C 1 * C 1 + C 2 * C 2 = 1 := unit_sum C hC
  simp only [dot, projPerp, Fin.sum_univ_three]
  linear_combination -(A 0 * C 0 + A 1 * C 1 + A 2 * C 2) *
    (B 0 * C 0 + B 1 * C 1 + B 2 * C 2) * hC'

/-! ### Dihedral-angle product helpers (S3b ACT) -/

/-- `0 ≤ sin (dihedralAngle A B C)`: the dihedral angle is either `0`
(degenerate branch) or an `arccos` value, which always lies in `[0, π]`. -/
theorem sin_dihedralAngle_nonneg (A B C : Fin 3 → ℝ) :
    0 ≤ Real.sin (dihedralAngle A B C) := by
  simp only [dihedralAngle]
  split_ifs with h
  · simp
  · exact Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg _) (Real.arccos_le_pi _)

/-- `sin (arcLen A B) = sqrt (normSq (projPerp B A))` for unit `A, B`.
The side-sine equals the length of the perpendicular projection. -/
theorem sin_arcLen_eq_sqrt (A B : Fin 3 → ℝ) (hA : IsUnit3 A) (hB : IsUnit3 B) :
    Real.sin (arcLen A B) = Real.sqrt (normSq (projPerp B A)) := by
  rw [normSq_projPerp_unit B A hB hA, arcLen_comm B A,
    Real.sqrt_sq (sin_arcLen_nonneg A B)]

/-- **Cosine–dihedral product identity** (unconditional).
For unit `A, B, C`,
  `cos (dihedralAngle A B C) · sin (arcLen A B) · sin (arcLen A C)
     = dot (projPerp B A) (projPerp C A)`.
In the non-degenerate case this is the definition of the dihedral
cosine cleared of its denominators; in the degenerate case both sides
vanish. -/
theorem cos_dihedralAngle_mul (A B C : Fin 3 → ℝ)
    (hA : IsUnit3 A) (hB : IsUnit3 B) (hC : IsUnit3 C) :
    Real.cos (dihedralAngle A B C) * Real.sin (arcLen A B) * Real.sin (arcLen A C)
      = dot (projPerp B A) (projPerp C A) := by
  rw [sin_arcLen_eq_sqrt A B hA hB, sin_arcLen_eq_sqrt A C hA hC]
  have h_lag := lagrange_identity (projPerp B A) (projPerp C A)
  have h_nn := normSq_cross_nonneg (projPerp B A) (projPerp C A)
  have h_cs : (dot (projPerp B A) (projPerp C A)) ^ 2
      ≤ normSq (projPerp B A) * normSq (projPerp C A) := by linarith
  have hnB_nn : 0 ≤ normSq (projPerp B A) := normSq_nonneg _
  have hnC_nn : 0 ≤ normSq (projPerp C A) := normSq_nonneg _
  simp only [dihedralAngle]
  by_cases h : Real.sqrt (normSq (projPerp B A)) = 0 ∨ Real.sqrt (normSq (projPerp C A)) = 0
  · rw [if_pos h, Real.cos_zero]
    have hdot0 : dot (projPerp B A) (projPerp C A) = 0 := by
      have hz : normSq (projPerp B A) = 0 ∨ normSq (projPerp C A) = 0 := by
        rcases h with h0 | h0
        · exact Or.inl (le_antisymm (Real.sqrt_eq_zero'.mp h0) hnB_nn)
        · exact Or.inr (le_antisymm (Real.sqrt_eq_zero'.mp h0) hnC_nn)
      rcases hz with hz | hz <;>
        · rw [hz] at h_cs
          nlinarith [sq_nonneg (dot (projPerp B A) (projPerp C A))]
    rw [hdot0]
    rcases h with h0 | h0 <;> rw [h0] <;> ring
  · rw [if_neg h]
    push_neg at h
    obtain ⟨hnB0, hnC0⟩ := h
    have hnB_pos : 0 < Real.sqrt (normSq (projPerp B A)) :=
      lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hnB0)
    have hnC_pos : 0 < Real.sqrt (normSq (projPerp C A)) :=
      lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hnC0)
    have hnB_sq : Real.sqrt (normSq (projPerp B A)) ^ 2 = normSq (projPerp B A) :=
      Real.sq_sqrt hnB_nn
    have hnC_sq : Real.sqrt (normSq (projPerp C A)) ^ 2 = normSq (projPerp C A) :=
      Real.sq_sqrt hnC_nn
    set nB := Real.sqrt (normSq (projPerp B A)) with hnB_def
    set nC := Real.sqrt (normSq (projPerp C A)) with hnC_def
    have harg_sq : (dot (projPerp B A) (projPerp C A) / (nB * nC)) ^ 2 ≤ 1 := by
      rw [div_pow, div_le_one (by positivity)]
      rw [mul_pow, hnB_sq, hnC_sq]; exact h_cs
    have hub : dot (projPerp B A) (projPerp C A) / (nB * nC) ≤ 1 := by
      nlinarith [harg_sq, sq_nonneg (dot (projPerp B A) (projPerp C A) / (nB * nC) - 1)]
    have hlb : -1 ≤ dot (projPerp B A) (projPerp C A) / (nB * nC) := by
      nlinarith [harg_sq, sq_nonneg (dot (projPerp B A) (projPerp C A) / (nB * nC) + 1)]
    rw [Real.cos_arccos hlb hub]
    field_simp

/-- **Sine–dihedral product identity** (unconditional).
For unit `A, B, C`,
  `sin (dihedralAngle A B C) · sin (arcLen A B) · sin (arcLen A C)
     = |tripleProduct A B C|`,
written as `sqrt (tripleProduct A B C ^ 2)`.  This is the spherical
"sine of the dihedral times the two adjacent side-sines equals the
scalar triple product" identity; both sides vanish in the degenerate
case. -/
theorem sin_dihedralAngle_mul (A B C : Fin 3 → ℝ)
    (hA : IsUnit3 A) (hB : IsUnit3 B) (hC : IsUnit3 C) :
    Real.sin (dihedralAngle A B C) * Real.sin (arcLen A B) * Real.sin (arcLen A C)
      = Real.sqrt (tripleProduct A B C ^ 2) := by
  have hnn : 0 ≤ Real.sin (dihedralAngle A B C) * Real.sin (arcLen A B)
      * Real.sin (arcLen A C) :=
    mul_nonneg (mul_nonneg (sin_dihedralAngle_nonneg A B C) (sin_arcLen_nonneg A B))
      (sin_arcLen_nonneg A C)
  rw [← Real.sqrt_sq hnn]
  congr 1
  have hsAB : Real.sin (arcLen A B) ^ 2 = normSq (projPerp B A) := sin_sq_arcLen A B hA hB
  have hsAC : Real.sin (arcLen A C) ^ 2 = normSq (projPerp C A) := sin_sq_arcLen A C hA hC
  by_cases h : normSq (projPerp B A) = 0 ∨ normSq (projPerp C A) = 0
  · have htrip : tripleProduct A B C ^ 2 = 0 := by
      have hcr := normSq_projPerp_cross A B C hA
      have hlag := lagrange_identity (projPerp B A) (projPerp C A)
      apply le_antisymm _ (sq_nonneg _)
      rcases h with h0 | h0 <;>
        nlinarith [sq_nonneg (dot (projPerp B A) (projPerp C A)), hcr, hlag, h0]
    rw [htrip]
    rcases h with h0 | h0
    · have hz : Real.sin (arcLen A B) = 0 :=
        (pow_eq_zero_iff (n := 2) (by norm_num)).mp (by rw [hsAB]; exact h0)
      rw [hz]; ring
    · have hz : Real.sin (arcLen A C) = 0 :=
        (pow_eq_zero_iff (n := 2) (by norm_num)).mp (by rw [hsAC]; exact h0)
      rw [hz]; ring
  · push_neg at h
    have hα := sin_sq_dihedralAngle A B C hA h.1 h.2
    have hexpand : (Real.sin (dihedralAngle A B C) * Real.sin (arcLen A B)
          * Real.sin (arcLen A C)) ^ 2
        = Real.sin (dihedralAngle A B C) ^ 2
          * (Real.sin (arcLen A B) ^ 2 * Real.sin (arcLen A C) ^ 2) := by ring
    rw [hexpand, hα, hsAB, hsAC]
    rw [div_mul_cancel₀ _ (mul_ne_zero h.1 h.2)]

/-! ### Main statement: the four-parts (cotangent) rule -/

/-- **Four-parts / cotangent rule** for a spherical triangle, in
cleared-of-cotangents polynomial form.

For a spherical triangle on the unit sphere with vertices
`A, B, C : Fin 3 → ℝ`, arc-length sides

    a := arcLen B C,    b := arcLen A C,    c := arcLen A B,

and dihedral angles

    α := dihedralAngle A B C,    γ := dihedralAngle C A B,

the four consecutive elements `(a, α, b, γ)` satisfy

    sin α · cos a · sin b
      = sin a · sin α · cos b · cos γ + sin a · cos α · sin γ.

Dividing through by `sin a · sin α` (both nonzero on a
non-degenerate spherical triangle) recovers the classical
`cot a · sin b = cos b · cos γ + sin γ · cot α`.

The polynomial form holds **unconditionally**: in degenerate
configurations both sides reduce to `0`. -/
theorem spherical_cotangent_rule_polynomial
    (A B C : Fin 3 → ℝ)
    (hA : IsUnit3 A) (hB : IsUnit3 B) (hC : IsUnit3 C) :
    Real.sin (dihedralAngle A B C) * Real.cos (arcLen B C)
        * Real.sin (arcLen A C)
      = Real.sin (arcLen B C) * Real.sin (dihedralAngle A B C)
          * Real.cos (arcLen A C) * Real.cos (dihedralAngle C A B)
        + Real.sin (arcLen B C) * Real.cos (dihedralAngle A B C)
          * Real.sin (dihedralAngle C A B) := by
  -- Cosines of the three sides as inner products.
  have hcos_a : Real.cos (arcLen B C) = dot B C := cos_arcLen B C hB hC
  have hcos_b : Real.cos (arcLen A C) = dot A C := cos_arcLen A C hA hC
  have hcos_c : Real.cos (arcLen A B) = dot A B := cos_arcLen A B hA hB
  -- Trig law of cosines for side `c = arcLen A B` (apex `C`), unconditional.
  have hE1 : Real.cos (arcLen A B)
      = Real.cos (arcLen B C) * Real.cos (arcLen A C)
        + Real.cos (dihedralAngle C A B) * Real.sin (arcLen B C)
          * Real.sin (arcLen A C) := by
    have hL1 := spherical_law_of_cosines_local A B C hC
    have hDγ := cos_dihedralAngle_mul C A B hC hA hB
    rw [arcLen_comm C A, arcLen_comm C B] at hDγ
    have hDγ' : Real.cos (dihedralAngle C A B) * Real.sin (arcLen B C)
          * Real.sin (arcLen A C) = dot (projPerp A C) (projPerp B C) := by
      rw [← hDγ]; ring
    rw [hcos_c, hcos_a, hcos_b, hDγ']
    linear_combination hL1
  -- Trig law of cosines for side `a = arcLen B C` (apex `A`), unconditional.
  have hE2 : Real.cos (arcLen B C)
      = Real.cos (arcLen A C) * Real.cos (arcLen A B)
        + Real.cos (dihedralAngle A B C) * Real.sin (arcLen A B)
          * Real.sin (arcLen A C) := by
    have hL2 := spherical_law_of_cosines_local B C A hA
    rw [dot_comm B A, dot_comm C A] at hL2
    have hDα := cos_dihedralAngle_mul A B C hA hB hC
    rw [hcos_a, hcos_b, hcos_c, hDα]
    linear_combination hL2
  -- Law of sines, product form: both sides equal `|tripleProduct A B C|`.
  have hP : Real.sin (dihedralAngle A B C) * Real.sin (arcLen A B) * Real.sin (arcLen A C)
      = Real.sin (dihedralAngle C A B) * Real.sin (arcLen B C) * Real.sin (arcLen A C) := by
    have h1 := sin_dihedralAngle_mul A B C hA hB hC
    have h2 := sin_dihedralAngle_mul C A B hC hA hB
    rw [arcLen_comm C A, arcLen_comm C B] at h2
    have htripeq : tripleProduct C A B = tripleProduct A B C :=
      (tripleProduct_cyclic C A B).symm
    rw [htripeq] at h2
    rw [h1, ← h2]; ring
  -- Pythagorean identity for the `b = arcLen A C` side.
  have hPyth := Real.sin_sq_add_cos_sq (arcLen A C)
  by_cases hSb : Real.sin (arcLen A C) = 0
  · -- Degenerate side `b`: both dihedral angles collapse to `0`.
    have hnpCA : normSq (projPerp C A) = 0 := by
      have h := sin_sq_arcLen A C hA hC
      rw [hSb] at h; simpa using h.symm
    have hnpAC : normSq (projPerp A C) = 0 := by
      have h := normSq_projPerp_unit A C hA hC
      rw [hSb] at h; simpa using h
    have hsα : Real.sin (dihedralAngle A B C) = 0 := by
      have hd : dihedralAngle A B C = 0 := by
        simp only [dihedralAngle]
        rw [if_pos (Or.inr (by rw [hnpCA, Real.sqrt_zero]))]
      rw [hd, Real.sin_zero]
    have hsγ : Real.sin (dihedralAngle C A B) = 0 := by
      have hd : dihedralAngle C A B = 0 := by
        simp only [dihedralAngle]
        rw [if_pos (Or.inl (by rw [hnpAC, Real.sqrt_zero]))]
      rw [hd, Real.sin_zero]
    rw [hsα, hsγ]; ring
  · -- Non-degenerate `b`: cancel the common `sin (arcLen A C)` factor.
    have hM : Real.sin (arcLen A C) *
        (Real.sin (dihedralAngle A B C) * Real.cos (arcLen B C) * Real.sin (arcLen A C))
        = Real.sin (arcLen A C) *
        (Real.sin (arcLen B C) * Real.sin (dihedralAngle A B C) * Real.cos (arcLen A C)
            * Real.cos (dihedralAngle C A B)
          + Real.sin (arcLen B C) * Real.cos (dihedralAngle A B C)
            * Real.sin (dihedralAngle C A B)) := by
      linear_combination
        (Real.sin (dihedralAngle A B C)) * hE2
        + (Real.sin (dihedralAngle A B C) * Real.cos (arcLen A C)) * hE1
        + (Real.sin (dihedralAngle A B C) * Real.cos (arcLen B C)) * hPyth
        + (Real.cos (dihedralAngle A B C)) * hP
    exact mul_left_cancel₀ hSb hM

/-! ### Summary

| Result                                                            | Status |
|-------------------------------------------------------------------|--------|
| `cos_arcLen`: cos(arcLen u v) = dot u v for unit u, v             | proved |
| `sin_arcLen_nonneg`: 0 ≤ sin(arcLen u v)                          | proved |
| `spherical_law_of_cosines_local` (general inner-product form)     | proved |
| `cos_dihedralAngle_mul` (cos·sides = dot of projections)          | proved |
| `sin_dihedralAngle_mul` (sin·sides = |triple product|)            | proved |
| `spherical_cotangent_rule_polynomial` (main theorem)              | proved |

Sorries: 0
Axioms:  0 (beyond Lean's foundational propext/Classical.choice/Quot.sound)
-/

end SphericalLawOfSines
