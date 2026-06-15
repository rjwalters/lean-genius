import Mathlib

/-!
# Converse of the Product-of-Segments-of-Chords (Power of a Point) Theorem

This file accompanies `Proofs/ProductOfSegmentsOfChords.lean`, which formalizes the
forward intersecting-chords theorem and **axiomatizes** the converse as
`converse_product_implies_concyclic_axiom`.

## The integrity finding

That axiom claims: for `P A B C D : EuclideanSpace ℝ (Fin 2)` with `B-P = t•(A-P)`,
`D-P = s•(C-P)`, all points `≠ P`, `A ≠ B`, `C ≠ D`, and the **unsigned** product
equality `‖P-A‖·‖P-B‖ = ‖P-C‖·‖P-D‖`, the four points are concyclic.

**This axiom is false.** The unsigned product discards the sign of the power of the
point. The true converse of power-of-a-point requires the *signed* powers to agree:
`t·‖A-P‖² = s·‖C-P‖²`. The unsigned condition `|t|·‖A-P‖² = |s|·‖C-P‖²` also holds when
`P` is *between* one pair but *outside* the other — opposite-sign powers, no shared
circle.

`unsigned_converse_counterexample` below proves the negation: an explicit configuration
satisfying every hypothesis of the axiom for which **no** common circle exists. The
witness is `P = 0`, `A = e₀`, `B = -4•e₀`, `C = e₁`, `D = 4•e₁` for any two unit vectors
`e₀, e₁` (e.g. the standard basis): here `t = -4`, `s = 4`, so `|t| = |s|` makes the
unsigned products equal (`1·4 = 1·4`), but the signed powers `-4` and `+4` have opposite
sign, so the four points cannot be concyclic.

The corrected, provable converse is stated as `signed_converse_implies_concyclic`
(currently a `sorry`; the circumcenter construction is build-gated — see
`research/problems/product-of-segments-of-chords-oq-02/knowledge.md`).

NOTE: build-pending. The Docker Lean toolchain was unavailable when this was written,
so the proofs below have not been machine-checked. This file is intentionally NOT
registered in `Proofs.lean` until it has been built.
-/

set_option linter.unusedVariables false

open scoped RealInnerProductSpace

namespace ProductOfSegmentsOfChordsConverse

abbrev Vec2 := EuclideanSpace ℝ (Fin 2)

/-- **The unsigned converse axiom is false (general form).**

Given *any* two unit vectors `e₀ e₁` in the plane, the configuration
`P = 0, A = e₀, B = -4•e₀, C = e₁, D = 4•e₁` satisfies every hypothesis of
`converse_product_implies_concyclic_axiom` (collinearity through `P`, all points
distinct from `P`, `A ≠ B`, `C ≠ D`, and equal unsigned products `‖P-A‖·‖P-B‖ =
‖P-C‖·‖P-D‖ = 4`), yet the four points lie on **no** common circle.

The obstruction is purely the sign: `B-P = (-4)•(A-P)` (P inside chord `AB`) while
`D-P = 4•(C-P)` (P outside chord `CD`), so the signed powers `-4` and `+4` disagree. -/
theorem unsigned_converse_counterexample_general
    (e₀ e₁ : Vec2) (he₀ : ‖e₀‖ = 1) (he₁ : ‖e₁‖ = 1) :
    ∃ (P A B C D : Vec2),
      (∃ t : ℝ, B - P = t • (A - P)) ∧
      (∃ t : ℝ, D - P = t • (C - P)) ∧
      ‖P - A‖ * ‖P - B‖ = ‖P - C‖ * ‖P - D‖ ∧
      A ≠ P ∧ B ≠ P ∧ C ≠ P ∧ D ≠ P ∧ A ≠ B ∧ C ≠ D ∧
      ¬ ∃ (O : Vec2) (r : ℝ), r > 0 ∧
          ‖A - O‖ = r ∧ ‖B - O‖ = r ∧ ‖C - O‖ = r ∧ ‖D - O‖ = r := by
  refine ⟨0, e₀, (-4 : ℝ) • e₀, e₁, (4 : ℝ) • e₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- collinearity of A, B through P = 0 with t = -4
    exact ⟨-4, by simp⟩
  · -- collinearity of C, D through P = 0 with s = 4
    exact ⟨4, by simp⟩
  · -- equal unsigned products: 1 * 4 = 1 * 4
    have hB : ‖(0 : Vec2) - (-4 : ℝ) • e₀‖ = 4 := by
      rw [zero_sub, norm_neg, norm_smul, he₀, mul_one, Real.norm_eq_abs]; norm_num
    have hD : ‖(0 : Vec2) - (4 : ℝ) • e₁‖ = 4 := by
      rw [zero_sub, norm_neg, norm_smul, he₁, mul_one, Real.norm_eq_abs]; norm_num
    have hA : ‖(0 : Vec2) - e₀‖ = 1 := by rw [zero_sub, norm_neg, he₀]
    have hC : ‖(0 : Vec2) - e₁‖ = 1 := by rw [zero_sub, norm_neg, he₁]
    rw [hA, hB, hC, hD]
  · -- A = e₀ ≠ 0
    intro h; rw [h, norm_zero] at he₀; norm_num at he₀
  · -- B = -4•e₀ ≠ 0
    intro h
    have hn : ‖(-4 : ℝ) • e₀‖ = 0 := by rw [h]; simp
    rw [norm_smul, he₀, mul_one, Real.norm_eq_abs] at hn; norm_num at hn
  · -- C = e₁ ≠ 0
    intro h; rw [h, norm_zero] at he₁; norm_num at he₁
  · -- D = 4•e₁ ≠ 0
    intro h
    have hn : ‖(4 : ℝ) • e₁‖ = 0 := by rw [h]; simp
    rw [norm_smul, he₁, mul_one, Real.norm_eq_abs] at hn; norm_num at hn
  · -- A = e₀ ≠ B = -4•e₀
    intro h
    have hsub : e₀ - (-4 : ℝ) • e₀ = (5 : ℝ) • e₀ := by module
    have h5 : (5 : ℝ) • e₀ = 0 := by rw [← hsub, sub_eq_zero]; exact h
    have hn : ‖(5 : ℝ) • e₀‖ = 0 := by rw [h5]; simp
    rw [norm_smul, he₀, mul_one, Real.norm_eq_abs] at hn; norm_num at hn
  · -- C = e₁ ≠ D = 4•e₁
    intro h
    have hsub : e₁ - (4 : ℝ) • e₁ = (-3 : ℝ) • e₁ := by module
    have h3 : (-3 : ℝ) • e₁ = 0 := by rw [← hsub, sub_eq_zero]; exact h
    have hn : ‖(-3 : ℝ) • e₁‖ = 0 := by rw [h3]; simp
    rw [norm_smul, he₁, mul_one, Real.norm_eq_abs] at hn; norm_num at hn
  · -- No common circle: the perpendicular-bisector constraints are contradictory.
    rintro ⟨O, r, hr, hA, hB, hC, hD⟩
    -- Square each distance equality to r.
    have hA2 : ‖e₀ - O‖ ^ 2 = r ^ 2 := by rw [hA]
    have hB2 : ‖(-4 : ℝ) • e₀ - O‖ ^ 2 = r ^ 2 := by rw [hB]
    have hC2 : ‖e₁ - O‖ ^ 2 = r ^ 2 := by rw [hC]
    have hD2 : ‖(4 : ℝ) • e₁ - O‖ ^ 2 = r ^ 2 := by rw [hD]
    -- Expand the squared norms via the polarization identity.
    rw [norm_sub_sq_real, he₀] at hA2
    rw [norm_sub_sq_real, he₁] at hC2
    rw [norm_sub_sq_real, norm_smul, he₀, real_inner_smul_left] at hB2
    rw [norm_sub_sq_real, norm_smul, he₁, real_inner_smul_left] at hD2
    -- Abbreviations for the two relevant inner products and ‖O‖².
    set a : ℝ := inner e₀ O with ha
    set b : ℝ := inner e₁ O with hb
    set n : ℝ := ‖O‖ ^ 2 with hn
    -- After expansion:
    --   hA2 : 1 - 2a + n = r²
    --   hB2 : (|−4|·1)² - 2(−4)a + n = r²   i.e. 16 + 8a + n = r²
    --   hC2 : 1 - 2b + n = r²
    --   hD2 : (|4|·1)² - 2(4)b + n = r²      i.e. 16 - 8b + n = r²
    -- From hA2 = hB2: 1 - 2a = 16 + 8a ⟹ a = -3/2.
    -- From hC2 = hD2: 1 - 2b = 16 - 8b ⟹ b =  5/2.
    -- From hA2 = hC2: a = b.  Contradiction (-3/2 ≠ 5/2).
    have e4 : ‖(-4 : ℝ)‖ = 4 := by rw [Real.norm_eq_abs]; norm_num
    have e4' : ‖(4 : ℝ)‖ = 4 := by rw [Real.norm_eq_abs]; norm_num
    rw [e4] at hB2
    rw [e4'] at hD2
    nlinarith [hA2, hB2, hC2, hD2]

/-- **The unsigned converse axiom is false (concrete witness).**

Specialization of `unsigned_converse_counterexample_general` to the standard basis
`e₀ = (1,0)`, `e₁ = (0,1)`, giving the explicit configuration
`P = (0,0), A = (1,0), B = (-4,0), C = (0,1), D = (0,4)` documented in the gallery. -/
theorem unsigned_converse_counterexample :
    ∃ (P A B C D : Vec2),
      (∃ t : ℝ, B - P = t • (A - P)) ∧
      (∃ t : ℝ, D - P = t • (C - P)) ∧
      ‖P - A‖ * ‖P - B‖ = ‖P - C‖ * ‖P - D‖ ∧
      A ≠ P ∧ B ≠ P ∧ C ≠ P ∧ D ≠ P ∧ A ≠ B ∧ C ≠ D ∧
      ¬ ∃ (O : Vec2) (r : ℝ), r > 0 ∧
          ‖A - O‖ = r ∧ ‖B - O‖ = r ∧ ‖C - O‖ = r ∧ ‖D - O‖ = r := by
  have h0 : ‖(EuclideanSpace.single (0 : Fin 2) (1 : ℝ))‖ = 1 := by
    rw [EuclideanSpace.norm_single]; simp
  have h1 : ‖(EuclideanSpace.single (1 : Fin 2) (1 : ℝ))‖ = 1 := by
    rw [EuclideanSpace.norm_single]; simp
  exact unsigned_converse_counterexample_general _ _ h0 h1

/-- **The corrected (signed) converse — provable formulation.**

Replacing the unsigned product with the **signed** power equality
`t · ‖A-P‖² = s · ‖C-P‖²` (here `t, s` are the collinearity scalars, so the left side
is `powerOfPoint P` measured along chord `AB` and the right along `CD`), together with
the non-degeneracy hypothesis that the two chords are genuinely distinct lines
(`A-P` and `C-P` linearly independent), the converse holds: `A, B, C, D` are concyclic.

The proof is the circumcenter construction (solve the 2×2 perpendicular-bisector system
for the circle through `A, B, C`, then show `D` is the second intersection of line `CD`
with that circle via the signed-power identity). It is build-gated; see knowledge.md. -/
theorem signed_converse_implies_concyclic
    (P A B C D : Vec2) (t s : ℝ)
    (hAB : B - P = t • (A - P)) (hCD : D - P = s • (C - P))
    (hindep : LinearIndependent ℝ ![A - P, C - P])
    (hsigned : t * ‖A - P‖ ^ 2 = s * ‖C - P‖ ^ 2)
    (hAneP : A ≠ P) (hCneP : C ≠ P) :
    ∃ (O : Vec2) (r : ℝ), r > 0 ∧
      ‖A - O‖ = r ∧ ‖B - O‖ = r ∧ ‖C - O‖ = r ∧ ‖D - O‖ = r := by
  sorry

end ProductOfSegmentsOfChordsConverse
