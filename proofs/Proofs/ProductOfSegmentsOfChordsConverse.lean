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

The corrected, provable converse is stated as `signed_converse_implies_concyclic`. Its
proof is now reduced (via a translation putting `P` at the origin) to a single isolated
geometric lemma `circumcenter_signed`; the surrounding assembly is fully proved, and only
the build-gated circumcenter construction inside `circumcenter_signed` remains a `sorry`
(a clean Aristotle target — see
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

/-- **Normalized circumcenter with matching signed powers (the geometric heart).**

The translation-invariant core of the corrected converse, stated with the point of
intersection moved to the origin (`P = 0`, `A = u`, `B = t•u`, `C = v`, `D = s•v`).

Given two linearly independent vectors `u, v` and scalars `t, s` whose **signed** powers
agree (`t·‖u‖² = s·‖v‖²`), there is a center `O` equidistant from all four of
`u, t•u, v, s•v`. Concretely `O` is the circumcenter of the circle through `u, t•u, v`;
the signed-power hypothesis is exactly what forces the fourth point `s•v` onto it.

Build-gated proof sketch (the isolated `sorry`, a clean Aristotle target):
solve the 2×2 perpendicular-bisector system for `O` in the basis `{u, v}` (its
determinant is `‖u‖²‖v‖² − ⟪u,v⟫² ≠ 0` by Cauchy–Schwarz + linear independence), set
`r = ‖u − O‖`, and verify `‖s•v − O‖ = r` by expanding squared norms (polarization) and
substituting `t·‖u‖² = s·‖v‖²`. Degenerate scalars are automatic: if `t = 1` then
`t•u = u` (and the corresponding equality is `rfl`-trivial), likewise `s = 1`. The
identity `‖s•v − O‖² = r²` was checked numerically over 19987 random configurations
(`research/problems/product-of-segments-of-chords-oq-02/verify_signed_converse.py`). -/
theorem circumcenter_signed (u v : Vec2) (t s : ℝ)
    (hindep : LinearIndependent ℝ ![u, v])
    (hsigned : t * ‖u‖ ^ 2 = s * ‖v‖ ^ 2) :
    ∃ O : Vec2,
      ‖u - O‖ = ‖t • u - O‖ ∧ ‖u - O‖ = ‖v - O‖ ∧ ‖u - O‖ = ‖s • v - O‖ := by
  sorry

/-- **The corrected (signed) converse — provable formulation.**

Replacing the unsigned product with the **signed** power equality
`t · ‖A-P‖² = s · ‖C-P‖²` (here `t, s` are the collinearity scalars, so the left side
is `powerOfPoint P` measured along chord `AB` and the right along `CD`), together with
the non-degeneracy hypothesis that the two chords are genuinely distinct lines
(`A-P` and `C-P` linearly independent), the converse holds: `A, B, C, D` are concyclic.

This reduces to the translation-normalized `circumcenter_signed` via `O = P + Õ`: the
substitution `X - (P + Õ) = (X - P) - Õ` carries each of the four distance equalities
back to the origin-centered statement. The radius is positive because `A ≠ C`
(equivalently `u ≠ v`, from linear independence). -/
theorem signed_converse_implies_concyclic
    (P A B C D : Vec2) (t s : ℝ)
    (hAB : B - P = t • (A - P)) (hCD : D - P = s • (C - P))
    (hindep : LinearIndependent ℝ ![A - P, C - P])
    (hsigned : t * ‖A - P‖ ^ 2 = s * ‖C - P‖ ^ 2)
    (hAneP : A ≠ P) (hCneP : C ≠ P) :
    ∃ (O : Vec2) (r : ℝ), r > 0 ∧
      ‖A - O‖ = r ∧ ‖B - O‖ = r ∧ ‖C - O‖ = r ∧ ‖D - O‖ = r := by
  obtain ⟨Õ, hAB', hAC', hAD'⟩ := circumcenter_signed (A - P) (C - P) t s hindep hsigned
  -- `u ≠ v`, i.e. `A - P ≠ C - P`, from linear independence (entries of an independent
  -- family are pairwise distinct).
  have huv : (A - P) ≠ (C - P) := by
    have hinj := hindep.injective
    have hne : ![A - P, C - P] 0 ≠ ![A - P, C - P] 1 := hinj.ne (by decide)
    simpa using hne
  -- Hence the candidate radius `‖(A - P) - Õ‖` is nonzero: otherwise `A - P = Õ = C - P`.
  have hrne : (A - P) - Õ ≠ 0 := by
    intro h0
    apply huv
    have hA0 : ‖(A - P) - Õ‖ = 0 := by rw [h0]; exact norm_zero
    have hC0 : ‖(C - P) - Õ‖ = 0 := by rw [← hAC']; exact hA0
    have hCeq : (C - P) - Õ = 0 := norm_eq_zero.mp hC0
    rw [sub_eq_zero.mp h0, sub_eq_zero.mp hCeq]
  refine ⟨P + Õ, ‖(A - P) - Õ‖, norm_pos_iff.mpr hrne, ?_, ?_, ?_, ?_⟩
  · -- ‖A - (P + Õ)‖ = r
    rw [show A - (P + Õ) = (A - P) - Õ from by abel]
  · -- ‖B - (P + Õ)‖ = r, using B - P = t • (A - P) and `hAB'`.
    rw [show B - (P + Õ) = (B - P) - Õ from by abel, hAB]
    exact hAB'.symm
  · -- ‖C - (P + Õ)‖ = r
    rw [show C - (P + Õ) = (C - P) - Õ from by abel]
    exact hAC'.symm
  · -- ‖D - (P + Õ)‖ = r, using D - P = s • (C - P) and `hAD'`.
    rw [show D - (P + Õ) = (D - P) - Õ from by abel, hCD]
    exact hAD'.symm

end ProductOfSegmentsOfChordsConverse
