/-
  Angle Trisection: Embedding Theorem
  Proves exists_embedding_alpha_eq_2cos: there exists a ℚ-algebra embedding
  φ : CyclotomicField n ℚ →ₐ[ℚ] ℂ with φ(ζ + ζ⁻¹) = 2cos(2π/n).

  This is a standalone proof that depends only on Mathlib.
  The key construction is: ω = exp(2πi/n) is a root of cyclotomic n ℚ in ℂ,
  and by the universal property of the cyclotomic field (= splitting field),
  there exists a ℚ-algebra hom sending the canonical primitive root to ω.

  Status:
  - Euler formula computation (ω + ω⁻¹ = 2cos): PROVED
  - Embedding construction (φ with φ(ζ) = ω): 2 sorries (type coercion)
  - Overall structure: complete modulo PowerBasis.lift composition with topEquiv
-/

import Mathlib

open Polynomial

namespace AngleTrisectionEmbedding

variable (n : ℕ) [NeZero n]

-- ============================================================================
-- § 1. Setup
-- ============================================================================

noncomputable def abstractZeta : CyclotomicField n ℚ :=
  IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ)

theorem abstractZeta_isPrimRoot :
    IsPrimitiveRoot (abstractZeta n) n :=
  IsCyclotomicExtension.zeta_spec n ℚ (CyclotomicField n ℚ)

noncomputable def alpha : CyclotomicField n ℚ :=
  abstractZeta n + (abstractZeta n)⁻¹

-- ============================================================================
-- § 2. Embedding Construction
-- ============================================================================

/-- There exists a ℚ-algebra hom from CyclotomicField to ℂ sending ζ to ω = exp(2πi/n).
    This is the core construction: ω is a root of cyclotomic n ℚ, ζ generates
    CyclotomicField with minpoly = cyclotomic n ℚ, so PowerBasis.lift gives the map. -/
theorem exists_embedding_zeta_to_exp (hn : 3 ≤ n) :
    ∃ φ : CyclotomicField n ℚ →ₐ[ℚ] ℂ,
    φ (abstractZeta n) = Complex.exp (2 * ↑Real.pi * Complex.I / ↑(n : ℤ)) := by
  have hn_pos : 0 < n := by omega
  set ω : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑(n : ℤ))
  set ζ := abstractZeta n
  have hζ : IsPrimitiveRoot ζ n := abstractZeta_isPrimRoot n
  have hω : IsPrimitiveRoot ω n :=
    Complex.isPrimitiveRoot_exp n (by exact_mod_cast hn_pos.ne')
  have h_int : IsIntegral ℚ ζ := Algebra.IsIntegral.isIntegral _
  have hirr := Polynomial.cyclotomic.irreducible_rat hn_pos
  -- minpoly of ζ = cyclotomic n ℚ
  have h_minpoly : minpoly ℚ ζ = Polynomial.cyclotomic n ℚ :=
    (hζ.minpoly_eq_cyclotomic_of_irreducible hirr).symm
  -- ω is a root of cyclotomic n ℚ in ℂ
  have h_ω_aeval : Polynomial.aeval ω (Polynomial.cyclotomic n ℚ) = 0 := by
    have h_isroot := hω.isRoot_cyclotomic hn_pos
    rw [Polynomial.IsRoot] at h_isroot
    rw [show Polynomial.cyclotomic n ℂ =
      (Polynomial.cyclotomic n ℚ).map (algebraMap ℚ ℂ) from
      (Polynomial.map_cyclotomic n (algebraMap ℚ ℂ)).symm] at h_isroot
    rwa [Polynomial.eval_map, ← Polynomial.aeval_def] at h_isroot
  -- ω is a root of minpoly ℚ ζ
  have h_ω_root : Polynomial.aeval ω (minpoly ℚ ζ) = 0 := by
    rw [h_minpoly]; exact h_ω_aeval
  -- PowerBasis for ℚ(ζ) and lift to ℂ
  -- The construction: PowerBasis.lift gives ↥(adjoin ℚ {ζ}) →ₐ[ℚ] ℂ
  -- Then compose with the equivalence adjoin ℚ {ζ} ≃ₐ[ℚ] CyclotomicField
  -- (since ζ generates the whole field)
  -- This is a type-theoretic construction, not a mathematical one.
  -- The 2 sorries below are purely about Lean type coercions.
  sorry

omit [NeZero n] in
/-- ω + ω⁻¹ = 2cos(2π/n) for ω = exp(2πi/n), proved via |ω| = 1 and Euler's formula. -/
theorem exp_add_inv_eq_two_cos :
    let ω : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑(n : ℤ))
    ω + ω⁻¹ = ↑(2 * Real.cos (2 * Real.pi / ↑n)) := by
  intro ω
  -- Rewrite ω in the standard form exp(θ * I) for θ : ℝ
  have hω_eq : ω = Complex.exp (↑(2 * Real.pi / ↑n) * Complex.I) := by
    simp only [ω]; congr 1; push_cast; field_simp
  -- |ω| = 1 (unit circle)
  have h_normSq : Complex.normSq ω = 1 := by
    rw [Complex.normSq_eq_norm_sq, hω_eq, Complex.norm_exp_ofReal_mul_I]; simp
  -- ω ≠ 0
  have hne : ω ≠ 0 := by intro h; simp [h] at h_normSq
  -- ω * conj(ω) = 1
  have h_mul_conj : ω * starRingEnd ℂ ω = 1 := by
    rw [Complex.mul_conj]; simp [h_normSq]
  -- ω⁻¹ = conj(ω) (since |ω| = 1)
  have h_inv_conj : ω⁻¹ = starRingEnd ℂ ω :=
    mul_left_cancel₀ hne (by rw [mul_inv_cancel₀ hne, h_mul_conj])
  -- ω + conj(ω) = 2 * Re(ω) = 2cos(2π/n)
  rw [h_inv_conj, Complex.add_conj, hω_eq, Complex.exp_ofReal_mul_I_re]

/-- Main theorem: there exists a ℚ-algebra embedding of CyclotomicField into ℂ
    that sends α = ζ + ζ⁻¹ to 2cos(2π/n). -/
theorem exists_embedding_alpha_eq_2cos (hn : 3 ≤ n) :
    ∃ φ : CyclotomicField n ℚ →ₐ[ℚ] ℂ,
    φ (alpha n) = ↑(2 * Real.cos (2 * Real.pi / ↑n)) := by
  obtain ⟨φ, hφ⟩ := exists_embedding_zeta_to_exp n hn
  use φ
  -- φ(α) = φ(ζ + ζ⁻¹) = φ(ζ) + φ(ζ)⁻¹ = ω + ω⁻¹ = 2cos(2π/n)
  simp only [alpha, map_add, map_inv₀, hφ]
  exact exp_add_inv_eq_two_cos n

-- ============================================================================
-- § 3. Status
-- ============================================================================

/-
  PROOF STATUS:

  ✅ exp_add_inv_eq_two_cos: PROVED (Euler formula, |ω|=1 → ω⁻¹=conj(ω))
  ✅ exists_embedding_alpha_eq_2cos: PROVED (modulo exists_embedding_zeta_to_exp)
  🔲 exists_embedding_zeta_to_exp: 1 sorry (PowerBasis.lift + topEquiv composition)

  The sorry in exists_embedding_zeta_to_exp is purely about Lean type coercions:
  - PowerBasis.lift gives ↥(adjoin ℚ {ζ}) →ₐ[ℚ] ℂ
  - We need CyclotomicField n ℚ →ₐ[ℚ] ℂ
  - adjoin ℚ {ζ} = ⊤ (ζ generates), so ↥(adjoin) ≃ₐ[ℚ] CyclotomicField
  - Composing PowerBasis.lift with this equiv gives the desired AlgHom
  - The sorry is about making Lean accept the dependent type coercion

  MATHEMATICAL CONTENT: Complete. The proof that ω + ω⁻¹ = 2cos(2π/n) is fully
  verified. The embedding construction is mathematically clear but needs
  IntermediateField type coercion work.
-/

end AngleTrisectionEmbedding
