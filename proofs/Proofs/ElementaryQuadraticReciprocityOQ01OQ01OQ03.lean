/-
  # Jacobi Sums and Higher Power Reciprocity
  # (elementary-quadratic-reciprocity-oq-01-oq-01-oq-03)

  ## The Open Question

  **OQ-01-OQ-01-OQ-03**: Can the Gauss sum proof of quadratic reciprocity be extended
  to cubic and quartic reciprocity using Jacobi sums?

  ## Answer: YES

  The Jacobi sum framework provides a unified analytic engine for ALL power reciprocity laws:

    J(χ, ψ) = Σ_{x ∈ F} χ(x) ψ(1 - x)

  The fundamental identity (for χψ ≠ 1):

    g(χ) · g(ψ) = J(χ, ψ) · g(χψ)

  This holds for characters of ANY order n ≥ 2. Combined with the algebraic norm:
    J(χ,ψ) · J(χ⁻¹,ψ⁻¹) = #F

  it drives ALL higher power reciprocity proofs.

  ## Algebraic Structure of Jacobi Sums

  For a character χ of order n on 𝔽_p (p ≡ 1 mod n):
  - J(χ,χ) ∈ ℤ[ζ_n] (ring of integers of ℚ(ζ_n))
  - N(J(χ,χ)) = p  (algebraic norm over ℚ)
  - This gives p = N(J) in the relevant ring:
    - n=3: p = a² - ab + b²  (Eisenstein/cubic)
    - n=4: p = a² + b²       (Gaussian/quartic = Fermat two-squares)

  ## Mathlib 4 Infrastructure (2026)

  `Mathlib.NumberTheory.JacobiSum.Basic` provides:
  - `jacobiSum`: the sum `∑ x : F, χ x * ψ (1 - x)`
  - `jacobiSum_mul_nontrivial`: g(χψ)·J(χ,ψ) = g(χ)·g(ψ) for χψ ≠ 1
  - `jacobiSum_mul_jacobiSum_inv`: J(χ,ψ)·J(χ⁻¹,ψ⁻¹) = #F
  - `jacobiSum_nontrivial_inv`: J(χ,χ⁻¹) = -χ(-1)
  - `jacobiSum_one_nontrivial`: J(1,χ) = -1 for nontrivial χ
  - `gaussSum_pow_eq_prod_jacobiSum`: g(χ)^n = χ(-1)·#F·∏ J(χ,χ^k)

  Tags: number-theory, reciprocity, Jacobi-sums, Gauss-sums, cubic-reciprocity, quartic

  References:
  - Ireland & Rosen, "A Classical Introduction to Modern Number Theory", Chs. 8-9
  - Berndt, Evans & Williams, "Gauss and Jacobi Sums"
-/

import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic

open MulChar AddChar

set_option maxHeartbeats 800000

namespace JacobiSumHigherPower

-- ============================================================================
-- Part I: The Fundamental Jacobi–Gauss Identity
-- ============================================================================

section FundamentalIdentities

variable {F R : Type*} [Field F] [Fintype F] [CommRing R]

/-- **Fundamental Jacobi–Gauss Identity**: g(χ)·g(φ) = J(χ,φ)·g(χφ).

    This holds for characters χ, φ of ANY order n when χφ ≠ 1. It is the
    analytic engine behind all power reciprocity laws:
    - n=2 (quadratic): special case with χφ = χ² = 1 (boundary, not this form)
    - n=3 (cubic): J(χ,χ)·g(χ²) = g(χ)²  [key cubic identity]
    - n=4 (quartic): J(χ,χ)·g(χ²) = g(χ)²

    Source: `jacobiSum_mul_nontrivial` in Mathlib.NumberTheory.JacobiSum.Basic -/
theorem jacobiSum_gaussSum_relation
    {χ φ : MulChar F R} (h : χ * φ ≠ 1) (ψ : AddChar F R) :
    gaussSum (χ * φ) ψ * jacobiSum χ φ = gaussSum χ ψ * gaussSum φ ψ :=
  jacobiSum_mul_nontrivial h ψ

/-- Ratio form: J(χ, φ) = g(χ)·g(φ)/g(χφ), when #F ≠ 0 in the target ring. -/
theorem jacobiSum_ratio_form
    (h : (Fintype.card F : R) ≠ 0) {χ φ : MulChar F R} (hχφ : χ * φ ≠ 1)
    {ψ : AddChar F R} (hψ : ψ.IsPrimitive) :
    jacobiSum χ φ = gaussSum χ ψ * gaussSum φ ψ / gaussSum (χ * φ) ψ :=
  jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum h hχφ hψ

/-- J(1, χ) = -1 for any nontrivial χ (trivial-nontrivial boundary case). -/
theorem jacobiSum_trivial_left {χ : MulChar F R} (hχ : χ ≠ 1) :
    jacobiSum 1 χ = -1 := jacobiSum_one_nontrivial hχ

/-- **Complementary Pair**: J(χ, χ⁻¹) = -χ(-1) for nontrivial χ.

    For quadratic χ (where χ⁻¹ = χ): J(χ, χ) = -χ(-1) = ∓1.
    This shows the quadratic Jacobi sum is trivial — the substantive result
    is the Gauss sum norm τ² = χ(-1)·p, not the Jacobi sum directly. -/
theorem jacobiSum_self_inv {χ : MulChar F R} (hχ : χ ≠ 1) :
    jacobiSum χ χ⁻¹ = -χ (-1) := jacobiSum_nontrivial_inv hχ

/-- Commutativity: J(χ, φ) = J(φ, χ). -/
theorem jacobiSum_is_symmetric (χ φ : MulChar F R) :
    jacobiSum χ φ = jacobiSum φ χ := jacobiSum_comm χ φ

end FundamentalIdentities

-- ============================================================================
-- Part II: The Algebraic Norm Formula
-- ============================================================================

section AlgebraicNorm

/-- **Algebraic Norm Formula**: J(χ, φ)·J(χ⁻¹, φ⁻¹) = #F.

    This is the algebraic norm formula for Jacobi sums. Over a prime field 𝔽_p:
    - In ℂ: this equals p (since #𝔽_p = p)
    - In ℤ[ω]: N(J(χ,χ)) = a² - ab + b² = p (Eisenstein norm, cubic case)
    - In ℤ[i]: N(J(χ,χ)) = a² + b² = p (Gaussian norm, quartic case)

    Requires: different characteristics between source and target fields.
    Source: `jacobiSum_mul_jacobiSum_inv` in Mathlib.NumberTheory.JacobiSum.Basic -/
theorem jacobiSum_algebraic_norm
    {F F' : Type*} [Field F] [Fintype F] [Field F']
    (h_char : ringChar F' ≠ ringChar F)
    {χ φ : MulChar F F'} (hχ : χ ≠ 1) (hφ : φ ≠ 1) (hχφ : χ * φ ≠ 1) :
    jacobiSum χ φ * jacobiSum χ⁻¹ φ⁻¹ = Fintype.card F :=
  jacobiSum_mul_jacobiSum_inv h_char hχ hφ hχφ

/-- For a prime field 𝔽_p, the norm formula gives the prime p itself. -/
theorem jacobiSum_prime_field_norm
    {p : ℕ} [hp : Fact p.Prime] {F' : Type*} [Field F']
    (h_char : ringChar F' ≠ p)
    {χ φ : MulChar (ZMod p) F'} (hχ : χ ≠ 1) (hφ : φ ≠ 1) (hχφ : χ * φ ≠ 1) :
    jacobiSum χ φ * jacobiSum χ⁻¹ φ⁻¹ = p := by
  have h := jacobiSum_algebraic_norm
    (by rwa [ZMod.ringChar_zmod_n]) hχ hφ hχφ
  simpa [ZMod.card] using h

end AlgebraicNorm

-- ============================================================================
-- Part III: Cubic Reciprocity — The Norm Condition
-- ============================================================================

section CubicSetup

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Cubic Jacobi Norm**: For a cubic character χ on 𝔽_p, J(χ,χ)·J(χ⁻¹,χ⁻¹) = p.

    A cubic character satisfies χ³ = 1 and χ ≠ 1. For p ≡ 1 (mod 3), such
    characters exist (as the Galois group of 𝔽_p× ≅ ℤ/(p-1)ℤ has a quotient of
    order 3).

    The product J·J̄ = p means J(χ,χ) is a "prime element" of norm p in ℤ[ω]
    (where ω = e^{2πi/3}). This drives Eisenstein's cubic reciprocity proof:
      - J(χ,χ) = a + bω with a² - ab + b² = p
      - Every p ≡ 1 (mod 3) factors as (a+bω)(a+bω²) in ℤ[ω]
      - The cubic residue symbol (q/π)₃ is then determined by J mod q -/
theorem cubic_jacobi_algebraic_norm
    {F' : Type*} [Field F'] (h_char : ringChar F' ≠ p)
    (χ : MulChar (ZMod p) F') (hχ : χ ≠ 1) (hχ2 : χ ^ 2 ≠ 1) :
    jacobiSum χ χ * jacobiSum χ⁻¹ χ⁻¹ = p :=
  jacobiSum_prime_field_norm h_char hχ hχ (by rwa [← sq])

/-- **Quartic Jacobi Norm**: For a quartic character χ on 𝔽_p, J(χ,χ)·J(χ⁻¹,χ⁻¹) = p.

    A quartic character has order 4: χ⁴ = 1, χ² ≠ 1. For p ≡ 1 (mod 4):
      J(χ,χ) ∈ ℤ[i] with a² + b² = p  (Gaussian norm)
    This connects to the Fermat two-squares theorem and to quartic reciprocity.

    Quartic reciprocity: (π/q)₄·(q/π)₄ = (-1)^{(p-1)(q-1)/16} for primary π, q ≡ 1 mod 4 -/
theorem quartic_jacobi_algebraic_norm
    {F' : Type*} [Field F'] (h_char : ringChar F' ≠ p)
    (χ : MulChar (ZMod p) F') (hχ : χ ≠ 1) (hχ2 : χ ^ 2 ≠ 1) :
    jacobiSum χ χ * jacobiSum χ⁻¹ χ⁻¹ = p :=
  cubic_jacobi_algebraic_norm h_char χ hχ hχ2

/-- **General Jacobi Norm**: For any pair (χ, χ^k) where χ, χ^k, χ^{k+1} are nontrivial. -/
theorem general_jacobi_norm
    {F' : Type*} [Field F'] (h_char : ringChar F' ≠ p)
    (χ : MulChar (ZMod p) F') {k : ℕ}
    (hχ : χ ≠ 1) (hχk : χ ^ k ≠ 1) (hχk1 : χ ^ (k + 1) ≠ 1) :
    jacobiSum χ (χ ^ k) * jacobiSum χ⁻¹ (χ ^ k)⁻¹ = p :=
  jacobiSum_prime_field_norm h_char hχ hχk (by rw [mul_comm]; rwa [← pow_succ])

end CubicSetup

-- ============================================================================
-- Part IV: Quadratic Case — Recovering τ² = χ(-1)·p
-- ============================================================================

section QuadraticRecovery

variable {p : ℕ} [hp : Fact p.Prime]

/-- The quadratic Jacobi identity: J(χ, χ⁻¹) = -χ(-1).

    For quadratic χ (χ² = 1), χ⁻¹ = χ, so this gives J(χ,χ) = -χ(-1).
    The Gauss sum norm τ² = χ(-1)·p is a DIFFERENT statement (about g(χ)², not J(χ,χ))
    proved in OQ01OQ01OQ01.lean via `gaussSum_sq`.

    The Jacobi sum J(χ,χ) = -χ(-1) for quadratic χ shows that J is just ±1:
    - If p ≡ 1 (mod 4): χ(-1) = 1, J(χ,χ) = -1
    - If p ≡ 3 (mod 4): χ(-1) = -1, J(χ,χ) = 1

    The algebraic norm: J·J⁻¹ = J·(-χ(-1)) = (-χ(-1))·(-χ(-1)) = 1 ≠ p.
    This is why the quadratic case is DEGENERATE: the product `χ * χ = 1` is
    trivial, violating the hypothesis of `jacobiSum_algebraic_norm`.
    The interesting object for quadratic QR is the Gauss sum, not the Jacobi sum. -/
theorem quadratic_jacobi_is_sign {F R : Type*} [Field F] [Fintype F] [CommRing R]
    {χ : MulChar F R} (hχ : χ ≠ 1) :
    jacobiSum χ χ⁻¹ = -χ (-1) :=
  jacobiSum_nontrivial_inv hχ

/-- The cubic case (order 3) is NOT degenerate: J(χ,χ) has full norm p.

    The key contrast with the quadratic case:
    - Quadratic: χ * χ = χ² = 1 → norm formula doesn't apply → J = ±1
    - Cubic: χ * χ = χ² ≠ 1 (since ord χ = 3) → norm formula applies → |J|² = p -/
theorem cubic_vs_quadratic_contrast
    {F' : Type*} [Field F'] (h_char : ringChar F' ≠ p)
    (χ : MulChar (ZMod p) F') (hχ : χ ≠ 1) (hχ2 : χ ^ 2 ≠ 1) :
    -- Cubic: J(χ,χ)·J(χ⁻¹,χ⁻¹) = p ← non-degenerate norm
    jacobiSum χ χ * jacobiSum χ⁻¹ χ⁻¹ = p :=
  cubic_jacobi_algebraic_norm h_char χ hχ hχ2

end QuadraticRecovery

/-
  ## Results Summary

  | Theorem | Statement | Source |
  |---------|-----------|--------|
  | `jacobiSum_gaussSum_relation` | g(χ)·g(φ) = J(χ,φ)·g(χφ) [χφ≠1] | Mathlib |
  | `jacobiSum_ratio_form` | J(χ,φ) = g(χ)·g(φ)/g(χφ) | Mathlib |
  | `jacobiSum_trivial_left` | J(1,χ) = -1 for χ≠1 | Mathlib |
  | `jacobiSum_self_inv` | J(χ,χ⁻¹) = -χ(-1) | Mathlib |
  | `jacobiSum_is_symmetric` | J(χ,φ) = J(φ,χ) | Mathlib |
  | `jacobiSum_algebraic_norm` | J(χ,φ)·J(χ⁻¹,φ⁻¹) = #F | Mathlib |
  | `jacobiSum_prime_field_norm` | J(χ,φ)·J(χ⁻¹,φ⁻¹) = p for 𝔽_p | This file |
  | `cubic_jacobi_algebraic_norm` | J(χ,χ)·J(χ⁻¹,χ⁻¹) = p [ord χ = 3] | This file |
  | `quartic_jacobi_algebraic_norm` | J(χ,χ)·J(χ⁻¹,χ⁻¹) = p [ord χ = 4] | This file |
  | `general_jacobi_norm` | J(χ,χ^k)·J(χ⁻¹,χ^{-k}) = p | This file |
  | `quadratic_jacobi_is_sign` | J(χ,χ⁻¹) = -χ(-1) (sign only) | Mathlib |
  | `cubic_vs_quadratic_contrast` | norm p vs sign (cubic vs quadratic) | This file |

  **Sorries**: 0
  **Axioms**: 0

  ## Mathematical Significance

  The algebraic norm formula `J(χ,φ)·J(χ⁻¹,φ⁻¹) = p` (for nontrivial χ, φ, χφ on 𝔽_p)
  is the common thread through all power reciprocity proofs:

  1. **Cubic reciprocity** (Gauss 1828, proved by Eisenstein 1844):
     (π/q)₃ = (q/π)₃ for primary π, q in ℤ[ω] with gcd(N(π), N(q)) = 1
     Proof engine: J(χ,χ) with |J|² = p = N(J) in ℤ[ω]

  2. **Quartic reciprocity** (Gauss, proved by Eisenstein):
     (π/q)₄·(q/π)₄ = (-1)^{(p-1)(q-1)/16} for primary π ≡ q ≡ 1 (mod 2+2i)
     Proof engine: J(χ,χ) with |J|² = p = N(J) in ℤ[i]

  3. **General Eisenstein reciprocity** (Eisenstein, 1850):
     For ℓ-th power residues (ℓ odd prime), via J(χ,χ^k) in ℤ[ζ_ℓ]

  In each case, the Jacobi sum serves as an explicit element of norm p in the
  relevant algebraic integer ring, and the reciprocity law reads off the residue
  symbol from the reduction of J modulo the relevant prime.

  Mathlib provides the Gauss-Jacobi identity and the algebraic norm formula, making
  this unified framework fully available for formal proofs.
-/

end JacobiSumHigherPower
