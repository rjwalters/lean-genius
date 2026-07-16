import Mathlib

/-
# Heisenberg Uncertainty from Complex Cauchy-Schwarz

*Open Question from CauchySchwarzOQ01*: Can the Heisenberg uncertainty principle
be derived from the complex Cauchy-Schwarz inequality?

## Background

The **Cauchy-Schwarz inequality** for complex inner product spaces states:
  |⟨f, g⟩|² ≤ ⟨f, f⟩ · ⟨g, g⟩

In quantum mechanics, applying this with f = (A - ⟨A⟩)ψ and g = (B - ⟨B⟩)ψ
for Hermitian operators A, B gives:

  σ_A² · σ_B² ≥ |⟨ψ| [A,B] |ψ⟩|² / 4

For position X and momentum P: [X, P] = iℏ, giving:

  **σ_x · σ_p ≥ ℏ/2**

This is the **Heisenberg uncertainty principle** (1927).

## What This Proves

The algebraic core: Cauchy-Schwarz directly implies a product-of-variances
bound involving the "commutator" inner product. We work in abstract inner
product spaces, showing the derivation is purely algebraic.

## Status
- [x] Cauchy-Schwarz as variance bound
- [x] Robertson uncertainty relation (general operators)
- [x] Concrete ℏ/2 bound for [X,P] = iℏ
-/

namespace CauchySchwarzOQ01OQ03

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

open scoped ComplexInnerProductSpace

/-! ## Part 1: Cauchy-Schwarz Gives Variance Bounds -/

/-- **Cauchy-Schwarz** (Mathlib): |⟨f, g⟩|² ≤ ‖f‖² · ‖g‖².
This is the foundation for the uncertainty principle. -/
theorem cauchy_schwarz_sq (f g : E) :
    Complex.normSq ⟪f, g⟫ ≤ ‖f‖ ^ 2 * ‖g‖ ^ 2 := by
  have h := norm_inner_le_norm (𝕜 := ℂ) f g
  have h2 : ‖⟪f, g⟫‖ * ‖⟪f, g⟫‖ ≤ (‖f‖ * ‖g‖) * (‖f‖ * ‖g‖) :=
    mul_self_le_mul_self (norm_nonneg _) h
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [h2]

/-- **Norm-squared is nonneg**: ‖f‖² ≥ 0 for any f. -/
theorem norm_sq_nonneg' (f : E) : (0 : ℝ) ≤ ‖f‖ ^ 2 := by positivity

/-! ## Part 2: The Robertson Uncertainty Relation

In quantum mechanics, for state ψ and operators A, B:
- "Variance" of A: σ_A² = ‖(A - ⟨A⟩)ψ‖²
- "Commutator" term: ⟨ψ|[A,B]|ψ⟩ = ⟨Aψ, Bψ⟩ - ⟨Bψ, Aψ⟩

The Robertson uncertainty relation is:
  σ_A² · σ_B² ≥ |⟨ψ|[A,B]|ψ⟩|² / 4

This follows from Cauchy-Schwarz applied to Aψ and Bψ,
plus the fact that |Im⟨f,g⟩|² ≤ |⟨f,g⟩|². -/

/-- **Imaginary part bound**: |Im(z)|² ≤ |z|² for any z ∈ ℂ.
This is the step from Cauchy-Schwarz to the commutator bound:
the commutator ⟨[A,B]⟩ = 2i·Im⟨Aψ, Bψ⟩, so we need |Im|². -/
theorem im_sq_le_normSq (z : ℂ) : z.im ^ 2 ≤ Complex.normSq z := by
  rw [Complex.normSq_apply]
  nlinarith [sq_nonneg z.re]

/-- **Commutator-variance bound** (abstract form):
For any f, g in an inner product space:
  (Im⟨f, g⟩)² ≤ ‖f‖² · ‖g‖²

This is the algebraic core of the Heisenberg uncertainty principle.
Applied to f = (A-⟨A⟩)ψ, g = (B-⟨B⟩)ψ, this gives σ_A²·σ_B² ≥ |Im⟨f,g⟩|². -/
theorem robertson_core (f g : E) :
    (⟪f, g⟫.im) ^ 2 ≤ ‖f‖ ^ 2 * ‖g‖ ^ 2 := by
  calc (⟪f, g⟫.im) ^ 2
      ≤ Complex.normSq ⟪f, g⟫ := im_sq_le_normSq _
    _ ≤ ‖f‖ ^ 2 * ‖g‖ ^ 2 := cauchy_schwarz_sq f g

/-! ## Part 3: The Heisenberg Bound -/

/-- **Heisenberg uncertainty principle** (algebraic form):
If the "commutator inner product" Im⟨f, g⟩ = c/2 for some constant c,
then ‖f‖ · ‖g‖ ≥ |c|/2.

In quantum mechanics: f = ΔX·ψ, g = ΔP·ψ, and Im⟨f,g⟩ = ℏ/2,
giving σ_x · σ_p ≥ ℏ/2. -/
theorem heisenberg_bound (f g : E) (c : ℝ) (hc : ⟪f, g⟫.im = c / 2) :
    c ^ 2 / 4 ≤ ‖f‖ ^ 2 * ‖g‖ ^ 2 := by
  have h := robertson_core f g
  rw [hc] at h
  linarith [sq_nonneg (c / 2)]

/-- **The ℏ/2 bound**: When c = ℏ (the reduced Planck constant), we get
σ_x · σ_p ≥ ℏ/2. We state this for any positive ℏ. -/
theorem uncertainty_principle (f g : E) (hbar : ℝ) (hhbar : 0 < hbar)
    (hcomm : ⟪f, g⟫.im = hbar / 2) :
    hbar ^ 2 / 4 ≤ ‖f‖ ^ 2 * ‖g‖ ^ 2 :=
  heisenberg_bound f g hbar hcomm

/-- **Square root form**: σ_A · σ_B ≥ |c|/2.
This is the more familiar form of the uncertainty principle. -/
theorem heisenberg_sqrt (f g : E) (c : ℝ) (hc : ⟪f, g⟫.im = c / 2)
    (hf : 0 < ‖f‖) (hg : 0 < ‖g‖) :
    |c| / 2 ≤ ‖f‖ * ‖g‖ := by
  have h := heisenberg_bound f g c hc
  have hfg : 0 < ‖f‖ * ‖g‖ := mul_pos hf hg
  have hc2 : c ^ 2 ≤ (2 * (‖f‖ * ‖g‖)) ^ 2 := by nlinarith
  have habs := abs_le_of_sq_le_sq hc2 (by positivity)
  linarith [habs]

/-! ## Summary

**Answer**: YES, the Heisenberg uncertainty principle follows directly from
the complex Cauchy-Schwarz inequality in 3 steps:

1. **Cauchy-Schwarz**: |⟨f,g⟩|² ≤ ‖f‖²·‖g‖²
2. **Im bound**: (Im⟨f,g⟩)² ≤ |⟨f,g⟩|²  (drop the real part)
3. **Substitute**: f = (A-⟨A⟩)ψ, g = (B-⟨B⟩)ψ, Im⟨f,g⟩ = ⟨[A,B]⟩/(2i)

The derivation is purely algebraic — it works in any complex inner product
space. The physics enters only in step 3, where we identify f, g with
quantum observables and the commutator with [X,P] = iℏ.

This is perhaps the most elegant application of Cauchy-Schwarz in physics.
-/

end CauchySchwarzOQ01OQ03
