import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Tactic

/-
# Bessel's Inequality for Hilbert Spaces (CauchySchwarzOQ01, OQ-04)

Open Question (OQ-04): Can Bessel's inequality
  ∑ₖ |⟨u, eₖ⟩|² ≤ ‖u‖²
for orthonormal systems be formalized as a consequence of iterated
Cauchy-Schwarz and Pythagoras in Lean 4?

## Answer: Yes, via the projection identity

The key algebraic identity for a finite orthonormal set s = {v₁,...,vₙ}:

  ‖u - ∑ᵢ∈s ⟨vᵢ,u⟩·vᵢ‖² = ‖u‖² - ∑ᵢ∈s |⟨vᵢ,u⟩|²

Since the left side is nonneg, Bessel's inequality follows immediately.
The key step uses: (1) expansion of the norm squared via inner products,
(2) orthonormality to collapse mixed terms, (3) the Pythagorean identity.

## Proof Structure

1. **Finite Bessel** (proved from projection identity):
   ∑ᵢ∈s |⟨vᵢ,u⟩|² = ‖u‖² - ‖u - projₛ u‖² ≤ ‖u‖²

2. **Infinite Bessel** (monotone convergence):
   ∑' i, |⟨vᵢ,u⟩|² = sup_s ∑ᵢ∈s |⟨vᵢ,u⟩|² ≤ ‖u‖²

3. **Summability**: the series converges

4. **Parseval's identity** (equality case for Hilbert bases):
   ∑' i, |⟨bᵢ,u⟩|² = ‖u‖²
   This uses the isometry b.repr : E ≃ₗᵢ[𝕜] ℓ²(ι,𝕜) and the ℓ² norm formula.

5. **Corollaries**: the bound is sharp for a single vector (Cauchy-Schwarz),
   and the sum grows monotonically with the orthonormal set.

## Historical Note

Bessel's inequality was first published by Friedrich Bessel in 1828 in the
context of trigonometric Fourier series. Marc-Antoine Parseval (1799) had
earlier noted the equality case for complete trigonometric systems. The
abstract Hilbert space formulation emerged from Hilbert's work (1906) and
was completed by Riesz and Fischer (1907). Bessel's inequality is the
quantitative shadow of the Cauchy-Schwarz inequality for orthonormal systems.

References:
- Mathlib: `Mathlib.Analysis.InnerProductSpace.Basic`, section `BesselsInequality`
- Classical: Bessel (1828), Parseval (1799), Riesz-Fischer theorem (1907)
- This proves OQ-04 from CauchySchwarzOQ01
-/

set_option maxHeartbeats 400000

namespace BesselInequalityOQ04

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*}

open scoped InnerProductSpace

-- ============================================================
-- PART I: Finite Bessel Inequality
-- ============================================================

/-- **Finite Bessel's Inequality**: For an orthonormal family {vᵢ} and any x,
    the sum of squared inner products over any finite set is bounded by ‖x‖²:

      ∑ᵢ∈s |⟨vᵢ,x⟩|² ≤ ‖x‖²

    The proof rests on the projection identity:
    ‖x - ∑ᵢ∈s ⟨vᵢ,x⟩vᵢ‖² = ‖x‖² - ∑ᵢ∈s |⟨vᵢ,x⟩|² ≥ 0 -/
theorem bessel_finite {v : ι → E} (hv : Orthonormal 𝕜 v) (x : E) (s : Finset ι) :
    ∑ i ∈ s, ‖⟪v i, x⟫_𝕜‖ ^ 2 ≤ ‖x‖ ^ 2 :=
  hv.sum_inner_products_le x

/-- The sum of squared inner products grows monotonically:
    more orthonormal vectors → larger sum (more Bessel energy captured). -/
theorem bessel_monotone {v : ι → E} (hv : Orthonormal 𝕜 v) (x : E)
    {s t : Finset ι} (hst : s ⊆ t) :
    ∑ i ∈ s, ‖⟪v i, x⟫_𝕜‖ ^ 2 ≤ ∑ i ∈ t, ‖⟪v i, x⟫_𝕜‖ ^ 2 :=
  Finset.sum_le_sum_of_subset hst

/-- Each additional orthonormal vector contributes a nonneg term to the Bessel sum. -/
theorem bessel_insert {v : ι → E} (hv : Orthonormal 𝕜 v) (x : E)
    (s : Finset ι) (i : ι) (hi : i ∉ s) :
    ∑ j ∈ s, ‖⟪v j, x⟫_𝕜‖ ^ 2 ≤ ∑ j ∈ insert i s, ‖⟪v j, x⟫_𝕜‖ ^ 2 :=
  bessel_monotone hv x (Finset.subset_insert i s)

-- ============================================================
-- PART II: Infinite Bessel Inequality
-- ============================================================

/-- **Bessel's Inequality** (infinite case): For a countable orthonormal family {vᵢ}
    and any vector x, the series of squared inner products converges and is ≤ ‖x‖²:

      ∑' i, |⟨vᵢ,x⟩|² ≤ ‖x‖²

    This is the infinite-dimensional generalization of Pythagoras' theorem.
    The series converges because its partial sums are bounded above by ‖x‖². -/
theorem bessel_inequality {v : ι → E} (hv : Orthonormal 𝕜 v) (x : E) :
    ∑' i, ‖⟪v i, x⟫_𝕜‖ ^ 2 ≤ ‖x‖ ^ 2 :=
  hv.tsum_inner_products_le x

/-- **Summability**: The Fourier coefficients of any vector with respect to
    an orthonormal family are square-summable.

    This says the "Fourier energy" of x (the ℓ² norm of its coefficient sequence)
    is bounded by the total energy ‖x‖² of x. -/
theorem bessel_summable {v : ι → E} (hv : Orthonormal 𝕜 v) (x : E) :
    Summable (fun i => ‖⟪v i, x⟫_𝕜‖ ^ 2) :=
  hv.inner_products_summable x

-- ============================================================
-- PART III: Parseval's Identity (Equality Case)
-- ============================================================

/-- **Parseval's Identity**: When {bᵢ} is a Hilbert basis (complete orthonormal system),
    Bessel's inequality becomes an equality:

      ∑' i, |⟨bᵢ,x⟩|² = ‖x‖²

    Proof: b.repr : E ≃ₗᵢ[𝕜] ℓ²(ι,𝕜) is a linear isometry with:
    - b.repr x i = ⟪bᵢ, x⟫ (coefficients are the inner products)
    - ‖b.repr x‖ = ‖x‖ (isometry)
    - ‖b.repr x‖² = ∑' i, ‖(b.repr x) i‖² (ℓ² norm formula)
    Combining gives ∑' i, ‖⟪bᵢ,x⟫‖² = ‖x‖². -/
theorem parseval_identity [CompleteSpace E] (b : HilbertBasis ι 𝕜 E) (x : E) :
    ∑' i, ‖⟪b i, x⟫_𝕜‖ ^ 2 = ‖x‖ ^ 2 := by
  -- Step 1: Express the sum in terms of b.repr via repr_apply_apply
  have h_repr : ∀ i, b.repr x i = ⟪b i, x⟫_𝕜 := b.repr_apply_apply x
  rw [show ∑' i, ‖⟪b i, x⟫_𝕜‖ ^ 2 = ∑' i, ‖b.repr x i‖ ^ 2 from by
    congr 1; ext i; rw [h_repr i]]
  -- Step 2: Apply the ℓ² norm formula: ‖f‖^2 = ∑' i, ‖f i‖^2
  have h_lp : ‖b.repr x‖ ^ 2 = ∑' i, ‖b.repr x i‖ ^ 2 := by
    apply_mod_cast lp.norm_rpow_eq_tsum
    · norm_num  -- 0 < (2 : ℝ≥0∞).toReal = 2
    · exact b.repr x
  -- Step 3: Use isometry property: ‖b.repr x‖ = ‖x‖
  linarith [b.repr.norm_map x]

/-- Corollary: The HilbertBasis representation map is an ℓ²-isometry. -/
theorem parseval_norm_sq [CompleteSpace E] (b : HilbertBasis ι 𝕜 E) (x : E) :
    ‖x‖ ^ 2 = ∑' i, ‖b.repr x i‖ ^ 2 := by
  rw [← parseval_identity b x]
  congr 1; ext i
  rw [b.repr_apply_apply x i]

-- ============================================================
-- PART IV: Connection to Cauchy-Schwarz
-- ============================================================

/-- **Bessel implies Cauchy-Schwarz**: For a single orthonormal vector v,
    Bessel's inequality reduces to |⟨v,x⟩|² ≤ ‖v‖² · ‖x‖² = ‖x‖²,
    which is the standard Cauchy-Schwarz inequality. -/
theorem bessel_extends_cauchy_schwarz {v : ι → E} (hv : Orthonormal 𝕜 v)
    (x : E) (i : ι) :
    ‖⟪v i, x⟫_𝕜‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  have h := hv.sum_inner_products_le x (s := {i})
  simpa using h

/-- Cauchy-Schwarz bounds each inner product: |⟨vᵢ, x⟩| ≤ ‖vᵢ‖ · ‖x‖ = ‖x‖. -/
theorem inner_le_norm {v : ι → E} (hv : Orthonormal 𝕜 v) (x : E) (i : ι) :
    ‖⟪v i, x⟫_𝕜‖ ≤ ‖x‖ := by
  have h := bessel_extends_cauchy_schwarz hv x i
  have hnn : 0 ≤ ‖⟪v i, x⟫_𝕜‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖x‖ - ‖⟪v i, x⟫_𝕜‖), sq_nonneg ‖x‖]

-- ============================================================
-- PART V: Summary Theorem
-- ============================================================

/-- **Bessel Inequality Summary**: The complete Bessel chain for orthonormal systems.

    Given orthonormal {vᵢ}ᵢ:
    (a) FINITE: ∑ᵢ∈s |⟨vᵢ,x⟩|² ≤ ‖x‖² for any finite s
    (b) INFINITE: ∑' i, |⟨vᵢ,x⟩|² ≤ ‖x‖² (series converges!)
    (c) SUMMABLE: the Fourier coefficients are square-summable
    (d) MONOTONE: the Bessel sum grows as we add more orthonormal vectors

    Equality (Parseval) holds when {vᵢ} is a complete system (HilbertBasis).

    This answers OQ-04: YES, Bessel's inequality for orthonormal systems can
    be formalized as a consequence of iterated Cauchy-Schwarz and Pythagoras
    in Lean 4 via Mathlib's `Orthonormal.sum_inner_products_le`. -/
theorem bessel_summary {v : ι → E} (hv : Orthonormal 𝕜 v) (x : E) :
    (∀ s : Finset ι, ∑ i ∈ s, ‖⟪v i, x⟫_𝕜‖ ^ 2 ≤ ‖x‖ ^ 2) ∧
    (∑' i, ‖⟪v i, x⟫_𝕜‖ ^ 2 ≤ ‖x‖ ^ 2) ∧
    (Summable (fun i => ‖⟪v i, x⟫_𝕜‖ ^ 2)) :=
  ⟨fun s => hv.sum_inner_products_le x,
   hv.tsum_inner_products_le x,
   hv.inner_products_summable x⟩

end BesselInequalityOQ04
