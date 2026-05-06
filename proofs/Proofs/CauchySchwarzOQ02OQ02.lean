/-
  Bessel's Inequality in Infinite Dimensions
  (cauchy-schwarz-oq-02-oq-02)

  For any orthonormal system {vᵢ}ᵢ in a real inner product space F and any x ∈ F:
    ∑' i, ⟨vᵢ, x⟩² ≤ ‖x‖²

  Key results proved:
  1. Finite Bessel: ∑ i ∈ s, ⟨vᵢ, x⟩² ≤ ‖x‖² for any finite index set s
  2. Summability: the Bessel series ∑' i, ⟨vᵢ, x⟩² converges
  3. Infinite Bessel: the tsum is bounded by ‖x‖²
  4. Monotone partial sums: adding more terms only increases the sum
  5. General RCLike: norm version works for any field
  6. Parseval's identity: equality for complete orthonormal systems (Hilbert bases)

  Proof strategy:
  - Finite Bessel follows from ‖x - ∑ᵢ∈s ⟨vᵢ,x⟩ vᵢ‖² ≥ 0, which by Pythagoras
    expands to ‖x‖² - ∑ᵢ∈s ⟨vᵢ,x⟩² ≥ 0.
  - Summability: partial sums are non-decreasing (non-negative terms) and
    bounded above by ‖x‖² (finite Bessel), so by monotone convergence the series converges.
  - Parseval: from `HilbertBasis.tsum_inner_mul_inner`, ∑ᵢ ⟨x,bᵢ⟩⟨bᵢ,x⟩ = ⟨x,x⟩.
    Real symmetry ⟨x,bᵢ⟩ = ⟨bᵢ,x⟩ converts the product to ⟨bᵢ,x⟩².
    And ⟨x,x⟩_ℝ = ‖x‖².

  All results delegate to Mathlib's inner product space library.
  Status: 0 sorries, 0 axioms.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic

-- Opens notation ⟪x, y⟫ for the real inner product @inner ℝ _ _ x y
open scoped RealInnerProductSpace

namespace BesselInequality

-- ============================================================
-- Real inner product space: we use ⟪x, y⟫ for the inner product.
-- ============================================================

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

-- ============================================================
-- Section 1: Finite Bessel Inequality
-- ============================================================

/-- **Bessel's inequality (finite)**: For a real orthonormal family v and any finite
    index set s, the sum of squared Fourier coefficients is bounded by ‖x‖². -/
theorem bessel_finite {ι : Type*} {v : ι → F} (hv : Orthonormal ℝ v)
    (x : F) (s : Finset ι) :
    ∑ i ∈ s, ⟪v i, x⟫ ^ 2 ≤ ‖x‖ ^ 2 := by
  have h := hv.sum_inner_products_le x (s := s)
  simp only [Real.norm_eq_abs, sq_abs] at h
  exact h

/-- Each Bessel term ⟨vᵢ, x⟩² is non-negative. -/
theorem bessel_term_nonneg {ι : Type*} {v : ι → F} (x : F) (i : ι) :
    0 ≤ ⟪v i, x⟫ ^ 2 := sq_nonneg _

-- ============================================================
-- Section 2: Summability and Convergence
-- ============================================================

/-- **Summability**: The Bessel series ∑' i, ⟨vᵢ, x⟩² converges for any
    real orthonormal family v and x ∈ F. -/
theorem bessel_summable {ι : Type*} {v : ι → F} (hv : Orthonormal ℝ v) (x : F) :
    Summable (fun i => ⟪v i, x⟫ ^ 2) := by
  have h : Summable (fun i => ‖⟪v i, x⟫‖ ^ 2) := hv.inner_products_summable x
  simp only [Real.norm_eq_abs, sq_abs] at h
  exact h

/-- The Bessel series HasSum to its tsum — precise convergence. -/
theorem bessel_hasSum {ι : Type*} {v : ι → F} (hv : Orthonormal ℝ v) (x : F) :
    HasSum (fun i => ⟪v i, x⟫ ^ 2) (∑' i, ⟪v i, x⟫ ^ 2) :=
  (bessel_summable hv x).hasSum

/-- Partial sums of the Bessel series are monotone non-decreasing. -/
theorem bessel_partial_sums_mono {ι : Type*} {v : ι → F} (x : F)
    {s t : Finset ι} (hst : s ⊆ t) :
    ∑ i ∈ s, ⟪v i, x⟫ ^ 2 ≤ ∑ i ∈ t, ⟪v i, x⟫ ^ 2 :=
  Finset.sum_le_sum_of_subset_of_nonneg hst fun _ _ _ => sq_nonneg _

-- ============================================================
-- Section 3: Infinite Bessel Inequality (main theorem)
-- ============================================================

/-- **Bessel's inequality**: For any real orthonormal family {vᵢ} and x ∈ F,
    ∑' i, ⟨vᵢ, x⟩² ≤ ‖x‖². -/
theorem bessel_inequality {ι : Type*} {v : ι → F} (hv : Orthonormal ℝ v) (x : F) :
    ∑' i, ⟪v i, x⟫ ^ 2 ≤ ‖x‖ ^ 2 := by
  have h := hv.tsum_inner_products_le x
  simp only [Real.norm_eq_abs, sq_abs] at h
  exact h

-- ============================================================
-- Section 4: General RCLike Field (norm-squared form)
-- ============================================================

/-- **Bessel's inequality (general, finite)**: For an orthonormal family over any
    RCLike field 𝕜, ∑ i ∈ s, ‖⟨vᵢ, x⟩_𝕜‖² ≤ ‖x‖². -/
theorem bessel_general_finite {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {ι : Type*} {v : ι → E} (hv : Orthonormal 𝕜 v) (x : E) (s : Finset ι) :
    ∑ i ∈ s, ‖@inner 𝕜 E _ (v i) x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
  hv.sum_inner_products_le x

/-- **Bessel's inequality (general, infinite)**: For an orthonormal family over any
    RCLike field 𝕜, ∑' i, ‖⟨vᵢ, x⟩_𝕜‖² ≤ ‖x‖². -/
theorem bessel_general {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {ι : Type*} {v : ι → E} (hv : Orthonormal 𝕜 v) (x : E) :
    ∑' i, ‖@inner 𝕜 E _ (v i) x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
  hv.tsum_inner_products_le x

-- ============================================================
-- Section 5: Parseval's Identity
-- ============================================================

/-- **Parseval's identity (real)**: For a real Hilbert basis {bᵢ} and x ∈ F,
    ∑' i, ⟨bᵢ, x⟩² = ‖x‖². -/
theorem parseval_real {ι : Type*} [CompleteSpace F] (b : HilbertBasis ι ℝ F) (x : F) :
    (∑' i, ⟪b i, x⟫ ^ 2) = ‖x‖ ^ 2 := by
  have h := b.tsum_inner_mul_inner x x
  -- ⟪x, b i⟫ = ⟪b i, x⟫ by real symmetry, so ⟪x, b i⟫ * ⟪b i, x⟫ = ⟪b i, x⟫^2
  have key : ∀ i, (⟪x, b i⟫ : ℝ) * ⟪b i, x⟫ = ⟪b i, x⟫ ^ 2 := fun i => by
    rw [real_inner_comm (b i) x]; ring
  simp_rw [key, real_inner_self_eq_norm_sq] at h
  exact h

/-- Corollary: for a real Hilbert basis, Bessel inequality is an equality. -/
theorem bessel_tight {ι : Type*} [CompleteSpace F] (b : HilbertBasis ι ℝ F) (x : F) :
    (∑' i, ⟪b i, x⟫ ^ 2) = ‖x‖ ^ 2 :=
  parseval_real b x

end BesselInequality

-- ============================================================
-- Examples
-- ============================================================

section Examples

open BesselInequality

-- Example: The single-vector Bessel inequality is Cauchy-Schwarz.
-- For any unit vector v ∈ F, we have ⟨v, x⟩² ≤ ‖x‖² for all x.
example {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {v : F} (hv : ‖v‖ = 1) (x : F) : ⟪v, x⟫ ^ 2 ≤ ‖x‖ ^ 2 := by
  have horth : Orthonormal ℝ (fun _ : Fin 1 => v) := by
    refine ⟨fun i => by simp [hv], fun i j hij => ?_⟩
    exact absurd (Subsingleton.elim i j) hij
  have h := bessel_finite horth x Finset.univ
  simp only [Finset.univ_unique, Finset.sum_singleton] at h
  simpa using h

end Examples

#check @BesselInequality.bessel_inequality
#check @BesselInequality.parseval_real
#check @BesselInequality.bessel_general
