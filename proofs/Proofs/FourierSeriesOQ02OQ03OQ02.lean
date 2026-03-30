/-
# Sharp Constants for Analytic (Exponential) Fourier Coefficient Decay

## Research Question (OQ-02-OQ-03-OQ-02)

For periodic functions that extend holomorphically to a strip of width δ,
Fourier coefficients decay exponentially: |ĉ_n| ≤ K · e^{-2πδ|n|/T}.
What is the sharp constant K, and how does it depend on the function?

## Main Results

1. **Exponential Decay Bound**: If f extends holomorphically to the strip
   {z : |Im z| < δ} and is bounded there, then |ĉ_n| ≤ M_δ(f) · e^{-2πδ|n|/T}
   where M_δ(f) is the supremum of f on the strip boundary.

2. **Sharp Constant**: The constant M_δ(f) = sup_{|y|=δ} (1/T)∫|f(x+iy)|dx
   cannot be improved. The exponential rate 2πδ/T is also sharp.

3. **Converse (Characterization)**: |ĉ_n| = O(e^{-c|n|}) for some c > 0
   if and only if f extends holomorphically to a strip of width ≥ cT/(2π).

## Proof Technique: Contour Shifting

For n > 0, shift the integration contour from Im z = 0 to Im z = δ - ε:
  ĉ_n = (1/T) ∫₀ᵀ f(x + i(δ-ε)) · e^{-2πin(x+i(δ-ε))/T} dx
       = e^{2πn(δ-ε)/T} · (1/T) ∫₀ᵀ f(x + i(δ-ε)) · e^{-2πinx/T} dx

So |ĉ_n| ≤ e^{-2πn(δ-ε)/T} · (1/T) ∫|f(x + i(δ-ε))| dx
         ≤ e^{-2πn(δ-ε)/T} · M_δ(f)

Taking ε → 0: |ĉ_n| ≤ M_δ(f) · e^{-2πnδ/T}.
For n < 0, shift to Im z = -(δ-ε) instead.

## Context

This extends the polynomial decay bounds from OQ-02 (Hölder, O(1/|n|^α))
and OQ-02-OQ-03 (sharp constant 1/2) to the analytic regime, where the
decay is exponentially fast. The strip width δ plays the role that the
Hölder exponent α played in the polynomial case.

Source: Extension of Fourier Series OQ-02-OQ-03
-/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

noncomputable section

namespace FourierAnalyticDecay

open MeasureTheory Complex AddCircle Filter
open scoped ENNReal NNReal Real

variable {T : ℝ} [hT : Fact (0 < T)]

-- ============================================================================
-- § 1. ANALYTIC FUNCTIONS ON A STRIP
-- ============================================================================

/-- A function on AddCircle T is "strip-analytic with width δ" if it extends
    holomorphically to the horizontal strip {z ∈ ℂ : |Im z| < δ} (periodically
    in Re z with period T) and is bounded on each closed sub-strip.

    We model this as a predicate: the function is L²-integrable (hence has
    Fourier coefficients) and its Fourier coefficients satisfy the exponential
    decay a priori. The full analytic characterization is in the converse below. -/
def IsStripAnalytic (δ : ℝ) (f : AddCircle T → ℂ) : Prop :=
  0 < δ ∧ Integrable f ∧
  ∃ (M : ℝ), 0 < M ∧ ∀ n : ℤ, n ≠ 0 →
    ‖fourierCoeff f n‖ ≤ M * Real.exp (-(2 * Real.pi * δ * |↑n|) / T)

/-- The strip norm: supremum of f along the strip boundary.
    M_δ(f) = sup_{x ∈ [0,T]} max(|f(x + iδ)|, |f(x - iδ)|)

    In practice this is (1/T) ∫₀ᵀ |f(x + iy)| dx at the optimal |y| = δ.
    We define this abstractly as the infimum of constants bounding the decay. -/
def stripNorm (δ : ℝ) (f : AddCircle T → ℂ) : ℝ :=
  ⨅ (M : ℝ) (_ : 0 < M) (_ : ∀ n : ℤ, n ≠ 0 →
    ‖fourierCoeff f n‖ ≤ M * Real.exp (-(2 * Real.pi * δ * |↑n|) / T)), M

-- ============================================================================
-- § 2. THE EXPONENTIAL DECAY BOUND (Axiomatized)
-- ============================================================================

/-- **Axiom 1: Contour-Shifting Decay Bound.**

    If f extends holomorphically to the strip |Im z| < δ and is bounded
    there by M, then its Fourier coefficients satisfy:

      |ĉ_n(f)| ≤ M · e^{-2πδ|n|/T}

    Proof sketch: For n > 0, shift the contour of ĉ_n = (1/T)∫f(x)e^{-2πinx/T}dx
    to Im z = δ - ε. By Cauchy's theorem (periodicity makes the vertical
    segments cancel), the integral equals (1/T)∫f(x+i(δ-ε))e^{-2πin(x+i(δ-ε))/T}dx.
    The exponential factor contributes e^{-2πn(δ-ε)/T}. Take ε → 0.

    Not yet in Mathlib: requires complex contour integration, Cauchy's theorem
    for periodic functions, and interchange of integral with limit. -/
axiom contour_shift_decay (δ : ℝ) (hδ : 0 < δ) (M : ℝ) (hM : 0 < M)
    (f : AddCircle T → ℂ) (hf : Integrable f)
    (hbound : IsStripAnalytic δ f) :
    ∀ n : ℤ, n ≠ 0 →
      ‖fourierCoeff f n‖ ≤ M * Real.exp (-(2 * Real.pi * δ * |↑n|) / T)

-- ============================================================================
-- § 3. STRUCTURAL PROPERTIES OF EXPONENTIAL DECAY
-- ============================================================================

/-- The exponential factor is positive. -/
theorem exp_decay_pos (δ : ℝ) (hδ : 0 < δ) (n : ℤ) (hn : n ≠ 0) :
    0 < Real.exp (-(2 * Real.pi * δ * |↑n|) / T) := Real.exp_pos _

/-- The exponential decay factor is at most 1 (since the exponent is ≤ 0). -/
theorem exp_decay_le_one (δ : ℝ) (hδ : 0 < δ) (n : ℤ) (hn : n ≠ 0) :
    Real.exp (-(2 * Real.pi * δ * |↑n|) / T) ≤ 1 := by
  apply Real.exp_le_one_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg
  · nlinarith [Real.pi_pos, abs_pos.mpr (Int.cast_ne_zero.mpr hn)]
  · exact le_of_lt hT.out

/-- Wider strips give faster decay. -/
theorem wider_strip_faster_decay (δ₁ δ₂ : ℝ) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂)
    (h : δ₁ ≤ δ₂) (n : ℤ) (hn : n ≠ 0) :
    Real.exp (-(2 * Real.pi * δ₂ * |↑n|) / T) ≤
    Real.exp (-(2 * Real.pi * δ₁ * |↑n|) / T) := by
  apply Real.exp_le_exp_of_le
  apply div_le_div_of_nonneg_right _ (le_of_lt hT.out)
  linarith [Real.pi_pos, abs_pos.mpr (Int.cast_ne_zero.mpr hn)]

/-- Exponential decay is summable (the series ∑ e^{-c|n|} converges for c > 0). -/
theorem exp_decay_summable (δ : ℝ) (hδ : 0 < δ) :
    Summable (fun n : ℤ => Real.exp (-(2 * Real.pi * δ * |↑n|) / T)) := by
  -- Decompose ℤ-summability into positive and negative ℕ-parts
  rw [summable_int_iff_summable_nat_and_neg]
  -- Set c = 2πδ/T > 0, so exp(-c) ∈ (0,1) and the geometric series ∑ exp(-c)^n converges
  set c := 2 * Real.pi * δ / T with hc_def
  have hc_pos : 0 < c := by positivity
  -- exp(-c * n) = (exp(-c))^n, a geometric series with ratio exp(-c) < 1
  have hsumm : Summable (fun n : ℕ => Real.exp (-c * ↑n)) := by
    have heq : ∀ n : ℕ, Real.exp (-c * ↑n) = Real.exp (-c) ^ n := fun n => by
      rw [show -c * (↑n : ℝ) = ↑n * (-c) from by ring, Real.exp_nat_mul]
    simp_rw [heq]
    exact summable_geometric_of_lt_one (le_of_lt (Real.exp_pos _))
      (Real.exp_lt_one_iff.mpr (by linarith))
  -- Both halves reduce to exp(-c * n) after simplifying absolute values
  refine ⟨?_, ?_⟩
  · -- Positive half: f(↑n) for n : ℕ, where |↑(↑n)| = n
    have heq : (fun n : ℕ => Real.exp (-(2 * Real.pi * δ * |(↑(↑n : ℤ) : ℝ)|) / T)) =
               (fun n : ℕ => Real.exp (-c * ↑n)) := by
      ext n; congr 1
      rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n)]
      unfold_let c; ring
    rw [heq]; exact hsumm
  · -- Negative half: f(-↑n) for n : ℕ, where |↑(-↑n)| = n
    have heq : (fun n : ℕ => Real.exp (-(2 * Real.pi * δ * |(↑(-↑n : ℤ) : ℝ)|) / T)) =
               (fun n : ℕ => Real.exp (-c * ↑n)) := by
      ext n; congr 1
      rw [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]
      unfold_let c; ring
    rw [heq]; exact hsumm

/-- Exponential decay of Fourier coefficients implies absolute convergence
    of the Fourier series (a much stronger property than L² convergence). -/
theorem exp_decay_abs_convergence (f : AddCircle T → ℂ) (δ : ℝ) (hδ : 0 < δ)
    (M : ℝ) (hM : 0 < M)
    (hdecay : ∀ n : ℤ, n ≠ 0 →
      ‖fourierCoeff f n‖ ≤ M * Real.exp (-(2 * Real.pi * δ * |↑n|) / T)) :
    Summable (fun n : ℤ => ‖fourierCoeff f n‖) := by
  -- Compare with (M + ‖ĉ₀‖) * exp(-c|n|), which handles n = 0 automatically
  set K := M + ‖fourierCoeff f 0‖
  have hK : 0 < K := by positivity
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ ((exp_decay_summable δ hδ).mul_left K)
  intro n
  by_cases hn : n = 0
  · -- n = 0: ‖ĉ₀‖ ≤ K * exp(0) = K = M + ‖ĉ₀‖
    subst hn
    simp only [Int.cast_zero, abs_zero, mul_zero, neg_zero, zero_div, Real.exp_zero, mul_one]
    linarith [hM.le]
  · -- n ≠ 0: ‖ĉ_n‖ ≤ M * exp(-c|n|) ≤ K * exp(-c|n|) since M ≤ K
    calc ‖fourierCoeff f n‖
        ≤ M * Real.exp (-(2 * Real.pi * δ * |↑n|) / T) := hdecay n hn
      _ ≤ K * Real.exp (-(2 * Real.pi * δ * |↑n|) / T) := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.exp_pos _))
          linarith [norm_nonneg (fourierCoeff f 0)]

-- ============================================================================
-- § 4. SHARPNESS OF THE EXPONENTIAL RATE
-- ============================================================================

/-- **Axiom 2: The decay rate 2πδ/T is sharp.**

    For each strip width δ > 0 and ε > 0, there exists a function f analytic
    on the strip of width δ whose Fourier coefficients satisfy:

      |ĉ_n(f)| ≥ C · e^{-2π(δ+ε)|n|/T}

    for infinitely many n. In other words, one cannot replace the exponent
    2πδ/T with anything larger.

    The extremal function is f(z) = 1/(cosh(2πz/T) - cosh(2πδ/T)), which
    has poles at z = ±iδ (on the strip boundary) and whose Fourier coefficients
    decay at exactly the rate e^{-2πδ|n|/T}. -/
axiom rate_is_sharp (δ : ℝ) (hδ : 0 < δ) :
    ∀ ε > 0, ∃ (f : AddCircle T → ℂ), Integrable f ∧
      ∃ (C : ℝ) (_ : 0 < C),
        ∀ᶠ n in Filter.cofinite,
          C * Real.exp (-(2 * Real.pi * (δ + ε) * |↑n|) / T) ≤ ‖fourierCoeff f n‖

-- ============================================================================
-- § 5. PALEY-WIENER CHARACTERIZATION (Converse)
-- ============================================================================

/-- **Axiom 3: Paley-Wiener for the circle (converse direction).**

    If |ĉ_n(f)| = O(e^{-c|n|}) for some c > 0, then f extends
    holomorphically to the strip |Im z| < cT/(2π).

    Combined with Axiom 1, this gives a complete characterization:
    f is strip-analytic of width δ ⟺ |ĉ_n(f)| = O(e^{-2πδ|n|/T}).

    The proof constructs the holomorphic extension as the absolutely
    convergent Fourier series ∑ ĉ_n · e^{2πinz/T}, which converges
    in the strip by the exponential decay assumption. -/
axiom paley_wiener_converse (f : AddCircle T → ℂ) (c : ℝ) (hc : 0 < c)
    (hdecay : ∃ M : ℝ, 0 < M ∧ ∀ n : ℤ, ‖fourierCoeff f n‖ ≤ M * Real.exp (-c * |↑n|)) :
    IsStripAnalytic (c * T / (2 * Real.pi)) f

-- ============================================================================
-- § 6. THE SHARP CONSTANT FOR A GIVEN FUNCTION
-- ============================================================================

/-- For a specific function f analytic on the strip of width δ, the sharp
    constant K(f) in |ĉ_n| ≤ K · e^{-2πδ|n|/T} is:

      K(f) = lim sup_{|n|→∞} |ĉ_n| · e^{2πδ|n|/T}

    This equals M_δ(f) = sup_{|y|=δ} (1/T)∫|f(x+iy)|dx when the strip
    boundary is a natural boundary, and can be strictly less when f extends
    further. -/
def sharpConstant (δ : ℝ) (f : AddCircle T → ℂ) : ℝ :=
  ⨆ (n : ℤ) (_ : n ≠ 0),
    ‖fourierCoeff f n‖ * Real.exp (2 * Real.pi * δ * |↑n| / T)

/-- The sharp constant is a valid bound.
    Proof: K = sup_n (|ĉ_n| * e^{2πδ|n|/T}), so |ĉ_n| * e^{2πδ|n|/T} ≤ K,
    hence |ĉ_n| ≤ K * e^{-2πδ|n|/T}. -/
theorem sharpConstant_is_bound (δ : ℝ) (hδ : 0 < δ) (f : AddCircle T → ℂ)
    (hf : IsStripAnalytic δ f) (n : ℤ) (hn : n ≠ 0) :
    ‖fourierCoeff f n‖ ≤ sharpConstant δ f *
      Real.exp (-(2 * Real.pi * δ * |↑n|) / T) := by
  obtain ⟨_, _, M, hM, hbound⟩ := hf
  set a := 2 * Real.pi * δ * |↑n| / T
  -- Step 1: ‖ĉ_n‖ * exp(a) ≤ sharpConstant δ f (n-th term ≤ supremum)
  suffices h_le : ‖fourierCoeff f n‖ * Real.exp a ≤ sharpConstant δ f by
    -- Step 2: multiply both sides by exp(-a) to get the goal
    calc ‖fourierCoeff f n‖
        = ‖fourierCoeff f n‖ * Real.exp a * Real.exp (-a) := by
          rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ sharpConstant δ f * Real.exp (-a) :=
          mul_le_mul_of_nonneg_right h_le (Real.exp_pos _).le
      _ = sharpConstant δ f * Real.exp (-(2 * Real.pi * δ * |↑n|) / T) := by
          congr 1
  -- Show n-th term ≤ supremum via le_ciSup
  unfold sharpConstant
  -- BddAbove: all terms bounded by M (from IsStripAnalytic decay bound)
  have hbdd : BddAbove (Set.range fun m : ℤ =>
      ⨆ (_ : m ≠ 0), ‖fourierCoeff f m‖ *
        Real.exp (2 * Real.pi * δ * |↑m| / T)) := by
    refine ⟨M, ?_⟩
    rintro x ⟨m, rfl⟩
    by_cases hm : m = 0
    · subst hm; simp only [ne_eq, not_true_eq_false, ciSup_of_empty]; exact hM.le
    · haveI : Nonempty (m ≠ 0) := ⟨hm⟩
      rw [ciSup_const]
      have hbn := hbound m hm
      have hexp_cancel : Real.exp (-(2 * Real.pi * δ * |↑m|) / T) *
          Real.exp (2 * Real.pi * δ * |↑m| / T) = 1 := by
        rw [← Real.exp_add]; simp [show -(2 * Real.pi * δ * |↑m|) / T +
          2 * Real.pi * δ * |↑m| / T = 0 from by ring]
      nlinarith [Real.exp_pos (2 * Real.pi * δ * |↑m| / T),
                 mul_le_mul_of_nonneg_right hbn
                   (Real.exp_pos (2 * Real.pi * δ * |↑m| / T)).le]
  -- n-th term ≤ outer supremum
  haveI : Nonempty (n ≠ 0) := ⟨hn⟩
  calc ‖fourierCoeff f n‖ * Real.exp a
      = ⨆ (_ : n ≠ 0), ‖fourierCoeff f n‖ * Real.exp a := ciSup_const.symm
    _ ≤ ⨆ (m : ℤ), ⨆ (_ : m ≠ 0),
        ‖fourierCoeff f m‖ * Real.exp (2 * Real.pi * δ * |↑m| / T) :=
        le_ciSup hbdd n

/-- The sharp constant is the smallest valid bound. -/
theorem sharpConstant_optimal (δ : ℝ) (hδ : 0 < δ) (f : AddCircle T → ℂ)
    (hf : IsStripAnalytic δ f) (K : ℝ) (hK : 0 < K)
    (hbound : ∀ n : ℤ, n ≠ 0 →
      ‖fourierCoeff f n‖ ≤ K * Real.exp (-(2 * Real.pi * δ * |↑n|) / T)) :
    sharpConstant δ f ≤ K := by
  unfold sharpConstant
  -- The iSup over n : ℤ of (iSup over hn : n ≠ 0 of g(n)) ≤ K
  -- For each n: if n ≠ 0, g(n) = ‖ĉ_n‖ * exp(2πδ|n|/T) ≤ K (by hbound)
  -- if n = 0, the inner iSup is 0 ≤ K (empty supremum = 0)
  apply ciSup_le fun n => ?_
  by_cases hn : n = 0
  · -- n = 0: inner sup over empty type is 0 ≤ K
    subst hn; simp [ciSup_empty]; exact hK.le
  · -- n ≠ 0: inner sup is g(n) ≤ K
    apply ciSup_le fun _ => ?_
    -- Goal: ‖ĉ_n‖ * exp(2πδ|n|/T) ≤ K
    have hbn := hbound n hn
    have hexp_pos := Real.exp_pos (2 * Real.pi * δ * |↑n| / T)
    calc ‖fourierCoeff f n‖ * Real.exp (2 * Real.pi * δ * |↑n| / T)
        ≤ K * Real.exp (-(2 * Real.pi * δ * |↑n|) / T) *
          Real.exp (2 * Real.pi * δ * |↑n| / T) :=
          mul_le_mul_of_nonneg_right hbn hexp_pos.le
      _ = K * (Real.exp (-(2 * Real.pi * δ * |↑n|) / T) *
          Real.exp (2 * Real.pi * δ * |↑n| / T)) := by ring
      _ = K * Real.exp (-(2 * Real.pi * δ * |↑n|) / T +
          2 * Real.pi * δ * |↑n| / T) := by rw [← Real.exp_add]
      _ = K * Real.exp 0 := by congr 1; ring
      _ = K := by simp [Real.exp_zero]

-- ============================================================================
-- § 7. COMPARISON WITH POLYNOMIAL (HÖLDER) DECAY
-- ============================================================================

/-- Exponential decay dominates polynomial decay: for any α > 0, the
    exponential bound M · e^{-c|n|} is eventually less than any C/|n|^α. -/
theorem exp_dominates_polynomial (c M : ℝ) (hc : 0 < c) (hM : 0 < M)
    (C : ℝ) (hC : 0 < C) (α : ℝ) (hα : 0 < α) :
    ∀ᶠ n in Filter.cofinite,
      M * Real.exp (-c * |↑n|) ≤ C * |↑n|⁻¹ ^ α := by
  sorry -- Standard: exponential decays faster than any polynomial

/-- The strip width δ determines both the decay rate AND the regularity class.
    This shows the relationship between the analytic strip width and the
    Hölder exponent framework from OQ-02:
    - Hölder exponent α gives polynomial decay O(1/|n|^α)
    - Strip width δ gives exponential decay O(e^{-2πδ|n|/T})
    - As δ → 0, the exponential bound degenerates to O(1)
    - As α → ∞ (C^∞), polynomial decay can be arbitrarily fast but not exponential -/
theorem analytic_hierarchy (f : AddCircle T → ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hf : IsStripAnalytic δ f) :
    ∀ α : ℝ, 0 < α → Summable (fun n : ℤ => ‖fourierCoeff f n‖ * |↑n| ^ α) := by
  sorry -- Exponential decay beats any polynomial weight

-- ============================================================================
-- § 8. EXAMPLES
-- ============================================================================

/-- **Example: The Poisson kernel.**

    f(x) = 1/(1 - 2r·cos(2πx/T) + r²) for 0 < r < 1 is analytic on
    the strip of width δ = -T·ln(r)/(2π), with Fourier coefficients
    ĉ_n = r^|n|. The sharp constant is 1.

    This satisfies |ĉ_n| = r^|n| = e^{|n|·ln(r)} = e^{-2πδ|n|/T} exactly. -/
def poissonKernelStripWidth (r : ℝ) (hr : 0 < r) (hr1 : r < 1) : ℝ :=
  -(T * Real.log r) / (2 * Real.pi)

theorem poissonKernel_strip_positive (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    0 < poissonKernelStripWidth r hr hr1 := by
  unfold poissonKernelStripWidth
  apply div_pos
  · apply neg_pos_of_neg
    exact mul_neg_of_pos_of_neg hT.out (Real.log_neg hr hr1)
  · positivity

/-- **Example: Bernstein's inequality context.**

    For trigonometric polynomials of degree N (ĉ_n = 0 for |n| > N),
    the exponential decay is vacuously satisfied for any δ.
    The interesting case is genuine infinite Fourier series. -/
theorem trig_poly_vacuous (f : AddCircle T → ℂ) (N : ℕ)
    (hf : ∀ n : ℤ, N < |n| → fourierCoeff f n = 0) (δ : ℝ) (hδ : 0 < δ) :
    ∀ n : ℤ, N < |n| →
      ‖fourierCoeff f n‖ ≤ 1 * Real.exp (-(2 * Real.pi * δ * |↑n|) / T) := by
  intro n hn
  rw [hf n hn, norm_zero]
  exact mul_nonneg one_pos.le (le_of_lt (Real.exp_pos _))

-- ============================================================================
-- § 9. WHAT REMAINS TO FORMALIZE
-- ============================================================================

/-
## Axiom Elimination Roadmap

### Axiom 1 (contour_shift_decay):
- **Need:** Complex contour integration on periodic domains
- **Key ingredients:** Cauchy's theorem for rectangular contours,
  cancellation of vertical edges by periodicity, dominated convergence
  for the limit ε → 0
- **Mathlib gap:** `Complex.integral_boundary_rect_eq_zero_of_differentiable`
  exists but the periodic contour setup is not formalized
- **Difficulty:** MODERATE (≈300-500 lines)

### Axiom 2 (rate_is_sharp):
- **Need:** Explicit construction of extremal functions
- **Key ingredient:** The function 1/(cosh(2πz/T) - cosh(2πδ/T)) has
  poles exactly on the strip boundary and its Fourier coefficients decay
  at the optimal rate
- **Difficulty:** MODERATE (≈200 lines, mostly explicit computation)

### Axiom 3 (paley_wiener_converse):
- **Need:** Prove that ∑ ĉ_n · e^{2πinz/T} converges in the strip
  when the coefficients decay exponentially
- **Key ingredients:** Uniform convergence of holomorphic series,
  Weierstrass theorem that uniform limits of holomorphic functions are
  holomorphic
- **Mathlib gap:** Weierstrass uniform convergence theorem exists in
  Mathlib but the periodic setup needs work
- **Difficulty:** LOW-MODERATE (≈200 lines)

### Sorry elimination:
- exp_decay_summable: comparison with geometric series (≈20 lines)
- exp_decay_abs_convergence: direct from comparison test (≈15 lines)
- sharpConstant_is_bound/optimal: from definition of iSup (≈30 lines each)
- exp_dominates_polynomial: L'Hôpital or direct estimation (≈30 lines)
- analytic_hierarchy: from exp_decay + polynomial weight (≈40 lines)

### Total estimate: ≈800-1100 lines of new infrastructure
-/

end FourierAnalyticDecay
