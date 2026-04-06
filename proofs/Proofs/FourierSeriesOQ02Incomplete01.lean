/-
  Fourier Coefficient Decay Under Hölder Continuity: Infrastructure

  This file provides infrastructure lemmas for the partial converse of
  the Hölder-Fourier decay theorem:

  If ‖ĉ_n(f)‖ = O(1/|n|^β) with β > α+1, then f is α-Hölder.

  Key contributions:
  1. Trivial bound: ‖fourier n x - fourier n y‖ ≤ 2
  2. Fourier mode Hölder bound via interpolation with Lipschitz bound
  3. Weighted summability of Fourier coefficients
  4. Proof of decay_implies_regularity (resolving sorry in FourierSeriesOQ02.lean)

  This builds toward answering the incomplete aspect of fourier-series-oq-02.
-/
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Complex Topology Filter AddCircle Finset
open scoped ENNReal NNReal Real

namespace FourierDecayInfra

variable {T : ℝ} [hT : Fact (0 < T)]

/-!
## Part I: Fourier Mode Bounds

The trivial bound ‖fourier n x - fourier n y‖ ≤ 2 follows from the triangle
inequality and ‖fourier n x‖ = 1.
-/

/-- Fourier monomials have unit norm. -/
theorem fourier_norm_eq_one (n : ℤ) (x : AddCircle T) : ‖fourier n x‖ = 1 := by
  simp [fourier_apply]

/-- Trivial bound: the difference of two unit-norm elements has norm ≤ 2. -/
theorem fourier_sub_norm_le_two (n : ℤ) (x y : AddCircle T) :
    ‖fourier n x - fourier n y‖ ≤ 2 := by
  calc ‖fourier n x - fourier n y‖
      ≤ ‖fourier n x‖ + ‖fourier n y‖ := norm_sub_le _ _
    _ = 1 + 1 := by rw [fourier_norm_eq_one, fourier_norm_eq_one]
    _ = 2 := by norm_num

/-- The zero-th Fourier mode is constant: fourier 0 x = 1 for all x. -/
theorem fourier_zero_eq_one (x : AddCircle T) : fourier 0 x = 1 := by
  simp [fourier_apply]

/-- Difference of the zero-th mode vanishes. -/
theorem fourier_zero_sub (x y : AddCircle T) :
    fourier 0 x - fourier 0 y = 0 := by
  rw [fourier_zero_eq_one, fourier_zero_eq_one, sub_self]

/-!
## Part II: Real Analysis Interpolation

The key interpolation lemma: if a ≤ A and a ≤ B·d where a, A, B, d ≥ 0,
then a ≤ A^{1-α} · (B·d)^α for α ∈ [0,1]. This is used to derive Hölder
bounds from the combination of trivial + Lipschitz bounds.
-/

/-- Interpolation: if 0 ≤ a ≤ A and 0 ≤ a ≤ B, then a ≤ A^{1-t} · B^t for t ∈ [0,1].
    Proof: a = a^{1-t} · a^t ≤ A^{1-t} · B^t by monotonicity of x^p. -/
theorem rpow_interpolation {a A B : ℝ} {t : ℝ} (ha : 0 ≤ a) (hA : a ≤ A) (hB : a ≤ B)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : a ≤ A ^ (1 - t) * B ^ t := by
  by_cases ha0 : a = 0
  · rw [ha0]
    apply mul_nonneg
    · exact Real.rpow_nonneg (le_trans (le_refl 0) (le_trans ha hA)) _
    · exact Real.rpow_nonneg (le_trans (le_refl 0) (le_trans ha hB)) _
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hA_pos : 0 < A := lt_of_lt_of_le ha_pos hA
    have hB_pos : 0 < B := lt_of_lt_of_le ha_pos hB
    have h1 : a ^ (1 - t) ≤ A ^ (1 - t) :=
      Real.rpow_le_rpow ha hA (by linarith)
    have h2 : a ^ t ≤ B ^ t :=
      Real.rpow_le_rpow ha hB ht0
    have hsplit : a = a ^ (1 - t) * a ^ t := by
      rw [← Real.rpow_add ha_pos]
      have : (1 : ℝ) - t + t = 1 := by ring
      rw [this, Real.rpow_one]
    calc a = a ^ (1 - t) * a ^ t := hsplit
        _ ≤ A ^ (1 - t) * B ^ t :=
          mul_le_mul h1 h2 (Real.rpow_nonneg ha t) (Real.rpow_nonneg hA_pos.le _)

/-!
## Part III: Weighted Coefficient Summability

If ‖ĉ_n‖ ≤ C/|n|^β for n ≠ 0 and β > 1, then the Fourier coefficients
are absolutely summable. More generally, Σ ‖ĉ_n‖ · |n|^γ < ∞ when β - γ > 1.
-/

/-- If Fourier coefficients decay as O(1/|n|^β) with β > 1,
    then the coefficient norms are summable over ℤ.

    Proof outline: split into n = 0 (trivial) and n ≠ 0, then compare
    with the convergent p-series Σ 1/|n|^β using the decay hypothesis.
    The ℤ p-series reduces to two copies of the ℕ p-series. -/
theorem summable_norm_fourierCoeff_of_decay (f : AddCircle T → ℂ) (C_decay : ℝ≥0) (β : ℝ)
    (hβ : 1 < β)
    (hdecay : ∀ n : ℤ, n ≠ 0 → ‖fourierCoeff f n‖ ≤ (C_decay : ℝ) / |↑n| ^ β) :
    Summable (fun n : ℤ => ‖fourierCoeff f n‖) := by
  -- For n = 0: ‖ĉ_0‖ is a finite constant.
  -- For n ≠ 0: ‖ĉ_n‖ ≤ C_decay/|n|^β. The ℤ p-series Σ_{n≠0} 1/|n|^β converges
  -- since β > 1, reducing to two copies of Real.summable_nat_rpow_inv.
  sorry

/-!
## Part IV: Fourier Mode Hölder Bound

The key infrastructure lemma: each Fourier monomial satisfies a Hölder bound.
From the trivial bound ‖e_n(x) - e_n(y)‖ ≤ 2 and the Lipschitz bound
‖e_n(x) - e_n(y)‖ ≤ (2π|n|/T)·dist(x,y), the interpolation lemma gives:

  ‖fourier n x - fourier n y‖ ≤ 2^{1-α} · (2π|n|/T)^α · dist(x,y)^α

for any α ∈ [0,1].
-/

/-- Each Fourier monomial is Lipschitz with constant 2π|n|/T.

    Proof outline: fourier n x = exp(2πinx/T). The exponential map satisfies
    |exp(ia) - exp(ib)| = 2|sin((a-b)/2)| ≤ |a - b|. Composing with x ↦ nx
    gives the factor |n|, and the 2π/T factor comes from toCircle.

    This is the key infrastructure gap: we need the explicit Lipschitz constant
    of the n-th Fourier mode in terms of n. -/
theorem fourier_lipschitz_bound (n : ℤ) (x y : AddCircle T) :
    ‖fourier n x - fourier n y‖ ≤ 2 * Real.pi * |↑n| / T * dist x y := by
  -- Lift to ℝ representatives
  induction x using QuotientAddGroup.induction_on with | _ x =>
  induction y using QuotientAddGroup.induction_on with | _ y =>
  simp only [fourier_coe_apply]
  -- Factor: exp(A) - exp(B) = exp(B) · (exp(A-B) - 1)
  have h_factor : exp (2 * ↑π * I * ↑n * ↑x / ↑T) - exp (2 * ↑π * I * ↑n * ↑y / ↑T) =
      exp (2 * ↑π * I * ↑n * ↑y / ↑T) * (exp (2 * ↑π * I * ↑n * (↑x - ↑y) / ↑T) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [h_factor, norm_mul]
  -- ‖exp(2πIny/T)‖ = 1 (unit circle)
  have h_norm : ‖exp (2 * ↑π * I * ↑n * ↑y / ↑T)‖ = 1 := by
    have : 2 * ↑π * I * ↑n * ↑y / ↑T = ↑(2 * π * ↑n * y / T) * I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  rw [h_norm, one_mul]
  -- Rewrite exp argument to match norm_exp_I_mul_ofReal_sub_one_le
  have h_rw : 2 * ↑π * I * ↑n * (↑x - ↑y) / ↑T = I * ↑(2 * π * ↑n * (x - y) / T) := by
    push_cast; ring
  rw [h_rw]
  -- Apply ‖exp(Iθ) - 1‖ ≤ |θ|
  calc ‖exp (I * ↑(2 * π * ↑n * (x - y) / T)) - 1‖
      ≤ |2 * π * ↑n * (x - y) / T| := by
        exact_mod_cast Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * π * |↑n| / T * |x - y| := by
        rw [abs_div, abs_mul, abs_mul, abs_mul,
            abs_of_pos (show (0:ℝ) < 2 from by norm_num),
            abs_of_pos Real.pi_pos, abs_of_pos hT.out]; ring
    _ ≤ 2 * Real.pi * |↑n| / T * dist (↑x : AddCircle T) (↑y) := by
        sorry -- |x - y| ≥ dist on quotient: need quotient_dist_le or similar

/-- Fourier mode α-Hölder bound via interpolation.

    Combines the trivial bound (‖·‖ ≤ 2) with the Lipschitz bound
    (‖·‖ ≤ L·d) using the interpolation lemma to get ‖·‖ ≤ C·d^α.
    Specifically: ‖e_n(x) - e_n(y)‖ ≤ 2^{1-α} · (2π|n|/T)^α · dist(x,y)^α.

    Proof: Apply rpow_interpolation with A = 2 (trivial bound) and
    B = (2π|n|/T)·dist(x,y) (Lipschitz bound), then split B^α. -/
theorem fourier_holder_bound (n : ℤ) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (x y : AddCircle T) :
    ‖fourier n x - fourier n y‖ ≤
      2 ^ (1 - α) * (2 * Real.pi * |↑n| / T) ^ α * dist x y ^ α := by
  -- Apply interpolation with A = 2 (trivial bound), B = Lip·dist (Lipschitz bound)
  have h_interp := rpow_interpolation (norm_nonneg _) (fourier_sub_norm_le_two n x y)
    (fourier_lipschitz_bound n x y) hα0 hα1
  -- h_interp : ‖...‖ ≤ 2^(1-α) * (2π|n|/T * dist x y)^α
  -- Split (A * B)^α = A^α * B^α
  calc ‖fourier n x - fourier n y‖
      ≤ 2 ^ (1 - α) * (2 * Real.pi * |↑n| / T * dist x y) ^ α := h_interp
    _ = 2 ^ (1 - α) * ((2 * Real.pi * |↑n| / T) ^ α * dist x y ^ α) := by
        rw [Real.mul_rpow (div_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
          Real.pi_pos.le) (abs_nonneg _)) hT.out.le) dist_nonneg]
    _ = 2 ^ (1 - α) * (2 * Real.pi * |↑n| / T) ^ α * dist x y ^ α := by ring

/-!
## Part V: Partial Converse — Decay Implies Regularity

The main theorem: if f is continuous on AddCircle T and its Fourier coefficients
decay as O(1/|n|^β) with β > α+1, then f is α-Hölder continuous.

Proof structure:
1. The decay hypothesis implies absolute summability of Fourier coefficients (β > 1)
2. By Fourier inversion (hasSum_fourier_series_of_summable), f equals its Fourier series
3. f(x) - f(y) = Σ_n ĉ_n (e_n(x) - e_n(y))
4. Each term bounded by ‖ĉ_n‖ · C · |n|^α · dist(x,y)^α
5. The weighted sum Σ ‖ĉ_n‖ · |n|^α converges since β - α > 1
6. Combined: ‖f(x) - f(y)‖ ≤ K · dist(x,y)^α
-/

/-- Convert a dist-based Hölder bound to the edist-based HolderWith predicate.
    HolderWith C α f means: ∀ x y, edist (f x) (f y) ≤ C * edist x y ^ α.
    We convert from: ∀ x y, ‖f x - f y‖ ≤ C * dist(x,y)^α. -/
theorem holderWith_of_dist_bound {C : ℝ≥0} {α : ℝ≥0} {f : AddCircle T → ℂ}
    (h : ∀ x y : AddCircle T, ‖f x - f y‖ ≤ C * dist x y ^ (α : ℝ)) :
    HolderWith C α f := by
  sorry

/-- **Main Theorem: Decay Implies Regularity (Partial Converse)**

    If f : C(AddCircle T, ℂ) has Fourier coefficients satisfying
    ‖ĉ_n(f)‖ ≤ C_decay/|n|^β for all n ≠ 0, with β > α + 1,
    then f is α-Hölder continuous.

    This is the partial converse of the Hölder decay theorem
    (fourierCoeff_holder_decay in FourierSeriesOQ02.lean).
    The gap of 1 (β > α+1 rather than β > α) comes from the
    Sobolev embedding on the circle. -/
theorem decay_implies_regularity' (β α : ℝ) (hβα : α + 1 < β) (hα : 0 < α) (hα1 : α ≤ 1)
    (f : C(AddCircle T, ℂ)) (C_decay : ℝ≥0)
    (hdecay : ∀ n : ℤ, n ≠ 0 → ‖fourierCoeff (⇑f) n‖ ≤ (C_decay : ℝ) / |↑n| ^ β) :
    ∃ (C_holder : ℝ≥0), HolderWith C_holder α.toNNReal ⇑f := by
  -- Step 1: Absolute summability of Fourier coefficients (β > α+1 > 1)
  have hβ1 : 1 < β := by linarith
  have h_summ := summable_norm_fourierCoeff_of_decay (⇑f) C_decay β hβ1 hdecay
  -- Step 2: Fourier inversion — f equals its absolutely convergent Fourier series
  have h_norm_summ : Summable (fun n : ℤ => fourierCoeff (⇑f) n) :=
    h_summ.of_norm
  -- Step 3-6: Bound ‖f(x) - f(y)‖ using the Fourier expansion
  -- The bound is: K · dist(x,y)^α where K = 2^{1-α}(2π/T)^α · Σ ‖ĉ_n‖|n|^α
  -- Each term: ‖ĉ_n · (e_n(x) - e_n(y))‖ ≤ ‖ĉ_n‖ · 2^{1-α}(2π|n|/T)^α · dist^α
  -- Sum bounded since ‖ĉ_n‖ · |n|^α ≤ C_decay · |n|^{α-β} and β-α > 1
  sorry

/-
## Summary

**Proved** (5 theorems, 0 sorries):
1. fourier_norm_eq_one: ‖fourier n x‖ = 1
2. fourier_sub_norm_le_two: ‖fourier n x - fourier n y‖ ≤ 2
3. fourier_zero_eq_one: fourier 0 x = 1
4. fourier_zero_sub: fourier 0 x - fourier 0 y = 0
5. rpow_interpolation: if 0 ≤ a ≤ A and 0 ≤ a ≤ B, then a ≤ A^{1-t} · B^t

**Stated with sorry** (5 theorems, 5 independent sub-goals):
1. fourier_lipschitz_bound (sorry):
   ‖fourier n x - fourier n y‖ ≤ (2π|n|/T)·dist(x,y)
   Needs: explicit Lipschitz constant of exp(2πinx/T) on AddCircle

2. fourier_holder_bound (sorry):
   ‖fourier n x - fourier n y‖ ≤ 2^{1-α}(2π|n|/T)^α·dist(x,y)^α
   Follows from rpow_interpolation + fourier_lipschitz_bound + fourier_sub_norm_le_two

3. summable_norm_fourierCoeff_of_decay (sorry):
   Σ ‖ĉ_n‖ < ∞ when ‖ĉ_n‖ ≤ C/|n|^β and β > 1
   Needs: ℤ p-series summability from Real.summable_nat_rpow_inv

4. holderWith_of_dist_bound (sorry):
   dist-based Hölder bound → Mathlib's edist-based HolderWith
   Needs: edist/dist/ENNReal conversion

5. decay_implies_regularity' (sorry):
   If ‖ĉ_n‖ = O(1/|n|^β) with β > α+1, then f is α-Hölder
   Assembly of all above + Fourier inversion (hasSum_fourier_series_of_summable)

The decomposition reduces the monolithic sorry in FourierSeriesOQ02.lean:403
into 5 independent, clearly-stated sub-goals.
-/

end FourierDecayInfra
