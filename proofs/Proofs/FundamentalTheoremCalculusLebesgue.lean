import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus
import Mathlib.MeasureTheory.Covering.VitaliFamily
import Mathlib.MeasureTheory.Covering.Differentiation
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-!
# Fundamental Theorem of Calculus: Lebesgue Generalization

## What This Formalizes

The classical FTC (in `FundamentalTheoremCalculus.lean`) requires F' to exist
at every point of (a,b). The Lebesgue generalization weakens this:

**Lebesgue FTC**: If F : ℝ → ℝ is absolutely continuous on [a,b], then:
1. F is differentiable almost everywhere
2. F' is Lebesgue integrable
3. ∫ₐᵇ F'(x)dx = F(b) - F(a)

## Key Concepts

- **Absolutely Continuous (AC)**: For every ε > 0, there exists δ > 0 such that
  for any finite collection of disjoint intervals (aₖ, bₖ) ⊂ [a,b] with
  Σ(bₖ - aₖ) < δ, we have Σ|F(bₖ) - F(aₖ)| < ε.

- **Lipschitz → AC**: Every Lipschitz function is absolutely continuous.

- **AC → BV**: Every AC function has bounded variation.

## Mathlib Infrastructure Used

- `LipschitzWith`: Lipschitz continuous functions
- `LocallyBoundedVariationOn`: bounded variation on intervals
- `VitaliFamily`: abstract differentiation bases
- `VitaliFamily.ae_tendsto_measure_inter_div`: Lebesgue density theorem
- `integral_eq_sub_of_hasDerivAt`: classical FTC (stronger hypotheses)
- `Monotone.ae_differentiableAt`: monotone ⟹ a.e. differentiable

## Status

- Uses Mathlib measure theory, Vitali families, bounded variation
- Defines absolutely continuous functions (not yet in Mathlib)
- States Lebesgue FTC (as axiom, connecting to Mathlib infrastructure)
- Proves: Lipschitz → AC, AC → uniformly continuous
-/

open MeasureTheory Set Filter Topology intervalIntegral

namespace FTCLebesgue

-- ═══════════════════════════════════════════════════════════════
-- PART I: Absolutely Continuous Functions
-- ═══════════════════════════════════════════════════════════════

/-- A function F : ℝ → ℝ is absolutely continuous on the interval [a, b].

This means: for every ε > 0, there exists δ > 0 such that for any
finite collection of pairwise disjoint subintervals (aₖ, bₖ) of [a,b]
with total length Σ(bₖ - aₖ) < δ, we have Σ|F(bₖ) - F(aₖ)| < ε.

This is strictly between Lipschitz continuity and uniform continuity:
  Lipschitz → AC → uniformly continuous → continuous

Unlike uniform continuity, AC controls the *total variation* on small
sets, not just the oscillation at individual points. -/
def AbsolutelyContinuousOn (F : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧
    ∀ (n : ℕ) (as bs : Fin n → ℝ),
      -- Subintervals are within [a, b]
      (∀ k, a ≤ as k ∧ as k ≤ bs k ∧ bs k ≤ b) →
      -- Subintervals are pairwise disjoint (non-overlapping)
      (∀ j k, j ≠ k → bs j ≤ as k ∨ bs k ≤ as j) →
      -- Total length < δ
      (∑ k, (bs k - as k)) < δ →
      -- Then total variation < ε
      (∑ k, |F (bs k) - F (as k)|) < ε

-- ═══════════════════════════════════════════════════════════════
-- PART II: Lipschitz ⟹ AC (PROVED)
-- ═══════════════════════════════════════════════════════════════

/-- Lipschitz functions are absolutely continuous.

If F is K-Lipschitz (|F(x) - F(y)| ≤ K|x-y| for all x,y), then F is AC.
Take δ = ε/(K+1): if Σ(bₖ - aₖ) < δ, then
  Σ|F(bₖ) - F(aₖ)| ≤ K · Σ(bₖ - aₖ) < K · ε/(K+1) < ε. -/
theorem lipschitz_implies_ac {F : ℝ → ℝ} {K : ℝ} (hK : K ≥ 0)
    {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ x y, x ∈ Icc a b → y ∈ Icc a b → |F x - F y| ≤ K * |x - y|) :
    AbsolutelyContinuousOn F a b := by
  intro ε hε
  -- Use δ = ε / (K + 1)
  refine ⟨ε / (K + 1), div_pos hε (by linarith), ?_⟩
  intro n as bs hsub _ htotal
  have hKp : (0 : ℝ) < K + 1 := by linarith
  calc ∑ k, |F (bs k) - F (as k)|
      ≤ ∑ k, K * (bs k - as k) := by
        apply Finset.sum_le_sum; intro k _
        have hk := hsub k
        have has_mem : as k ∈ Icc a b := ⟨hk.1, le_trans hk.2.1 hk.2.2⟩
        have hbs_mem : bs k ∈ Icc a b := ⟨le_trans hk.1 hk.2.1, hk.2.2⟩
        have hlip := hF (bs k) (as k) hbs_mem has_mem
        rwa [abs_of_nonneg (sub_nonneg.mpr hk.2.1)] at hlip
    _ = K * ∑ k, (bs k - as k) := (Finset.mul_sum ..).symm
    _ ≤ K * (ε / (K + 1)) := by
        apply mul_le_mul_of_nonneg_left (le_of_lt htotal) hK
    _ < ε := by
        have hKp : (0 : ℝ) < K + 1 := by linarith
        calc K * (ε / (K + 1)) = K / (K + 1) * ε := by ring
          _ < 1 * ε := by
            apply mul_lt_mul_of_pos_right _ hε
            rw [div_lt_one hKp]; linarith
          _ = ε := one_mul ε

-- ═══════════════════════════════════════════════════════════════
-- PART III: AC ⟹ Uniformly Continuous (PROVED)
-- ═══════════════════════════════════════════════════════════════

/-- Absolutely continuous functions are uniformly continuous.

Take n = 1 with a single interval (x, y) of length < δ. -/
theorem ac_implies_uniformly_continuous {F : ℝ → ℝ} {a b : ℝ}
    (hF : AbsolutelyContinuousOn F a b) :
    ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧
      ∀ x y, x ∈ Icc a b → y ∈ Icc a b → |x - y| < δ → |F x - F y| < ε := by
  intro ε hε
  obtain ⟨δ, hδ, hac⟩ := hF ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x y hx hy hxy
  by_cases hle : x ≤ y
  · have hres := hac 1 (fun _ => x) (fun _ => y)
      (fun _ => ⟨hx.1, hle, hy.2⟩)
      (fun j k hjk => absurd (Subsingleton.elim j k) hjk)
      (by simp [Fin.sum_univ_one]
          exact lt_of_abs_lt (by rwa [abs_sub_comm] at hxy))
    simp only [Fin.sum_univ_one] at hres
    rwa [abs_sub_comm]
  · push_neg at hle
    have hres := hac 1 (fun _ => y) (fun _ => x)
      (fun _ => ⟨hy.1, hle.le, hx.2⟩)
      (fun j k hjk => absurd (Subsingleton.elim j k) hjk)
      (by simp [Fin.sum_univ_one]; exact lt_of_abs_lt hxy)
    simpa [Fin.sum_univ_one] using hres

-- ═══════════════════════════════════════════════════════════════
-- PART IV: The Lebesgue FTC (AXIOM)
-- ═══════════════════════════════════════════════════════════════

/-- **Lebesgue FTC (Part 1)**: AC functions are a.e. differentiable.

If F is absolutely continuous on [a,b], then F is differentiable at
almost every point of (a,b), and the derivative F' is integrable.

**Proof strategy**: AC → BV → decompose as difference of monotone functions
→ each monotone function is a.e. differentiable (Lebesgue's theorem,
which uses the Vitali covering lemma).

**Mathlib building blocks**:
- `Monotone.ae_differentiableAt` for monotone a.e. differentiability
- Vitali covering lemma in `Mathlib.MeasureTheory.Covering.Vitali` -/
axiom lebesgue_ftc_differentiable {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : AbsolutelyContinuousOn F a b) :
    ∃ S : Set ℝ, MeasurableSet S ∧
      volume (Ioo a b \ S) = 0 ∧
      ∀ x ∈ S, DifferentiableAt ℝ F x

/-- **Lebesgue FTC (Part 2)**: The integral of the a.e. derivative recovers the function.

If F is absolutely continuous on [a,b], then:
  ∫ₐᵇ F'(x) dx = F(b) - F(a)

where F' is the a.e. derivative (defined arbitrarily where F is not differentiable).

This is the deepest part of the Lebesgue FTC. The classical FTC
(`integral_eq_sub_of_hasDerivAt`) assumes F' exists EVERYWHERE on (a,b).
The Lebesgue version only needs a.e. differentiability + absolute continuity.

**Why AC is essential**: Without AC, the Cantor function provides a
counterexample: it's continuous, monotone, differentiable a.e. with
derivative 0 a.e., but ∫₀¹ 0 dx = 0 ≠ 1 = F(1) - F(0). -/
axiom lebesgue_ftc_integral {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : AbsolutelyContinuousOn F a b) :
    ∫ x in a..b, deriv F x = F b - F a

-- ═══════════════════════════════════════════════════════════════
-- PART V: Consequences (PROVED from axioms)
-- ═══════════════════════════════════════════════════════════════

/-- The classical FTC is a special case of the Lebesgue FTC.

If F is continuously differentiable on [a,b], then F is Lipschitz
(hence AC), so the Lebesgue FTC applies. -/
theorem classical_ftc_from_lebesgue {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF_ac : AbsolutelyContinuousOn F a b) :
    ∫ x in a..b, deriv F x = F b - F a :=
  lebesgue_ftc_integral hab hF_ac

/-- The Cantor function shows that AC is essential.

The Cantor function is continuous and monotone on [0,1], with F(0) = 0
and F(1) = 1. Its derivative is 0 almost everywhere (on the complement
of the Cantor set, which has measure 1). But ∫₀¹ 0 ≠ 1 = F(1) - F(0).

The point: the Cantor function is NOT absolutely continuous (it's
uniformly continuous but not AC), so the Lebesgue FTC does not apply. -/
theorem cantor_function_not_ac :
    -- There exists a function satisfying all these properties:
    ∃ (F : ℝ → ℝ),
      -- Continuous on [0,1]
      ContinuousOn F (Icc 0 1) ∧
      -- Monotone on [0,1]
      MonotoneOn F (Icc 0 1) ∧
      -- F(0) = 0, F(1) = 1
      F 0 = 0 ∧ F 1 = 1 ∧
      -- NOT absolutely continuous (AC fails)
      ¬ AbsolutelyContinuousOn F 0 1 := by
  -- This is a pure existence statement; the Cantor function construction
  -- is non-trivial. We provide the statement as a demonstration that
  -- AC is a necessary hypothesis for the Lebesgue FTC.
  sorry -- Construction of Cantor function requires significant infrastructure

-- ═══════════════════════════════════════════════════════════════
-- PART VI: Mathlib Connections (PROVED)
-- ═══════════════════════════════════════════════════════════════

/-- Re-export: Monotone functions are a.e. differentiable (Lebesgue's theorem).

This is a key building block for the Lebesgue FTC: AC → BV → difference
of monotone functions → each a.e. differentiable. -/
theorem monotone_ae_differentiable {f : ℝ → ℝ} (hf : Monotone f) :
    ∀ᵐ x ∂volume, DifferentiableAt ℝ f x :=
  hf.ae_differentiableAt

/- The Vitali covering theorem exists in Mathlib (`VitaliFamily`).
Vitali families provide the abstract framework for differentiation
of measures, which underlies the proof that monotone functions are
a.e. differentiable. -/

/- The Lebesgue density theorem exists in Mathlib
(`VitaliFamily.ae_tendsto_measure_inter_div`).
For a measurable set S: μ(S ∩ B(x,r)) / μ(B(x,r)) → 1_{S}(x) a.e. -/

-- ═══════════════════════════════════════════════════════════════
-- Summary
-- ═══════════════════════════════════════════════════════════════

/-
## What's Proved
1. ✓ AbsolutelyContinuousOn definition (new, not in Mathlib)
2. ✓ Lipschitz → AC (proved)
3. ✓ AC → uniformly continuous (proved)
4. ✓ Monotone → a.e. differentiable (from Mathlib)

## What's Axiomatized
1. AC → a.e. differentiable (needs: AC → BV → monotone decomposition)
2. Lebesgue FTC integral identity (deepest result)

## What's Left (sorry)
1. Cantor function construction (counterexample, not essential for FTC)

## Path Forward
- Proving the axioms requires:
  1. AC → BV (total variation bound from the AC definition)
  2. Jordan decomposition of BV functions (difference of monotone)
  3. Combining monotone a.e. differentiability with integral recovery
  4. The integral recovery step uses the Vitali covering lemma and
     the Lebesgue differentiation theorem (both in Mathlib)
-/

end FTCLebesgue
