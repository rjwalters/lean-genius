/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5e879a4b-c313-4d93-ada9-41f2dcf2407c

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem HasFejerGaps.hasFabryGaps {n : ℕ → ℕ} (h : HasFejerGaps n) : HasFabryGaps n
-/

/-
  Erdős Problem #517: Lacunary Entire Functions and Value Distribution

  **Problem**: Let f(z) = ∑_{k=1}^∞ aₖz^{nₖ} be an entire function with aₖ ≠ 0 for all k.
  If nₖ/k → ∞ (Fabry gap condition), does f assume every value infinitely often?

  **Status**: OPEN (the main Fabry gap conjecture)

  **Related Results**:
  - Fejér (1908): If ∑1/nₖ < ∞, then f assumes every value at least once
  - Biernacki (1928): If ∑1/nₖ < ∞, then f assumes every value infinitely often
  - Pólya (1929): If f has finite order and lim sup(nₖ₊₁ - nₖ) = ∞, then f assumes
    every value infinitely often

  The Fejér gap condition (∑1/nₖ < ∞) is stronger than the Fabry gap condition (nₖ/k → ∞),
  so Biernacki's theorem doesn't resolve the main conjecture.

  Reference: https://erdosproblems.com/517
  [Fe08] Fejér, Leopold, "Über die Wurzel vom kleinsten absoluten Betrage..."
  [Bi28] Biernacki, "Sur les équations algébriques contenant des paramètres arbitraires"
  [Po29] Pólya, "Untersuchungen über Lücken und Singularitäten von Potenzreihen"

  Source: Adapted from Google DeepMind Formal Conjectures project
-/

import Mathlib


open Set Filter Topology

namespace Erdos517

/-
## Gap Conditions for Lacunary Series

A power series f(z) = ∑ aₖz^{nₖ} is called lacunary if there are "gaps" in the exponents.
Different gap conditions lead to different value distribution properties.
-/

/-- A sequence of natural numbers n₀ < n₁ < ... has **Fabry gaps** if nₖ/k → ∞.
This is the weaker gap condition appearing in the main conjecture. -/
def HasFabryGaps (n : ℕ → ℕ) : Prop :=
  StrictMono n ∧ Tendsto (fun k => (n k : ℝ) / k) atTop atTop

/-- A sequence of natural numbers n₀ < n₁ < ... has **Fejér gaps** if ∑ 1/nₖ < ∞.
This is the stronger gap condition for which value distribution is known. -/
def HasFejerGaps (n : ℕ → ℕ) : Prop :=
  StrictMono n ∧ Summable (fun k => (n k : ℝ)⁻¹)

/-- Fejér gaps imply Fabry gaps. The converse is false.
Example: nₖ = k² has Fabry gaps (k²/k = k → ∞) but not Fejér gaps (∑1/k² = π²/6 converges,
but that's because we're looking at n = k², so ∑1/nₖ = ∑1/k² which does converge). -/
theorem HasFejerGaps.hasFabryGaps {n : ℕ → ℕ} (h : HasFejerGaps n) : HasFabryGaps n := by
  constructor
  · exact h.1
  · -- Fejér gaps imply Fabry gaps via a telescoping argument
    -- If ∑1/nₖ < ∞, then 1/nₖ → 0, so nₖ → ∞, and the sum of 1/nₖ over intervals
    -- provides the growth rate needed for nₖ/k → ∞
    -- Since $\sum (n k : ℝ)⁻¹$ converges, it follows that $n k$ grows faster than $k$.
    have h_growth : Filter.Tendsto (fun k => (n k : ℝ)⁻¹ * k) Filter.atTop (nhds 0) := by
      -- Since $\sum (n k : ℝ)⁻¹$ converges, it follows that $n k$ grows faster than $k$. Hence, $(n k : ℝ)⁻¹ * k$ tends to $0$.
      have h_lim : Filter.Tendsto (fun k => (∑ i ∈ Finset.range k, (n i : ℝ)⁻¹) - (∑ i ∈ Finset.range (k / 2), (n i : ℝ)⁻¹)) Filter.atTop (nhds 0) := by
        simpa using Filter.Tendsto.sub ( h.2.hasSum.tendsto_sum_nat ) ( h.2.hasSum.tendsto_sum_nat.comp ( Filter.tendsto_atTop_atTop.mpr fun x => ⟨ 2 * x, fun k hk => by linarith [ Nat.div_add_mod k 2, Nat.mod_lt k two_pos ] ⟩ ) );
      have h_bound : ∀ k ≥ 2, (∑ i ∈ Finset.Ico (k / 2) k, (n i : ℝ)⁻¹) ≥ (k / 2) * (n k : ℝ)⁻¹ := by
        intros k hk
        have h_bound : ∀ i ∈ Finset.Ico (k / 2) k, (n i : ℝ)⁻¹ ≥ (n k : ℝ)⁻¹ := by
          field_simp;
          exact fun i hi => one_div_le_one_div_of_le ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by linarith [ h.1 <| show i > 0 from Nat.pos_of_ne_zero <| by rintro rfl; norm_num at hi; linarith [ Nat.div_add_mod k 2, Nat.mod_lt k two_pos ] ] ) <| Nat.cast_le.mpr <| h.1.monotone <| by linarith [ Finset.mem_Ico.mp hi ] ;
        refine' le_trans _ ( Finset.sum_le_sum h_bound ) ; norm_num;
        exact mul_le_mul_of_nonneg_right ( by rw [ div_le_iff₀ ] <;> norm_cast ; linarith [ Nat.div_mul_le_self k 2, Nat.sub_add_cancel ( show k / 2 ≤ k from Nat.div_le_self _ _ ) ] ) ( by positivity );
      have h_lim_zero : Filter.Tendsto (fun k => (k / 2) * (n k : ℝ)⁻¹) Filter.atTop (nhds 0) := by
        refine' squeeze_zero_norm' _ h_lim;
        filter_upwards [ Filter.eventually_ge_atTop 2 ] with k hk using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; simpa only [ Finset.sum_Ico_eq_sub _ ( Nat.div_le_self _ _ ) ] using h_bound k hk;
      convert h_lim_zero.const_mul 2 using 2 <;> ring;
    have h_reciprocal : Filter.Tendsto (fun k => (n k : ℝ)⁻¹ * k) Filter.atTop (nhds 0) → Filter.Tendsto (fun k => (n k : ℝ) / k) Filter.atTop Filter.atTop := by
      intro h_reciprocal
      have h_reciprocal : Filter.Tendsto (fun k => (n k : ℝ)⁻¹ * k) Filter.atTop (nhds 0) → Filter.Tendsto (fun k => ((n k : ℝ)⁻¹ * k)⁻¹) Filter.atTop Filter.atTop := by
        intro h_reciprocal
        have h_reciprocal : Filter.Tendsto (fun k => ((n k : ℝ)⁻¹ * k)⁻¹) Filter.atTop Filter.atTop := by
          have h_pos : ∀ᶠ k in Filter.atTop, 0 < (n k : ℝ)⁻¹ * k := by
            filter_upwards [ Filter.eventually_gt_atTop 0, Filter.eventually_gt_atTop ( n 0 ) ] with k hk₁ hk₂ using mul_pos ( inv_pos.mpr ( Nat.cast_pos.mpr ( by linarith [ h.1 hk₁ ] ) ) ) ( Nat.cast_pos.mpr hk₁ )
          refine' Filter.Tendsto.inv_tendsto_nhdsGT_zero _;
          rw [ tendsto_nhdsWithin_iff ] ; aesop;
        convert h_reciprocal using 1;
      grind;
    exact h_reciprocal h_growth

-- This requires careful analysis; see formal-conjectures for full proof

/-
## Main Conjecture (OPEN)

The Fabry gap conjecture asks whether the weaker gap condition nₖ/k → ∞ is sufficient
to guarantee that an entire function assumes every value infinitely often.
-/

/-- **Erdős Problem #517 (OPEN)**: The Fejér-Pólya Conjecture on Fabry Gaps.

If f(z) = ∑ aₖz^{nₖ} is an entire function where the exponents nₖ satisfy the
Fabry gap condition nₖ/k → ∞, does f assume every value infinitely often?

This remains open. The difficulty is that Fabry gaps are much weaker than Fejér gaps,
and the complex analysis techniques that work for Fejér gaps don't extend. -/
def fabryGapConjecture : Prop :=
  ∀ (f : ℂ → ℂ) (n : ℕ → ℕ) (a : ℕ → ℂ),
    HasFabryGaps n →
    (∀ z, HasSum (fun k => a k * z ^ n k) (f z)) →
    ∀ w : ℂ, {z : ℂ | f z = w}.Infinite

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['Erdos517.biernacki_theorem', 'harmonicSorry731341']-/
/-
## Biernacki's Theorem (1928)

Under the stronger Fejér gap condition, the value distribution result is proved.
-/

/-- **Biernacki's Theorem (1928)**: Under Fejér gaps, entire functions assume every
value infinitely often.

If f(z) = ∑ aₖz^{nₖ} is an entire function where ∑ 1/nₖ < ∞ (Fejér gaps),
then for every complex number w, the equation f(z) = w has infinitely many solutions.

This is a deep result in complex analysis that combines:
1. Picard's theorem (entire functions miss at most one value)
2. Properties of lacunary series near the boundary
3. Careful analysis of the growth and zero distribution

We state this as an axiom since the proof requires complex analysis beyond Mathlib. -/
axiom biernacki_theorem (f : ℂ → ℂ) (n : ℕ → ℕ) (a : ℕ → ℂ) :
    HasFejerGaps n →
    (∀ z, HasSum (fun k => a k * z ^ n k) (f z)) →
    ∀ w : ℂ, {z : ℂ | f z = w}.Infinite

/-
## Example: Comparing Gap Conditions
-/

/-- The sequence nₖ = 2^k has Fejér gaps (and hence Fabry gaps).
∑ 1/2^k = 1 < ∞, and 2^k/k → ∞. -/
theorem exponential_has_fejer_gaps : HasFejerGaps (fun k => 2^k) := by
  constructor
  · intro a b hab
    exact Nat.pow_lt_pow_right (by norm_num : 1 < 2) hab
  · -- ∑ 1/2^k is dominated by a convergent geometric series
    have h : Summable (fun k : ℕ => ((1 : ℝ) / 2) ^ k) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    refine h.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    simp only [one_div, inv_pow]
    gcongr
    norm_cast

/-- For the exponential sequence, Biernacki's theorem applies:
any entire function f(z) = ∑ aₖz^{2^k} assumes every value infinitely often. -/
theorem exponential_gap_value_distribution (f : ℂ → ℂ) (a : ℕ → ℂ)
    (hf : ∀ z, HasSum (fun k => a k * z ^ (2^k)) (f z)) (w : ℂ) :
    {z : ℂ | f z = w}.Infinite :=
  biernacki_theorem f (fun k => 2^k) a exponential_has_fejer_gaps hf w

end Erdos517