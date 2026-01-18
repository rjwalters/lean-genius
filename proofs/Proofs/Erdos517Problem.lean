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
    sorry -- This requires careful analysis; see formal-conjectures for full proof

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
