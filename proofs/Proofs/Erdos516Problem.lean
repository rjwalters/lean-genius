/-
Erdős Problem #516: Gap Series and the Minimum Modulus Problem

**Statement**: Let f(z) = Σ aₖzⁿᵏ be an entire function of finite order such that
nₖ/k → ∞ (Fabry gaps). Define M(r) = max_{|z|=r} |f(z)| and m(r) = min_{|z|=r} |f(z)|.
Is it true that lim sup (log m(r))/(log M(r)) = 1?

**Answer**: YES - proved by Fuchs (1963)

**Historical Development**:
- Pólya (1929): Originally posed this question
- Wiman (1914): Proved under (nₖ₊₁ - nₖ)² > nₖ
- Erdős & Macintyre (1954): Proved under Σ 1/(nₖ₊₁ - nₖ) < ∞
- Fuchs (1963): Full solution - lim sup = 1 for Fabry gaps
- Kovári (1965): Extended to nₖ > k(log k)^{2+c}

**Related Open Problem**: Does Σ 1/nₖ < ∞ suffice for arbitrary entire functions?

Reference: https://erdosproblems.com/516
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open scoped Nat
open Filter Real Set Topology

namespace Erdos516

/-
## Gap Series Definitions

A **gap series** is a power series where many coefficients are zero.
The sequence (nₖ) records the positions of nonzero coefficients.
-/

/-- The Fabry gap condition: nₖ/k → ∞.
    This means the gaps between nonzero terms grow faster than linear. -/
def HasFabryGaps (n : ℕ → ℕ) : Prop :=
  Tendsto (fun k => (n k : ℝ) / k) atTop atTop

/-- The Fejér gap condition: Σ 1/nₖ < ∞.
    A weaker condition than Fabry gaps. -/
def HasFejerGaps (n : ℕ → ℕ) : Prop :=
  Summable (fun k => (1 : ℝ) / n k)

/-- Fabry gaps are stronger than Fejér gaps.
    If nₖ/k → ∞, then nₖ grows superlinearly, so 1/nₖ is summable. -/
theorem fabry_implies_fejer (n : ℕ → ℕ) (hn : HasFabryGaps n) :
    HasFejerGaps n := by
  -- This follows from the comparison test: if nₖ/k → ∞ then
  -- eventually nₖ > k², so Σ 1/nₖ < Σ 1/k² < ∞
  sorry

/-
## Entire Functions of Finite Order

An entire function is analytic on all of ℂ.
Finite order means the growth is at most exponential in |z|^a for some a.
-/

/-- An entire function f is of finite order if there exist c, a ≥ 0
    such that |f(z)| ≤ c · exp(|z|^a) for all z. -/
def OfFiniteOrder (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ ∃ c ≥ (0 : ℝ), ∃ a ≥ (0 : ℝ), ∀ z : ℂ, ‖f z‖ ≤ c * rexp (‖z‖ ^ a)

/-- The order of an entire function is the infimum of valid exponents a. -/
noncomputable def orderOf (f : ℂ → ℂ) : ℝ :=
  sInf { a : ℝ | a ≥ 0 ∧ ∃ c ≥ (0 : ℝ), ∀ z : ℂ, ‖f z‖ ≤ c * rexp (‖z‖ ^ a) }

/-
## Maximum and Minimum Modulus

For an entire function f, we study its behavior on circles |z| = r.
-/

/-- The maximum modulus M(r) = max_{|z|=r} |f(z)|. -/
noncomputable def maxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  ⨆ z : {z : ℂ // ‖z‖ = r}, ‖f z‖

/-- The minimum modulus m(r) = min_{|z|=r} |f(z)|. -/
noncomputable def minModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  ⨅ z : {z : ℂ // ‖z‖ = r}, ‖f z‖

/-- The ratio log m(r) / log M(r). -/
noncomputable def modulusRatio (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  (minModulus f r).log / (maxModulus f r).log

/-
## The Main Theorems

Fuchs (1963) proved that for Fabry gap series of finite order,
lim sup (log m(r))/(log M(r)) = 1.
-/

/--
**Fuchs's Theorem (1963)** - The Solution to Erdős Problem #516

Let f(z) = Σ aₖzⁿᵏ be an entire function of finite order with Fabry gaps (nₖ/k → ∞).
Then lim sup (log m(r))/(log M(r)) = 1.

More precisely, for any ε > 0, log m(r) > (1-ε) log M(r) holds outside
a set of logarithmic density 0.

This is axiomatized as the proof requires deep complex analysis
(Nevanlinna theory, Phragmén-Lindelöf principles) beyond current Mathlib.
-/
axiom fuchs_theorem {f : ℂ → ℂ} {n : ℕ → ℕ}
    (hn : HasFabryGaps n) {a : ℕ → ℂ}
    (hf_sum : ∀ z, HasSum (fun k => a k * z ^ n k) (f z))
    (hf_order : OfFiniteOrder f) :
    limsup (fun r => modulusRatio f r) atTop = 1

/-
## Historical Precedents

Earlier results under stronger gap conditions.
-/

/--
**Wiman's Theorem (1914)**

Under the stronger condition (nₖ₊₁ - nₖ)² > nₖ,
we get lim sup m(r)/M(r) = 1 (without logarithms!).
-/
/--
**Erdős-Macintyre Theorem (1954)**

Under Σ 1/(nₖ₊₁ - nₖ) < ∞, the result holds.
-/
/-
## Extensions Beyond Finite Order

Kovári (1965) extended the result to entire functions of infinite order
under a stronger gap condition.
-/

/--
**Kovári's Theorem (1965)**

For any entire function (not necessarily of finite order) with gaps
nₖ > k(log k)^{2+c} for some c > 0, the lim sup is still 1.
-/
/-
## The Remaining Open Question

Kovári's condition nₖ > k(log k)^{2+c} is stronger than Fejér gaps (Σ 1/nₖ < ∞).
It remains open whether Fejér gaps suffice for arbitrary entire functions.
-/

/--
**Open Conjecture**: Does Σ 1/nₖ < ∞ suffice?

For any entire function f(z) = Σ aₖzⁿᵏ with Fejér gaps,
is lim sup (log m(r))/(log M(r)) = 1?

Macintyre (1952) showed this would be optimal: if Σ 1/nₖ = ∞,
counterexamples exist.
-/
def fejer_gap_conjecture : Prop :=
  ∀ {f : ℂ → ℂ} {n : ℕ → ℕ},
    HasFejerGaps n →
    ∀ {a : ℕ → ℂ}, (∀ z, HasSum (fun k => a k * z ^ n k) (f z)) →
    Differentiable ℂ f →
    limsup (fun r => modulusRatio f r) atTop = 1

/--
**Macintyre's Counterexample (1952)**

Given any sequence (nₖ) with Σ 1/nₖ = ∞, there exists an entire function
f(z) = Σ aₖzⁿᵏ that tends to 0 along the positive real axis.

This shows Fejér gaps would be the optimal condition if the conjecture holds.
-/
/-
## The Answer to Erdős Problem #516

The original question (for finite order with Fabry gaps) was answered
affirmatively by Fuchs in 1963.
-/

/-- Erdős Problem #516 is SOLVED: The answer is YES for finite order + Fabry gaps. -/
theorem erdos_516_solved :
    ∀ {f : ℂ → ℂ} {n : ℕ → ℕ},
      HasFabryGaps n →
      ∀ {a : ℕ → ℂ}, (∀ z, HasSum (fun k => a k * z ^ n k) (f z)) →
      OfFiniteOrder f →
      limsup (fun r => modulusRatio f r) atTop = 1 :=
  fun hn _ hf_sum hf_order => fuchs_theorem hn hf_sum hf_order

end Erdos516
