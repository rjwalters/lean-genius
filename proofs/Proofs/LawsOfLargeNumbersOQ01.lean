import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Tactic

/-!
# Laws of Large Numbers for Heavy-Tailed Distributions (laws-of-large-numbers-oq-01)

## The Open Question

**What happens with heavy-tailed distributions where variance is infinite?**

The standard WLLN proof via Chebyshev's inequality requires **finite variance** (E[X²] < ∞).
But many important distributions (Pareto α ∈ (1,2), stable laws, Lévy distributions) have
infinite variance while still having a finite first moment E[|X|] < ∞.

Can the LLN still hold for such distributions?

## The Answer: YES, for distributions with finite first moment

**Key insight**: Kolmogorov's SLLN requires only E[|X|] < ∞ (integrability),
NOT finite variance. For heavy-tailed distributions with E[|X|] < ∞ but E[X²] = ∞,
both SLLN and WLLN hold.

**Moment condition hierarchy for LLN**:
```
E[X²] < ∞ → E[|X|] < ∞ → SLLN (Kolmogorov) → WLLN
   ↑               ↑
(Chebyshev     (threshold
 needs this)    for LLN)
```

## Mathlib's SLLN Formulation

`ProbabilityTheory.strong_law_ae` proves:
```
∀ᵐ ω ∂μ, Tendsto (fun n => n⁻¹ • ∑ i ∈ Finset.range n, X i ω) atTop (nhds E[X₀])
```

The hypothesis is only `Integrable (X 0) μ` — no L² condition needed!

## Mathematical Significance

This resolves a common misconception: Chebyshev's failure (for infinite variance)
does NOT mean LLN fails. Kolmogorov's deeper theorem shows the true threshold is
E[|X|] < ∞, not E[X²] < ∞.

This is fundamental for:
- Financial risk models (power-law returns, Pareto α ∈ (1,2))
- Network traffic (heavy-tailed packet sizes)
- Earthquake magnitudes (power-law energy distribution)
-/

namespace LawsOfLargeNumbersOQ01

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable [MeasureTheory.IsProbabilityMeasure μ]

/-!
## Section I: Kolmogorov's SLLN Under Finite Mean Only

The pivotal theorem: Kolmogorov's SLLN requires only integrability (E[|X|] < ∞),
NOT finite variance. This is the key insight for heavy-tailed distributions.
-/

/-- **Kolmogorov's Strong Law of Large Numbers** for heavy-tailed distributions.

    For i.i.d. X₀, X₁, ... with **only** E[|X₀|] < ∞:
    the sample mean `n⁻¹ · ∑ᵢ Xᵢ` converges a.s. to E[X₀].

    **Critical distinction**:
    - Chebyshev WLLN: Requires E[X²] < ∞ (finite variance, L²)
    - Kolmogorov SLLN: Requires only E[|X|] < ∞ (finite mean, L¹)

    So for Pareto α ∈ (1,2), stable(α) for α ∈ (1,2): **SLLN holds even though
    Chebyshev's approach fails** (variance is infinite).

    Direct application of `ProbabilityTheory.strong_law_ae` from Mathlib. -/
theorem slln_under_finite_mean_only
    (X : ℕ → Ω → ℝ)
    (hint : MeasureTheory.Integrable (X 0) μ)  -- E[|X|] < ∞, NO variance condition!
    (hindep : Pairwise fun i j => ProbabilityTheory.IndepFun (X i) (X j) μ)
    (hident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n : ℕ => (↑n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω)
      Filter.atTop
      (nhds (∫ x, X 0 x ∂μ)) :=
  ProbabilityTheory.strong_law_ae X hint hindep hident

/-!
## Section II: SLLN ⟹ WLLN for Heavy-Tailed Distributions
-/

/-- **WLLN for heavy-tailed distributions** via SLLN.

    For i.i.d. distributions with **only finite first moment** (possibly infinite variance):
    The sample mean converges to E[X] in probability.

    Since Chebyshev's approach fails for infinite variance, we derive WLLN from
    Kolmogorov's SLLN: a.s. convergence implies convergence in probability. -/
theorem wlln_for_heavy_tails
    (X : ℕ → Ω → ℝ)
    (hint : MeasureTheory.Integrable (X 0) μ)
    (hindep : Pairwise fun i j => ProbabilityTheory.IndepFun (X i) (X j) μ)
    (hident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hmeas : ∀ (n : ℕ), MeasureTheory.AEStronglyMeasurable
      (fun ω => (↑n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω) μ) :
    MeasureTheory.TendstoInMeasure μ
      (fun (n : ℕ) ω => (↑n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω)
      Filter.atTop
      (fun _ => ∫ x, X 0 x ∂μ) :=
  MeasureTheory.tendstoInMeasure_of_tendsto_ae hmeas
    (slln_under_finite_mean_only X hint hindep hident)

/-!
## Section III: The Necessity of Finite Mean

The condition E[|X|] < ∞ is not just sufficient but also **necessary** for SLLN.
When E[|X|] = ∞ (e.g., Cauchy distribution), the sample mean may fail to converge.

**Kolmogorov's characterization** (1930): For i.i.d. X₀, X₁, ...:
SLLN holds ⟺ E[|X₀|] < ∞.

The "sufficient" direction is `slln_under_finite_mean_only` above.
The "necessary" direction (E[|X|] = ∞ ⟹ SLLN fails) is harder and
requires the Borel-Cantelli lemma applied to tail events {|Xₙ| > nε}.

**Cauchy example**: X₀, X₁, ... ~ Cauchy(0,1) i.i.d.
- E[|X₀|] = ∞ (integral diverges)
- By 1-stability: (X₀ + ... + Xₙ₋₁)/n ~ Cauchy(0,1) for ALL n
- So the sample mean's distribution NEVER concentrates → LLN fails!
-/

/-- **Necessity of finite mean for SLLN**.

    If SLLN holds for i.i.d. X₀, X₁, ..., then E[|X₀|] < ∞.

    This is the converse of `slln_under_finite_mean_only`, completing the
    Kolmogorov characterization: SLLN ⟺ E[|X₀|] < ∞.

    Not currently in Mathlib; proof requires Borel-Cantelli lemma arguments. -/
axiom slln_necessity
    (X : ℕ → Ω → ℝ)
    (hindep : Pairwise fun i j => ProbabilityTheory.IndepFun (X i) (X j) μ)
    (hident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hslln : ∃ (c : ℝ), ∀ᵐ ω ∂μ,
      Filter.Tendsto (fun n : ℕ => (↑n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω)
      Filter.atTop (nhds c)) :
    MeasureTheory.Integrable (X 0) μ

/-!
## Section IV: Pareto Distribution — Key Example

The Pareto distribution with shape α exemplifies the heavy-tail story:
- α > 2: finite variance, both Chebyshev and Kolmogorov apply
- 1 < α ≤ 2: infinite variance, finite mean — Chebyshev fails, SLLN holds!
- α ≤ 1: infinite mean — LLN FAILS

The critical threshold E[|X|] < ∞ is precisely when α > 1.
For Pareto(α, x_m): E[X] = αx_m/(α-1) < ∞ iff α > 1.
-/

/-- Chebyshev's finite variance condition implies Kolmogorov's integrability condition.

    If a random variable has finite variance (is in L²), then it has finite mean (is in L¹).
    This shows the WLLN via Chebyshev is a special case: whenever Chebyshev applies,
    Kolmogorov's SLLN also applies (and gives a stronger result).

    The converse fails: there exist L¹ distributions that are NOT L²
    (e.g., Pareto(α, x_m) with 1 < α ≤ 2 has finite mean but infinite variance). -/
theorem finite_variance_implies_slln_applicable
    (X : ℕ → Ω → ℝ)
    (hL2 : ∀ i, MeasureTheory.Memℒp (X i) 2 μ) :
    MeasureTheory.Integrable (X 0) μ :=
  (hL2 0).integrable (by norm_num)

/-!
## Main Theorem: Complete Answer to the Open Question

For i.i.d. heavy-tailed distributions with **finite first moment** E[|X|] < ∞:
- SLLN holds: sample mean → E[X] almost surely
- WLLN holds: sample mean → E[X] in probability
- Neither requires finite variance E[X²] < ∞!

The threshold for LLN is exactly E[|X|] < ∞ (Kolmogorov 1930).
-/

/-- **Kolmogorov's complete characterization of SLLN** (1930).

    For i.i.d. random variables X₀, X₁, ...:
    SLLN holds (sample mean converges a.s.) ⟺ E[|X₀|] < ∞.

    This is the "iff" form, combining:
    - `slln_under_finite_mean_only`: E[|X₀|] < ∞ → SLLN (sufficient direction, from Mathlib)
    - `slln_necessity`: SLLN → E[|X₀|] < ∞ (necessary direction, axiomatized) -/
theorem kolmogorov_slln_characterization
    (X : ℕ → Ω → ℝ)
    (hindep : Pairwise fun i j => ProbabilityTheory.IndepFun (X i) (X j) μ)
    (hident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ) :
    MeasureTheory.Integrable (X 0) μ ↔
    ∃ (c : ℝ), ∀ᵐ ω ∂μ,
      Filter.Tendsto (fun n : ℕ => (↑n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω)
      Filter.atTop (nhds c) := by
  constructor
  · intro hint
    exact ⟨∫ x, X 0 x ∂μ, slln_under_finite_mean_only X hint hindep hident⟩
  · intro ⟨c, hconv⟩
    exact slln_necessity X hindep hident ⟨c, hconv⟩

/-- **Main theorem**: LLN holds for heavy-tailed distributions with finite mean.

    This directly answers the open question: infinite variance does NOT cause
    LLN failure. Only infinite first moment (E[|X|] = ∞) causes failure.

    Proof: `ProbabilityTheory.strong_law_ae` needs only `Integrable (X 0)`,
    which is exactly E[|X₀|] < ∞. No finite variance assumption is needed! -/
theorem lln_heavy_tail_answer
    (X : ℕ → Ω → ℝ)
    (hint : MeasureTheory.Integrable (X 0) μ)  -- E[|X|] < ∞, variance may be ∞!
    (hindep : Pairwise fun i j => ProbabilityTheory.IndepFun (X i) (X j) μ)
    (hident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n : ℕ => (↑n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω)
      Filter.atTop
      (nhds (∫ x, X 0 x ∂μ)) :=
  ProbabilityTheory.strong_law_ae X hint hindep hident

/-!
## Section V: Lᵖ Distributions (p ≥ 1) also satisfy SLLN

For p ≥ 1, any Lᵖ random variable is also L¹ (integrable).
So SLLN applies whenever E[|X|ᵖ] < ∞ for ANY p ≥ 1.
-/

/-- **SLLN for Lᵖ distributions** (p ≥ 1).

    If X has finite p-th moment for some p ≥ 1, then Kolmogorov's SLLN applies.
    The key: `Memℒp X p μ` with `p ≥ 1` implies `Integrable X μ` (finite first moment).

    This covers all classical cases:
    - p = 1: L¹ (finite mean) — minimum for LLN
    - p = 2: L² (finite variance) — Chebyshev's condition
    - p > 2: higher moments — all sufficient for SLLN -/
theorem slln_for_Lp_distributions
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (X : ℕ → Ω → ℝ)
    (hLp : ∀ i, MeasureTheory.Memℒp (X i) p μ)
    (hindep : Pairwise fun i j => ProbabilityTheory.IndepFun (X i) (X j) μ)
    (hident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n : ℕ => (↑n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω)
      Filter.atTop
      (nhds (∫ x, X 0 x ∂μ)) :=
  slln_under_finite_mean_only X ((hLp 0).integrable hp) hindep hident

/-!
## Section VI: Mean-Zero and Centered Distributions
-/

/-- **SLLN for mean-zero distributions**: sample mean converges to 0 almost surely.

    For centered or symmetric distributions with E[X₀] = 0 and E[|X₀|] < ∞,
    the sample mean converges a.s. to 0.

    Common cases: symmetric stable distributions with α ∈ (1, 2) (infinite variance
    but finite mean, centered). These are ubiquitous in financial modeling. -/
theorem slln_mean_zero
    (X : ℕ → Ω → ℝ)
    (hint : MeasureTheory.Integrable (X 0) μ)
    (hmean : ∫ x, X 0 x ∂μ = 0)
    (hindep : Pairwise fun i j => ProbabilityTheory.IndepFun (X i) (X j) μ)
    (hident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n : ℕ => (↑n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω)
      Filter.atTop
      (nhds 0) := by
  simpa [hmean] using slln_under_finite_mean_only X hint hindep hident

end LawsOfLargeNumbersOQ01
