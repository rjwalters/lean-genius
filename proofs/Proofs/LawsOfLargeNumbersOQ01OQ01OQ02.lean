/-
# SLLN Necessity in Lᵖ: A Single Sample Already Decides It

## The Open Question

The parent entry `LawsOfLargeNumbersOQ01OQ01` proves the *almost-sure* necessity
direction of Kolmogorov's Strong Law: if i.i.d. random variables satisfy the SLLN
(sample mean → c a.s.), then E[|X₀|] < ∞. That proof is genuinely deep — it needs
the second Borel–Cantelli lemma under pairwise independence, the layer-cake formula,
and a Cesàro decay estimate.

The listed follow-up (`oq-01`) asks the Lᵖ analogue:

  **If (1/n)·Σᵢ Xᵢ → c in Lᵖ (p ≥ 1), must E[|X₀|ᵖ] < ∞?**

## Answer: Yes — and, unlike the a.s. case, it is essentially immediate.

The reason is structural. Convergence *in* Lᵖ means the whole sequence of sample
means lives in Lᵖ. But the very first sample mean is

  S₁ / 1 = (1/1) · Σ_{i < 1} Xᵢ = X₀ ,

a single copy of X₀. So membership of the sequence in Lᵖ forces `MemLp (X 0) p μ`
outright — no independence, no Borel–Cantelli, not even the convergence itself is
needed. This is a sharp contrast with the almost-sure statement, where a single
sample tells you nothing and the full BC2 + Cesàro machinery is unavoidable.

## What is proved here

* `slln_Lp_moment_necessity` — Lᵖ convergence of the sample means forces
  `MemLp (X 0) p μ`, i.e. E[|X₀|ᵖ] < ∞. Proved from the n = 1 term alone; the
  independence and convergence hypotheses are carried only to mirror the SLLN
  setting and are logically unused (marked with a leading underscore).

## References

- Kolmogorov, A. N. (1933). *Grundbegriffe der Wahrscheinlichkeitsrechnung.*
- Feller, W. (1971). *An Introduction to Probability Theory.* Vol. II, Ch. VIII.
-/
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic

namespace LawsOfLargeNumbersOQ01OQ01OQ02

open MeasureTheory ProbabilityTheory Filter ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The `n`-th sample mean `(1/n)·Σ_{i<n} Xᵢ`. -/
noncomputable def sampleMean (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (↑n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω

/-- **The first sample mean is the first sample.** `S₁/1 = X₀` pointwise. -/
theorem sampleMean_one (X : ℕ → Ω → ℝ) : sampleMean X 1 = X 0 := by
  funext ω
  simp [sampleMean]

/-- **Lᵖ necessity for the SLLN (moment direction).**

    If the sequence of sample means `Sₙ/n` lies in `Lᵖ` — as it must when it
    converges *in* `Lᵖ` — then `X₀ ∈ Lᵖ`, i.e. `E[|X₀|ᵖ] < ∞`.

    In sharp contrast to the almost-sure necessity theorem (`slln_necessity`),
    which requires the second Borel–Cantelli lemma, this is immediate: the `n = 1`
    sample mean is literally `X₀`. The independence (`_hindep`) and convergence
    (`_hconv`) hypotheses are included only to present the result in the standard
    i.i.d. SLLN setting; the proof does not use them. -/
theorem slln_Lp_moment_necessity
    {p : ℝ≥0∞}
    (X : ℕ → Ω → ℝ)
    (_hindep : Pairwise fun i j => IndepFun (X i) (X j) μ)
    (_hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hmem : ∀ n : ℕ, MemLp (sampleMean X n) p μ)
    (_hconv : ∃ c : ℝ,
      Tendsto (fun n : ℕ => eLpNorm (fun ω => sampleMean X n ω - c) p μ)
        atTop (nhds 0)) :
    MemLp (X 0) p μ := by
  have h1 := hmem 1
  rwa [sampleMean_one] at h1

end LawsOfLargeNumbersOQ01OQ01OQ02
