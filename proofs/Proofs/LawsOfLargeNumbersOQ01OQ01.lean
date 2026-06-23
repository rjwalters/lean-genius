/-
# SLLN Necessity: Proving the Converse of Kolmogorov's Strong Law

## The Open Question

**Can the converse direction (slln_necessity) be proved in Mathlib?**

In `LawsOfLargeNumbersOQ01`, the full Kolmogorov characterization is stated:

  SLLN holds ⟺ E[|X₀|] < ∞

The sufficiency direction (E[|X₀|] < ∞ → SLLN) is handled by Mathlib's
`ProbabilityTheory.strong_law_ae`. But the necessity direction — that SLLN
convergence **forces** finite expectation — was left as an axiom.

## Answer: Yes, with Borel-Cantelli machinery

**Proof strategy** (contradiction):
1. Assume SLLN holds: (1/n) Σᵢ Xᵢ(ω) → c a.s. for some c ∈ ℝ
2. By Cesàro: Xₙ(ω)/n → 0 a.s.
3. If E[|X₀|] = ∞ then (layer cake): Σₙ P(|X₀| > n) = ∞
4. By identical distribution: Σₙ P(|Xₙ| > n) = ∞
5. **Borel-Cantelli for pairwise independent events** (BC2): |Xₙ| > n i.o. a.s.
6. But from step 2: |Xₙ|/n → 0 a.s., so |Xₙ| ≤ n for all large n a.s. — contradiction!

## Key Infrastructure Built

- **Layer cake theorem**: E[|X|] = ∞ ↔ Σₙ P(|X| > n) = ∞ (both directions)
- **Cesàro lemma**: convergence of sample mean implies Xₙ/n → 0
- **BC2 for pairwise independence**: variance bound Var(S_N) ≤ E[S_N] via
  pairwise independence of indicator functions, then Chebyshev gives P(S_N ≤ M) → 0

## Status

Complete: 0 axioms, 0 sorries. See `LawsOfLargeNumbersOQ01Aristotle` for full proof.

## References

- Etemadi, N. (1981). "An elementary proof of the strong law of large numbers".
- Feller, W. (1971). "An Introduction to Probability Theory". Vol. II, Ch. VIII.
-/
import Proofs.LawsOfLargeNumbersOQ01Aristotle

namespace LawsOfLargeNumbersOQ01OQ01

open MeasureTheory ProbabilityTheory Filter ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **SLLN Necessity** (Converse of Kolmogorov's Strong Law).

    If i.i.d. random variables satisfy the SLLN — their sample mean converges
    almost surely to some constant — then they must have finite first moment.

    This completes Kolmogorov's characterization:
      SLLN holds ⟺ E[|X₀|] < ∞

    The proof proceeds by contradiction: assume E[|X₀|] = ∞. By the layer cake
    formula, Σₙ P(|Xₙ| > n) = ∞. The second Borel-Cantelli lemma (adapted for
    pairwise independence via Chebyshev's inequality) then gives P(|Xₙ| > n i.o.) = 1.
    But SLLN implies Xₙ/n → 0 a.s. via Cesàro, so |Xₙ| ≤ n eventually a.s. —
    a contradiction. -/
theorem slln_necessity
    (X : ℕ → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i))
    (hindep : Pairwise fun i j => IndepFun (X i) (X j) μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hslln : ∃ (c : ℝ), ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => (↑n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω)
      atTop (nhds c)) :
    Integrable (X 0) μ :=
  LawsOfLargeNumbersOQ01.slln_necessity_statement X hmeas hindep hident hslln

end LawsOfLargeNumbersOQ01OQ01
