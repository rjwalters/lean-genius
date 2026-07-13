# Knowledge: erdos-1002-wip-01

## Summary

Gallery proofs exist for `erdos-1002` (main conjecture, 1 axiom, 0 sorries)
and `erdos-1002-oq-01` (supporting lemmas, 0 axioms, 0 sorries). Research task:
formalize the Kesten two-parameter result — f(α, β, n) converges to a Cauchy
distribution — which is a **proved theorem** (not an open conjecture), adding
genuine mathematical content beyond the axiomatized gallery entries.

## Key Facts

- **Main file**: `proofs/Proofs/Erdos1002Problem.lean` — 189 lines, 0 sorries, 1 axiom
  - `erdos_1002_conjecture`: f(α, n) has asymptotic distribution (OPEN — cannot prove)
  - Contains: `deviation`, `innerSum`, `f`, Weyl equidistribution interface
- **OQ-01 file**: `proofs/Proofs/Erdos1002OQ01.lean` — proves Cauchy CDF validity + periodicity for rational α (0 axioms after reduction)
- **Gallery**: `src/data/proofs/erdos-1002/`, `src/data/proofs/erdos-1002-oq-01/`

## The Mathematical Problem

**Open conjecture (Erdős)**: Does f(α, n) = (1/log n) Σ_{k=1}^n (1/2 - {αk}) have
an asymptotic distribution function for 0 < α < 1?

**Known theorem (Kesten 1960)**: The two-parameter variant
  f(α, β, n) = (1/log n) Σ_{k=1}^n (β - {αk})
converges in distribution to Cauchy(0, ρ) where ρ = ρ(α, β) depends on the
Diophantine approximation properties of α.

**Key insight**: The Kesten result IS proved, while the one-parameter case (β = 1/2)
is the open problem. Formalizing Kesten's theorem adds mathematical value without
claiming to resolve the open conjecture.

## Mathlib Infrastructure Available

- `Mathlib.NumberTheory.Equidistribution.Weyl`: Weyl equidistribution theorem
- `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`: Lebesgue measure, convergence in distribution
- `Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan`: arctan for Cauchy CDF
- `Mathlib.Analysis.SpecialFunctions.Log.Basic`: log for normalization
- `Mathlib.Data.Int.Floor`: Int.fract for fractional part
- **OQ-01 infrastructure**: `Erdos1002OQ01.cauchyDistribution`, `IsDistributionFunction`, `innerSum`

## Tractability Assessment

**Tractable approach** — formalize Kesten's two-parameter result:

1. Define `innerSumBeta (α β : ℝ) (n : ℕ) := Σ_{k=1}^n (β - {αk})`
2. Define `fBeta (α β : ℝ) (n : ℕ) := innerSumBeta α β n / log n`
3. Axiomatize the Kesten limit (provable but requires deep CLT + continued fraction theory):
   `axiom kesten_1960 : ∀ (α : ℝ) (hα : Irrational α) (β : ℝ) (hβ : β ∉ ℤ + ℤ•α), ConvergesInDistribution (fBeta α β) (cauchyCDF (rho α β))`
4. Prove: for the one-parameter case (β = 1/2), this reduces to the Erdős conjecture
   if α is algebraic quadratic — giving conditional progress

**Why tractable**: Kesten is proved (1960, hard number theory but not open). We can
axiomatize it cleanly as a single theorem, making the formalization honest and useful.

## Open Questions for This Problem

1. Does Mathlib have enough of the three-distance theorem to prove partial cases?
   Check `Mathlib.NumberTheory.ThreeDistance` for `threeDistance_theorem`.
2. What is ρ(α, β) explicitly? For quadratic irrationals, it's computable from
   the continued fraction expansion of α.
3. Can we prove the periodic case (rational α) directly from `Erdos1002OQ01`?
4. Is there a clean formulation using Mathlib's `ProbabilityMeasure` and `ConvergesInDistribution`?

## Dead Ends

None yet (initial selection).
