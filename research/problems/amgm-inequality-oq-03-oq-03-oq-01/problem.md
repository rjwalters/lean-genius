# Problem: Formalize power mean limits using Filter.Tendsto and Real.rpow

**Slug**: amgm-inequality-oq-03-oq-03-oq-01
**Created**: 2026-04-05T15:41:10-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\lim_{r \to +\infty} M_r(x) = \max_i x_i, \qquad \lim_{r \to -\infty} M_r(x) = \min_i x_i
$$

where $M_r(x) = \left(\frac{1}{n}\sum_{i=1}^n x_i^r\right)^{1/r}$ for $r \neq 0$,
$x_1,\ldots,x_n > 0$.

In Lean 4 (targeting the `powerMean` definition in `AmgmInequalityOQ03OQ03.lean`):
```lean
theorem powerMean_tendsto_max {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) (hx : ∀ i, 0 < x i) :
    Filter.Tendsto (fun r => powerMean x r) Filter.atTop
      (nhds (Finset.univ.sup' Finset.univ_nonempty x))

theorem powerMean_tendsto_min {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) (hx : ∀ i, 0 < x i) :
    Filter.Tendsto (fun r => powerMean x r) Filter.atBot
      (nhds (Finset.univ.inf' Finset.univ_nonempty x))
```

### Plain Language

The power mean M_r of n positive reals converges to the maximum as r → +∞ and to the
minimum as r → -∞. This formalizes both limits using Mathlib's `Filter.Tendsto` and
`Real.rpow` machinery.

### Why This Matters

The limit theorems for power means are classical analysis but remain as comments in the
current gallery proof. Formalizing them with `Filter.Tendsto` demonstrates best-practice
Lean 4 real analysis and completes the gallery entry's story.

## Known Results

### What's Already Proven

- `AmgmInequalityOQ03OQ03.lean` — defines `powerMean`, proves M₁ = AM, M₋₁ = HM (2-point case)
- `amgm-inequality-oq-03-oq-02` — lim_{r→0} M_r = GM (geometric mean)
- `amgm-inequality-oq-03-oq-01` — negative power means M_r ≤ M_s for r ≤ s < 0

### What's Still Open

- `powerMean_tendsto_max` via Filter.atTop
- `powerMean_tendsto_min` via Filter.atBot

### Our Goal

Prove both limit theorems for finite nonempty `Fintype ι` with all `x i > 0`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `amgm-inequality-oq-03-oq-03` | Parent: defines powerMean | Real.rpow, Finset.sum |
| `amgm-inequality-oq-03-oq-02` | Sibling: lim M_r = GM at r=0 | Filter.Tendsto, Real.exp_log |
| `amgm-inequality-oq-03` | Grandparent: weighted power means | ConvexOn, Jensen |

## Initial Thoughts

### Potential Approaches

1. **Squeeze via max domination** (primary):
   - Let M = sup xᵢ. For r > 0: M^r ≤ Σ xᵢʳ ≤ n·M^r
   - So M ≤ M_r ≤ n^{1/r}·M
   - n^{1/r} → 1 via `Real.tendsto_rpow_atTop_of_base_gt_one` (since n ≥ 1)
   - Conclude by squeeze (`tendsto_of_tendsto_of_tendsto_of_le_of_le`)
   - Why it might work: Mathlib has all needed rpow lemmas
   - Risk: `powerMean` definition uses `if r = 0` branch; need to handle the r ≠ 0 regime

2. **Reduction to 1/x + symmetry** (for min):
   - M_{-r}(x) = 1 / M_r(1/x), so min follows from max theorem applied to 1/xᵢ
   - Why it might work: elegant, avoids repeating the argument
   - Risk: need to formalize the reciprocal identity first

### Key Difficulties

- `powerMean` piecewise definition: tactics must case-split or restrict to large r
- `Finset.sup'` vs `Real.iSup`: need to match the definition's `Finset.univ.sup'`
- Strictness: all xᵢ > 0 is used to ensure rpow is well-defined and monotone

### What Would a Proof Need?

- Key lemma: `n^{1/r} → 1` as r → ∞  (`Real.rpow` continuity at exponent 0)
- Key lemma: sum squeeze `M^r ≤ Σ xᵢʳ ≤ n·M^r` via `Finset.sum_le_card_nsmul`
- Key lemma: `(A^{1/r}) → lim A` when A is eventually constant? No — need squeeze properly

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Parent proof already has the `powerMean` definition and Finset setup
- Mathlib has `Filter.Tendsto`, `Real.rpow_natCast`, squeeze lemmas
- The math is classical (Hardy-Littlewood-Pólya, 1952)
- Main challenge: threading rpow inequalities through Lean's type system

**Estimated Effort**:
- Exploration: 1-2 hours (check Mathlib for rpow limit lemmas)
- If tractable: 1-3 days
- If hard: may need auxiliary file or Aristotle for sublemmas

## References

### Papers
- Hardy, Littlewood, Pólya, "Inequalities" (1952) — §2.9: power mean limits

### Mathlib
- `Mathlib.Analysis.MeanInequalities` — power mean inequalities
- `Mathlib.Analysis.SpecialFunctions.Pow.Real` — `Real.rpow` API
- `Mathlib.Topology.Algebra.Order.LiminfLimsup` — squeeze/sandwich lemmas

## Metadata

```yaml
tags:
  - analysis
  - power-means
  - filter-tendsto
  - real-rpow
  - mathlib
  - lean4
related_proofs:
  - amgm-inequality-oq-03-oq-03
  - amgm-inequality-oq-03-oq-02
  - amgm-inequality-oq-03-oq-01
difficulty: medium
source: gallery-gap
created: 2026-04-05T15:41:10-07:00
```
