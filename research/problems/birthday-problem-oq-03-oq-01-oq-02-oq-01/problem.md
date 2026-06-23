# Problem: Chen-Stein Method for Poisson Approximation in the k=3 Birthday Problem

**Slug**: birthday-problem-oq-03-oq-01-oq-02-oq-01
**Created**: 2026-04-21
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The parent proof `BirthdayProblemOQ03OQ01OQ02.lean` contains:
```lean
-- Axiomatized: Poisson approximation for triple-coincidence probability
axiom poisson_approx_birthday3 (n d : ℕ) (hn : 0 < n) (hd : 0 < d) :
    |triple_prob n d - (1 - Real.exp (-(n.choose 3 : ℝ) / d ^ 2))| ≤
    C * (n ^ 4 : ℝ) / d ^ 3
```

**Goal**: Prove this axiom using the Chen-Stein method (Arratia-Goldstein-Gordon 1989),
giving a rigorous total variation bound between the triple-coincidence count and a
Poisson random variable.

### Plain Language

The k=3 birthday problem asks: how many people are needed so there's a 50% chance
three share a birthday? The threshold is around n ≈ 82-88. The proof that n scales
like (6d² ln 2)^{1/3} relies on a Poisson approximation: the number of triple-coincident
groups is approximately Poisson(λ) where λ = C(n,3)/d².

The Chen-Stein method (1989) gives rigorous total variation bounds between the actual
distribution and a Poisson approximation for sums of weakly dependent indicator variables.
Applying it here would remove the `axiom poisson_approx_birthday3` and complete the proof.

### Why This Matters

1. Removes an axiom from an existing gallery proof — improves the axiom count from 1 to 0
2. Demonstrates the Chen-Stein method in Lean 4 — a frequently-used technique in combinatorics and probability that is not yet in Mathlib
3. The method generalizes to many "birthday-type" problems: Erdős–Rényi random graphs, random hash collisions, etc.

## Known Results

### What's Already Proven (in BirthdayProblemOQ03OQ01OQ02.lean)

- `asympThreshold`: The k=3 threshold satisfies `asympThreshold d = (6 * d^2 * Real.log 2)^{1/3}`
- `birthday3_threshold_asymptotics`: n*(d) ~ (6d² ln 2)^{1/3} in the limit
- `general_threshold_exponent`: For general k, n*(d) ~ (k! d^{k-1} ln 2)^{1/k}
- `triple_prob n d`: The exact probability of having a triple-coincidence among n people in d days

### What's Still Open

- `poisson_approx_birthday3`: The total variation bound |triple_prob n d - Poisson approx| ≤ C·n⁴/d³

### Our Goal

Prove `poisson_approx_birthday3` using the Chen-Stein method for positively associated
indicators, or find an alternative formulation compatible with existing Mathlib probability tools.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `birthday-problem-oq-03-oq-01-oq-02` | Direct parent — contains the axiom | Threshold asymptotics, choose, div |
| `birthday-problem-oq-03-oq-01` | Grandparent — exact counting | Slot-based recurrence, native_decide |
| `birthday-problem-oq-03` | Great-grandparent — original birthday problem | Inclusion-exclusion |

## Initial Thoughts

### Potential Approaches

1. **Chen-Stein via Mathlib PoissonDistribution** (preferred):
   - Define indicator variables `X_{i,j,k} = 1` if persons i, j, k share a birthday
   - Compute `b1` (sum of covariances within a "neighborhood") and `b2` (cross-neighborhood)
   - Apply Stein's identity bound: TV ≤ min(1, b1 + b2) · something
   - Risk: Mathlib may not have the full Chen-Stein machinery; might need to build key lemmas

2. **Direct moment calculation approach**:
   - Show triple_prob is close to 1 - exp(-λ) via Taylor series
   - Bound the error using |e^{-λ} - Prob| ≤ Var[triple count] / something
   - Risk: This is not Chen-Stein proper; may not give the stated error bound form

3. **Axiom restructuring** (fallback):
   - Convert the axiom to a theorem with a sorry, add it to the Aristotle queue
   - Risk: Aristotle cannot prove this (it requires probabilistic reasoning)

### Key Difficulties

- Chen-Stein method is not in Mathlib — would require building new infrastructure
- Positively associated indicators require correlations to be computed
- The indicator approach needs Lean formalization of discrete probability spaces with
  appropriate conditioning

### What Would a Proof Need?

- Key lemma 1: `X_{i,j,k}` indicators are positively associated (positive correlations)
- Key lemma 2: b1 = O(n⁴/d³) — total covariance within neighborhoods
- Key lemma 3: b2 = O(n⁵/d⁴) — cross-neighborhood correlations (negligible at threshold)
- Technical requirement: Mathlib's `MeasureTheory.PoissonDistribution` or a direct total-variation bound

## Tractability Assessment

**Difficulty**: Medium-High

**Justification**:
- Chen-Stein is a standard technique but requires building probability infrastructure in Lean
- The indicator approach is well-understood mathematically — the challenge is Lean formalization
- Mathlib has `PoissonDistribution` and some total variation machinery, but Chen-Stein proper is missing
- Alternative: could axiomatize a Chen-Stein lemma and prove the specific instance

**First step**: Search Mathlib for `totalVariation`, `PoissonDistribution`, `BernoulliDistribution`,
and any existing Stein-type bounds. Read BirthdayProblemOQ03OQ01OQ02.lean to understand exactly
what `triple_prob` and `poisson_approx_birthday3` expect.

## References

### Papers
- Arratia, Goldstein, Gordon (1989) "Two Moments Suffice for Poisson Approximations: The Chen-Stein Method" — defines the method
- Chen (1975) "Poisson approximation for dependent trials" — original Chen-Stein paper

### Mathlib
- `Mathlib.Probability.Distributions.Poisson` — PoissonDistribution
- `Mathlib.MeasureTheory.Measure.MeasureSpace` — measure theory infrastructure
- `Mathlib.Analysis.SpecialFunctions.ExpDeriv` — exponential function bounds

## Metadata

```yaml
tier: B
significance: 7
tractability: 6
tags:
  - probability
  - poisson-approximation
  - chen-stein
  - birthday-problem
  - axiom-removal
related_proofs:
  - birthday-problem-oq-03-oq-01-oq-02
  - birthday-problem-oq-03-oq-01
  - birthday-problem-oq-03
source: gallery-gap
created: 2026-04-21
```

**Significance**: 7/10
**Tractability**: 6/10
