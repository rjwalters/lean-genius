# Problem: What happens when variance is infinite

## Statement

### Plain Language
When a distribution has infinite variance (power-law tails P(|X|>x) ~ x^(-α) for α < 2), the sum of n i.i.d. copies normalized by n^(1/α) converges to an α-stable distribution.

### Formal Statement
The characteristic function φ_α(t) = exp(-|t|^α) satisfies the stability property:
[φ_α(t/n^(1/α))]^n = φ_α(t)

## Classification

```yaml
tier: B
significance: 6
tractability: 6
tags:
  - seeker-selected
  - extension
  - challenging
  - probability
  - analysis
  - advanced
  - characteristic-functions
  - stable-distributions
  - infinite-variance
```

**Status**: COMPLETE
**Significance**: 6/10
**Tractability**: 6/10

## Why This Matters

1. Explains convergence for heavy-tailed distributions (finance, physics, internet)
2. Completes the classification of CLT limit distributions
3. Shows Gaussian is a special case (α=2), not the universal limit

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| central-limit-theorem | Parent theorem (finite variance case) |
