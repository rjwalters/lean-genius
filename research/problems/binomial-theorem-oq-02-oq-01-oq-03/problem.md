# Problem: Multinomial Covariance — Cov(Xi, Xj) = −n·pi·pj

## Statement

### Plain Language

If (X₁, …, Xₖ) ~ Multinomial(n; p₁, …, pₖ), prove that for i ≠ j:

  Cov(Xᵢ, Xⱼ) = −n · pᵢ · pⱼ

This is the off-diagonal covariance of the multinomial distribution. The result
follows from Var(Σ Xᵢ) = 0 combined with marginal variances Var(Xᵢ) = n·pᵢ·(1−pᵢ).

### Formal Statement

```lean
-- Prerequisite: binomial-theorem-oq-02-oq-01 provides PMF.multinomial
-- Goal: prove the off-diagonal covariance formula

theorem multinomial_cov (n : ℕ) (p : Fin k → ℝ) (hp : ∑ i, p i = 1)
    (hpos : ∀ i, 0 ≤ p i) (i j : Fin k) (hij : i ≠ j)
    (X : Fin k → Ω → ℝ) (hX : IsMultinomial n p X) :
    covariance (X i) (X j) = -↑n * p i * p j := by
  sorry
```

Proof strategy:
1. Var(X₁ + … + Xₖ) = Var(n) = 0 (constant sum)
2. Expand: Σᵢ Var(Xᵢ) + 2 Σᵢ<ⱼ Cov(Xᵢ,Xⱼ) = 0
3. Marginal Xᵢ ~ Bin(n, pᵢ), so Var(Xᵢ) = n·pᵢ·(1−pᵢ)
4. By symmetry and Σpᵢ = 1, solve for Cov(Xᵢ,Xⱼ)

## Classification

```yaml
tier: B
significance: 6
tractability: 7
tags:
  - probability
  - statistics
  - multinomial-distribution
  - covariance
  - mathlib
```

**Significance**: 6/10 — Standard probability result, important for statistics
**Tractability**: 7/10 — Clear proof path via variance decomposition

## Origin

- **Source proof**: `binomial-theorem-oq-02-oq-01` — Multinomial Distribution and MGF
- **Open question**: OQ-03 — "Can the variance-covariance matrix Cov(Xi, Xj) = -n*pi*pj be proved?"

## Why This Matters

1. **Completes the multinomial toolkit** — covariance is essential for any statistical
   analysis using multinomial distributions
2. **Connects to CLT for multinomials** — covariance structure underlies the multivariate
   CLT for sample proportions
3. **Mathlib gap** — this off-diagonal covariance formula may be missing from Mathlib's
   `ProbabilityTheory` namespace

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `binomial-theorem-oq-02-oq-01` | Parent: Multinomial PMF and MGF |
| `binomial-theorem-oq-02` | Multinomial theorem (algebraic) |
| `central-limit-theorem-oq-01` | CLT requires covariance structure |
| `shannon-entropy-oq-01` | Information theory uses multinomial distribution |
