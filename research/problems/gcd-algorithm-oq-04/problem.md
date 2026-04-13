# Problem: Unifying EuclideanDomain GCD with GCDMonoid Normalization

## Statement

### Plain Language
Show that in Lean 4/Mathlib, the GCD computed via `EuclideanDomain` (using the Euclidean algorithm) coincides with the `GCDMonoid` normalized GCD. Establish that the `EuclideanDomain` instance for `ℤ` (or a general Euclidean domain) gives a `GCDMonoid` structure where `gcd` satisfies the universal divisibility property and the normalization condition, and that these two algebraic hierarchies are coherent for concrete types like `ℕ` and `ℤ`.

### Formal Statement
$$
\forall \alpha\ [\text{EuclideanDomain}\ \alpha]\ (a\ b : \alpha),\quad
\gcd_{\text{Euclid}}(a, b) \sim \gcd_{\text{GCDMonoid}}(a, b)
$$
where $\sim$ denotes association (unit multiple), and both divide each other.

## Classification

```yaml
tier: B
significance: 6
tractability: 7
tags:
  - algebra
  - lean-mathlib
  - gcd
  - type-theory
  - typeclass-coherence
  - seeker-selected
```

**Significance**: 6/10 — Fills a real gap in Mathlib's algebraic hierarchy coherence; used downstream in any formal number theory that switches between `EuclideanDomain` and `GCDMonoid` APIs.

**Tractability**: 7/10 — Both structures exist in Mathlib; the main challenge is navigating typeclass instances and normalization conditions.

## Why This Matters

1. **Typeclass coherence** — Mathlib has two overlapping GCD abstractions; a formal bridge prevents API mismatches in downstream proofs
2. **Normalization** — `GCDMonoid` requires a canonical representative; `EuclideanDomain.gcd` is not automatically normalized (e.g., `gcd` in `ℤ` can be negative)
3. **Practical formalization** — Number theory proofs often need to switch between polynomial rings (via `EuclideanDomain`) and integers (via `GCDMonoid`); coherence theorems enable this

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| gcd-algorithm | Parent proof: Euclidean GCD algorithm formalized |
| gcd-algorithm-oq-01 | Related: extended Euclidean / Bézout context |
| gcd-algorithm-oq-02 | Related: Binary GCD (Stein's algorithm) |
