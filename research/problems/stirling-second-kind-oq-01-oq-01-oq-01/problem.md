# Problem: Closed form for Stirling numbers S(n,4) via the forced recursion

**Slug**: stirling-second-kind-oq-01-oq-01-oq-01
**Created**: 2026-07-02
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
S(n,4) = \frac{4^{n-1} - 3^{n} + 3\cdot 2^{n-1} - 1}{6}, \qquad n \ge 1,
$$

where $S(n,k)$ is the Stirling number of the second kind (the number of partitions of an $n$-element set into $k$ nonempty blocks).

### Plain Language

The parent gallery proof establishes the closed form $S(n,3) = (3^{n-1} - 2^n + 1)/2$ by solving the forced recursion for the last column. This problem asks to push the same method one column further and prove the explicit formula for $S(n,4)$, the number of ways to partition an $n$-element set into exactly four nonempty groups.

### Why This Matters

Column closed forms for Stirling numbers of the second kind are a clean, fully finite target that exercises recursion-solving in Lean. Extending from $k=3$ to $k=4$ demonstrates that the parent's method generalises and adds a genuinely new, verifiable identity to the gallery.

## Known Results

### What's Already Proven

- $S(n,3) = (3^{n-1} - 2^n + 1)/2$ — parent proof `stirling-second-kind-oq-01-oq-01` (verified).
- The general recurrence $S(m+1,k) = k\,S(m,k) + S(m,k-1)$ — standard and derivable.
- The inclusion–exclusion formula $S(n,k) = \frac{1}{k!}\sum_{j=0}^{k}(-1)^j\binom{k}{j}(k-j)^n$.

### What's Still Open

- A machine-checked proof of the $S(n,4)$ closed form in this repository.
- Whether the induction is cleaner from the recursion $S(m+1,4) = 4\,S(m,4) + S(m,3)$ (reusing the verified $S(n,3)$ form) or directly from inclusion–exclusion.

### Our Goal

Prove `S(n,4) = (4^(n-1) - 3^n + 3*2^(n-1) - 1)/6` for all `n ≥ 1`, ideally by induction on the recursion `S(m+1,4) = 4*S(m,4) + S(m,3)`, substituting the parent's verified `S(n,3)` closed form.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| stirling-second-kind-oq-01-oq-01 | Parent: verified S(n,3) closed form; supplies the S(n,3) term in the recursion | recursion-solving, induction |
| stirling-second-kind-oq-01 | Base column identities and definitions | Stirling recurrence |

## Initial Thoughts

### Potential Approaches

1. **Recursion + substitution**: Induct on `n`, expand `S(m+1,4) = 4*S(m,4) + S(m,3)`, plug in the closed forms for both, and verify the algebraic identity with `ring`.
   - Why it might work: reduces to a polynomial identity in `2^n, 3^n, 4^n` after clearing denominators.
   - Risk: managing the powers `4^(n-1)`, `3^n`, `2^(n-1)` and the `/6` denominator over ℕ vs ℚ.

2. **Inclusion–exclusion**: Prove directly from `S(n,4) = (1/24)∑ (-1)^j C(4,j)(4-j)^n`.
   - Why it might work: closed and non-inductive.
   - Risk: binomial-sum manipulation is heavier than the recursion route.

### Key Difficulties

- Divisibility: showing the numerator is always divisible by 6 to keep everything in ℕ (or work in ℚ throughout).
- Aligning `4^(n-1)` vs `4^n` conventions carefully at the base case `n=1` (`S(1,4)=0`).

### What Would a Proof Need?

- Key lemma 1: the recursion `S(m+1,4) = 4*S(m,4) + S(m,3)` in the repo's chosen `S` definition.
- Key lemma 2: the verified `S(n,3)` closed form, imported from the parent.
- Technical requirements: work over ℚ (or prove the 6 ∣ numerator divisibility) and close with `ring`/`field_simp`.

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- The $k=3$ case is already fully formalized; this is a direct methodological extension.
- Purely finite/algebraic; the hard step is bookkeeping, not mathematics.
- `ring`, `field_simp`, and induction suffice; no missing Mathlib theory.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–2 days

## References

### Papers
- Graham, Knuth, Patashnik, *Concrete Mathematics*, §6.1 — Stirling numbers and column closed forms.

### Online Resources
- OEIS A000453 — Stirling numbers of the second kind S(n,4).

### Mathlib
- Stirling / Bell number infrastructure — definitions and recurrences.
- `ring`, `field_simp`, induction — algebraic closing tactics.

## Metadata

```yaml
tags:
  - combinatorics
  - stirling-numbers
  - closed-form
  - recursion
related_proofs:
  - stirling-second-kind-oq-01-oq-01
  - stirling-second-kind-oq-01
difficulty: low
source: proof-suggestion
created: 2026-07-02
```

**Significance**: 5/10
**Tractability**: 8/10
