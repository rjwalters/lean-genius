# Problem: Nicomachus's Theorem — Sum of Cubes = Square of Triangular Number

**Slug**: arithmetic-series-oq-00
**Created**: 2026-04-06
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\sum_{k=1}^{n} k^3 = \left(\frac{n(n+1)}{2}\right)^2 = T_n^2
$$

where $T_n = \sum_{k=1}^{n} k = \frac{n(n+1)}{2}$ is the $n$-th triangular number.

In Lean notation:
```lean
theorem nicomachus (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), k ^ 3 =
    (∑ k ∈ Finset.range (n + 1), k) ^ 2
```

### Plain Language

The sum of the first n perfect cubes (1³ + 2³ + 3³ + ... + n³) equals the square
of the sum of the first n natural numbers (1 + 2 + ... + n). Since the latter equals
n(n+1)/2 (the n-th triangular number), we get: 1³ + 2³ + ... + n³ = [n(n+1)/2]².

Example: 1³ + 2³ + 3³ = 1 + 8 + 27 = 36 = 6² = (1+2+3)².

### Why This Matters

This is one of the most beautiful identities in elementary number theory — a deep
connection between two simple-looking sequences (cubes and triangular numbers). It was
known to Nicomachus of Gerasa around 100 CE and connects to:
- Figurate number theory (the basis of arithmetic-series-oq-02 and higher-dimensional extensions)
- Faulhaber's formulas (∑k^p generalizations)
- The "staircase square" visual proof: n³ = (odd numbers from T_{n-1}+1 to T_n)

## Known Results

### What's Already Proven

- **arithmetic-series**: Gauss formula ∑k = n(n+1)/2 with `Finset.sum_range_id` (verified, 0 sorries)
- **arithmetic-series-oq-02**: Simplicial numbers — higher-dimensional sums (gallery)
- Mathlib `Finset.sum_range_id`: ∑_{i<n} i = n*(n-1)/2

### What's Still Open in Gallery

- No Lean 4 formalization of Nicomachus's theorem exists in the gallery
- The arithmetic-series gallery proof lists this explicitly as an open question:
  "Formalize Nicomachus's theorem: the sum of the first n cubes equals the square
  of the n-th triangular number" — listed in `openQuestions[0]`

### Our Goal

Prove `∑_{k=0}^{n} k³ = (∑_{k=0}^{n} k)²` in Lean 4, building on:
1. `Finset.sum_range_id` for the triangular number formula
2. Either induction or direct algebraic manipulation

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `arithmetic-series` | Parent: proves ∑k = n(n+1)/2 which appears squared on RHS | `Finset.sum_range_id`, `ring`, `omega` |
| `arithmetic-series-oq-02` | Generalizes to simplicial numbers | Figurate number theory |
| `mathematical-induction` | Canonical induction template in gallery | Lean `induction` tactic |

## Initial Thoughts

### Potential Approaches

1. **Approach A: Direct induction**
   - Induct on n, use inductive hypothesis ∑_{k≤n-1} k³ = T_{n-1}²
   - Show T_n² - T_{n-1}² = n³ (telescoping)
   - Key identity: T_n² - T_{n-1}² = (T_n - T_{n-1})(T_n + T_{n-1}) = n · T_{2n-1}/...
   - Actually: T_n² - T_{n-1}² = (n(n+1)/2)² - (n(n-1)/2)² = n² · (n+1+n-1)/4 · (n+1-n+1)/2
   - = n² · (2n)/4 · 2/2... let me compute: [(n(n+1))² - (n(n-1))²]/4 = n²[(n+1)² - (n-1)²]/4 = n²[4n]/4 = n³ ✓
   - So T_n² - T_{n-1}² = n³ follows from `ring` after unfolding T_n
   - Why it might work: straightforward algebraic identity, `ring` should close it
   - Risk: handling natural number subtraction / casting ℕ vs ℤ

2. **Approach B: Check Mathlib**
   - Search for `Finset.sum_range_id_pow`, `sum_cubes`, `nicomachus`
   - Mathlib may already have this; could be a direct application
   - Why it might work: Mathlib is comprehensive for elementary identities
   - Risk: May not exist by that name; Lean API changes

3. **Approach C: Algebraic identity via `ring` on ℤ, then cast**
   - Prove the identity as a polynomial identity in ℤ[n]
   - Use `Finset.sum_comm` and `ring` to verify the algebraic steps
   - Why it might work: polynomial identity proofs are robust via `ring`
   - Risk: casting complications between ℕ and ℤ for division

### Key Difficulties

- Natural number division: n(n+1)/2 in ℕ requires 2 | n(n+1), which holds since one of n, n+1 is even
- Index conventions: Lean uses 0-indexed `Finset.range (n+1)` vs classical 1..n notation
- The identity needs the triangular number formula proved first (already in Mathlib)

### What Would a Proof Need?

- Key lemma 1: `Finset.sum_range_id` — ∑_{i < n} i = n*(n-1)/2 (in Mathlib)
- Key lemma 2: n(n+1) % 2 = 0 (or working in ℤ to avoid division issues)
- Key lemma 3: Telescoping identity (T_n)² - (T_{n-1})² = n³
- Technical: `ring` or `omega` for polynomial arithmetic

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- The induction step reduces to `n(n+1) · n(n-1)` vs `n³` which is a polynomial identity
- Lean's `ring` tactic handles multivariate polynomial identities automatically
- Mathlib already has all prerequisite lemmas (`Finset.sum_range_id`)
- Similar identity proofs in the gallery (arithmetic-series) used ring + omega successfully
- Main challenge is index bookkeeping, not mathematical difficulty

**Estimated Effort**:
- Exploration: 1-2 hours (Mathlib search + approach selection)
- If tractable: 1-2 days for complete Lean proof
- If hard: unlikely — this is a canonical textbook exercise

## References

### Papers
- Nicomachus of Gerasa, *Introduction to Arithmetic* (~100 CE) — original discovery
- Faulhaber, J. (1631) — general formula for ∑k^p (Bernoulli numbers)

### Online Resources
- Mathlib: `Mathlib.Algebra.BigOperators.Intervals` — contains `Finset.sum_range_id`
- OEIS A000537: Sum of cubes 1³+2³+...+n³ = [n(n+1)/2]²

### Mathlib
- `Finset.sum_range_id` — ∑_{i < n} i = n*(n-1)/2
- `Finset.sum_range_succ` — inductive step for range sums
- `Nat.odd_or_even` (or `dvd_mul_of_dvd_left`) — for divisibility 2 | n(n+1)

## Metadata

```yaml
tags:
  - number-theory
  - elementary-algebra
  - induction
  - power-sums
  - figurate-numbers
  - nicomachus
related_proofs:
  - arithmetic-series
  - arithmetic-series-oq-02
  - mathematical-induction
difficulty: low
tractability: 8
significance: 6
tier: B
source: gallery-gap
created: 2026-04-06
```
