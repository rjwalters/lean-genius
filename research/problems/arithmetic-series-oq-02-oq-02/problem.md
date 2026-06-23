# Problem: k-dimensional Hockey Stick Identity

**Slug**: arithmetic-series-oq-02-oq-02-oq-01
**Created**: 2026-03-22
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
\sum_{\substack{i_1 + i_2 + \cdots + i_d \leq n}} \prod_{j=1}^{d} \binom{i_j + k_j}{k_j} = \binom{n + k_1 + k_2 + \cdots + k_d + d}{k_1 + k_2 + \cdots + k_d + d}
$$

Prove the k-dimensional hockey stick identity by induction on dimension $d$, using the 2D case as the inductive step.

### Plain Language

The 2D hockey stick identity sums products of binomial coefficients over a triangular region. The k-dimensional version sums over a simplex. We want to prove the general case by induction on dimension, where each step applies the 2D identity to reduce the dimension by 1.

### Why This Matters

- Generalizes one of the most elegant combinatorial identities
- Connects to lattice path counting in d dimensions
- Foundation for multivariate generating function identities
- Applications in enumerative combinatorics and statistical mechanics

## Known Results

### What's Already Proven

- 2D Hockey Stick Identity (arithmetic-series-oq-02-oq-02) — fully formalized, 0 sorries
- Standard 1D hockey stick: ∑ᵢ C(i+k, k) = C(n+k+1, k+1) — from Mathlib

### What's Still Open

- k-dimensional generalization
- Connection to Vandermonde identity via generating functions
- Combinatorial bijection proof (lattice paths)

### Our Goal

Prove the k-dimensional hockey stick identity by induction on dimension d, using the 2D case (already proved) as the inductive step.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| arithmetic-series-oq-02-oq-02 | Direct parent — 2D hockey stick | Induction, Nat.choose, Finset.sum |
| arithmetic-series-oq-02 | Arithmetic series | Summation formulas |
| binomial-theorem | Binomial theorem | Nat.choose properties |
| binomial-theorem-oq-02 | Multinomial theorem | Multi-index summation |

## Initial Thoughts

### Potential Approaches

1. **Induction on dimension d**
   - Why it might work: Base case d=2 is proved. Inductive step sums over one coordinate using 1D hockey stick, reducing to (d-1)-dimensional identity
   - Risk: Finset manipulation for simplex summation may be complex in Lean

2. **Generating functions**
   - Why it might work: The identity corresponds to coefficient extraction from (1-x)^{-(k+1)} products
   - Risk: Requires formal power series infrastructure

### Key Difficulties

- Defining the d-dimensional simplex sum as a Finset
- Managing the inductive step's bookkeeping for multi-index sums
- Type-level dimension parameter (Fin d or ℕ-indexed)

### What Would a Proof Need?

- Key lemma: Simplex sum factorization — sum over {i₁+...+iₐ ≤ n} splits as ∑ᵢ₁ ∑_{i₂+...+iₐ ≤ n-i₁}
- The 2D base case (already proved)
- Nat.choose addition identities from Mathlib

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Base case is already formalized
- Induction structure is clear
- Main challenge is Finset manipulation for simplices
- Mathlib has strong Nat.choose and Finset infrastructure

**Estimated Effort**:
- Exploration: 1 day
- If tractable: 3-5 days

## References

### Mathlib
- `Mathlib.Data.Nat.Choose.Sum` — hockey stick and Vandermonde identities
- `Mathlib.Data.Nat.Choose.Basic` — binomial coefficient properties
- `Mathlib.Data.Finset.NatAntidiagonal` — antidiagonal for simplex sums

## Metadata

```yaml
tags:
  - combinatorics
  - binomial-coefficients
  - hockey-stick
  - induction
  - generalization
related_proofs:
  - arithmetic-series-oq-02-oq-02
  - arithmetic-series-oq-02
  - binomial-theorem
  - binomial-theorem-oq-02
difficulty: medium
source: proof-suggestion
created: 2026-03-22
```

**Significance**: 7/10
**Tractability**: 6/10
