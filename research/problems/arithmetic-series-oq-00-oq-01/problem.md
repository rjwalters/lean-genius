# Problem: Bijective Proof of Nicomachus's Theorem

**Slug**: arithmetic-series-oq-00-oq-01
**Created**: 2026-04-21T22:19:24+02:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Nicomachus's theorem states:
$$\sum_{k=1}^n k^3 = \left(\sum_{k=1}^n k\right)^2 = T_n^2$$
where $T_n = n(n+1)/2$ is the $n$-th triangular number.

**Problem**: Construct an explicit bijection in Lean 4 between the set of $T_n^2 = (1 + 2 + \cdots + n)^2$ objects (the "staircase square") and the set of $n^3$ objects (the $n$-th cube), and prove it is a bijection.

Concretely: partition $[n]^2$ (an $n \times n$ grid) into "gnomon" L-shapes of sizes $1, 3, 5, \ldots, 2n-1$, and show each $k$-th gnomon bijects with $k^2$ elements of $[k]^3 \setminus [k-1]^3$ (the $k$-th "shell" of the cube). The union gives the full bijection.

### Plain Language

The algebraic proof (`∑ k^3 = T_n^2`) is easy by induction. A bijective proof constructs an actual function $f : \bigsqcup_{k=1}^n [k]^2 \to \bigsqcup_{k=1}^n \{k\} \times [k] \times [k]$ that witnesses the identity combinatorially. This is more informative than the algebraic proof and demonstrates Lean's ability to formalize combinatorial bijections.

### Why This Matters

- Bijective proofs in Lean are a useful formalization technique (Fintype instances, Equiv)
- Nicomachus's theorem is a classic identity connecting cubes and triangular numbers
- Gallery entry `arithmetic-series-oq-00` proves this algebraically; the bijective version would be novel formalization

## Known Results

### What's Already Proven

- In gallery `arithmetic-series-oq-00`: `∑_{k=1}^n k^3 = (n(n+1)/2)^2` (algebraic induction proof)
- Mathlib: `Finset.sum_range_succ`, `Finset.card_product`
- Mathlib: `Equiv` and `Fintype.equivFin` for explicit bijections

### What's Still Open

- Whether a clean bijective proof exists that Lean can verify
- The explicit bijection function and its verification

### Our Goal

Either:
1. Construct an explicit `Equiv (Σ k : Fin n, Fin k × Fin k) (Σ k : Fin n, Fin k × Fin k × Fin k)` that witnesses Nicomachus's theorem bijectively, or
2. Determine that while the identity holds, a clean bijective proof in Lean requires substantially more infrastructure than the inductive proof.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| arithmetic-series-oq-00 | Parent — algebraic proof of Nicomachus | Finset.sum, induction |
| arithmetic-series-oq-02 | Power sums and Faulhaber | higher sum identities |

## Initial Thoughts

### Potential Approaches

1. **Gnomon decomposition**: Partition $\{1, \ldots, T_n\}^2$ into L-shaped gnomons; the $k$-th gnomon has $2k-1$ elements and bijects with $k$ copies of something in the cube. Explicitly:
   - Why it might work: This is the standard visual bijective proof
   - Risk: Encoding L-shaped regions in Lean may be verbose

2. **Sigma type Equiv**: Define `f : (k : Fin n) × (Fin (2*k.val+1)) ≃ (k : Fin n) × (Fin k.val × Fin k.val)` using the gnomon structure, then chain with the cube shell decomposition.
   - Why it might work: Uses `Equiv.sigmaEquiv` and finite type machinery
   - Risk: Getting the indices right requires care

3. **Reformulate and decide**: Show that both sides have the same `Fintype.card`, then use `Fintype.equivOfCardEq` (non-constructive but valid).
   - Why it might work: Trivial if non-constructive bijections are acceptable
   - Risk: Not a "bijective proof" in the combinatorial sense

### Key Difficulties

- Defining the gnomon explicitly (it's an L-shape, not a simple product)
- Establishing injectivity and surjectivity of the bijection
- The bijection involves dependent types (Σ k, ...) which require care

### What Would a Proof Need?

- `Finset.card_biUnion` for partition counting
- `Equiv.trans` to compose bijections
- An explicit encoding of "the k-th gnomon in an n×n grid"

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Approach 3 (non-constructive) is trivial once cardinality is known
- Approach 1-2 (explicit bijection) requires moderate Lean engineering
- The mathematical content is elementary; the challenge is formalization style

## References

### Papers
- Conway & Guy, "The Book of Numbers" — visual proof of Nicomachus
- Proofs Without Words (Nelsen) — staircase square argument

### Mathlib
- `Mathlib.Algebra.BigOperators.Basic` — `Finset.sum`
- `Mathlib.Data.Fintype.Basic` — `Fintype.equivOfCardEq`, `Equiv`
- `Mathlib.Data.Sigma.Basic` — `Sigma` type instances

## Metadata

```yaml
tags:
  - combinatorics
  - number-theory
  - bijective-proof
  - figurate-numbers
  - nicomachus
  - triangular-numbers
related_proofs:
  - arithmetic-series-oq-00
  - arithmetic-series-oq-02
difficulty: medium
source: gallery-gap
created: 2026-04-21T22:19:24+02:00
```

**Significance**: 6/10
**Tractability**: 7/10
