# Problem: Prove the Erdős-Heilbronn Conjecture (replace axiom)

**Slug**: erdos-476
**Created**: 2026-04-22T09:05:08+02:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For a prime $p$ and a subset $A \subseteq \mathbb{Z}/p\mathbb{Z}$ with $|A| \geq 2$, define the restricted sumset:
$$A \mathbin{\hat{+}} A = \{a + b : a, b \in A,\ a \neq b\}$$

Prove:
$$|A \mathbin{\hat{+}} A| \geq \min(2|A| - 3,\ p)$$

### Plain Language

The Erdős-Heilbronn Conjecture (1964), proved by da Silva and Hamidoune in 1994, says
that if you take a set of $n$ distinct elements from $\mathbb{Z}/p\mathbb{Z}$ and add them
in pairs (excluding $a + a$), you get at least $\min(2n-3, p)$ distinct values.

The current gallery proof uses `axiom erdos_heilbronn_bound` as a placeholder.
This problem asks: **replace the axiom with an actual Lean proof**.

### Why This Matters

This is one of the foundational results of additive combinatorics. The proof technique
(originally exterior algebra; alternatively the polynomial method) has been highly
influential. Removing the axiom would make this one of the first complete formalizations
of the da Silva-Hamidoune theorem in Lean 4.

## Known Results

### What's Already Proven in the Gallery

- `erdos-476` (current): `erdos_heilbronn_bound` stated as axiom; all surrounding infrastructure complete:
  - `restrictedSumset` definition
  - `AP_restrictedSumset`: arithmetic progressions achieve exactly $2n-3$ elements
  - `AP_achieves_bound`: tightness of the bound
  - `bound_comparison`: restricted vs unrestricted sumset relationship
  - `card_two_case`: $|A| = 2$ base case verified
  - `card_three_lower_bound`: $|A| = 3$ lower bound
  - `erdos_476_summary`: main theorem (depends on axiom)

### Key Axiom to Remove

```lean
-- proofs/Proofs/Erdos476Problem.lean, line 111
axiom erdos_heilbronn_bound (A : Finset (ZMod p)) (h : 2 ≤ A.card) :
    (restrictedSumset p A).card ≥ min (2 * A.card - 3) p
```

### Our Goal

Prove `erdos_heilbronn_bound` as a theorem, eliminating the axiom. This makes
`erdos_476_summary` and all downstream results fully verified.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `erdos-476-oq-05` | Cauchy-Davenport extremal sets | Vosper's theorem, AP characterization |
| `erdos-476-oq-05-incomplete-01` | Vosper's theorem (incomplete) | Polynomial method |
| `cauchy-davenport` (if exists) | Unrestricted sumsets | Additive combinatorics |

## Initial Thoughts

### Potential Approaches

1. **Polynomial method (Alon-Nathanson-Ruzsa 1995)**: Use the Combinatorial Nullstellensatz.
   Consider the polynomial $f(x, y) = \prod_{i=0}^{n-3}(x + y - c_i)$ for $c_i \notin A \hat{+} A$.
   If $|A \hat{+} A| < 2n-3$, then $f$ vanishes on all $(a, b)$ with $a \neq b$, contradicting
   the Nullstellensatz coefficient condition.
   - Why it might work: Mathlib has `MvPolynomial` and finite field theory; Nullstellensatz is tractable
   - Risk: Combinatorial Nullstellensatz for multivariate case needs careful setup

2. **Exterior algebra (da Silva-Hamidoune 1994)**: Use Grassmann derivatives. The $k$-th
   Grassmann derivative of $\prod_{a \in A}(x - a)$ encodes information about the restricted sumset.
   - Why it might work: The original proof; conceptually clean
   - Risk: Exterior algebra in Lean 4 / Mathlib may require more infrastructure

3. **Induction on |A|**: Base cases $|A| = 2, 3$ are already done. Inductive step via
   a Freiman-type argument.
   - Why it might work: Avoids heavy algebra
   - Risk: The inductive structure is not straightforward; standard proofs do not use simple induction

### Key Difficulties

- The polynomial method proof requires `Finset.sum` manipulation over $\mathbb{Z}/p\mathbb{Z}$
- Need a Lean statement of Combinatorial Nullstellensatz or can use a direct coefficient argument
- The exterior algebra approach requires multilinear algebra infrastructure

### What Would a Proof Need?

- Combinatorial Nullstellensatz: coefficient of $\prod x_i^{t_i}$ in $f$ is nonzero if $f$ does not vanish on product sets. Check if Mathlib has `Polynomial.combinatorialNullstellensatz` or similar.
- Finset cardinality bounds over `ZMod p`
- Polynomial evaluation at structured finite sets

## Tractability Assessment

**Difficulty**: Challenging

**Justification**:
- The mathematics is completely known (proved in 1994)
- The polynomial method proof is shorter and more direct than the exterior algebra proof
- Mathlib has `ZMod`, `Finset`, `MvPolynomial`, and `FiniteField` infrastructure
- Main risk: Combinatorial Nullstellensatz may not be in Mathlib and would need to be proven first

**Estimated Effort**:
- Exploration: 2-3 days (survey Mathlib's polynomial/Nullstellensatz landscape)
- If Nullstellensatz available: 1-2 weeks
- If Nullstellensatz needs building: 3-6 weeks

## References

### Papers
- da Silva, Hamidoune (1994) — *Cyclic spaces for Grassmann derivatives and additive theory*, Bull. London Math. Soc.
- Alon, Nathanson, Ruzsa (1995) — *The polynomial method and restricted sums of congruence classes*, J. Number Theory
- Alon (1999) — *Combinatorial Nullstellensatz*, Combinatorics, Probability and Computing

### Mathlib
- `Mathlib.FieldTheory.Finite.Basic` — `ZMod` finite fields
- `Mathlib.RingTheory.MvPolynomial.Basic` — multivariate polynomials
- `Mathlib.Data.Finset.Card` — cardinality lemmas
- `Mathlib.Algebra.GeomSum` — geometric sum lemmas useful for AP calculations

## Metadata

```yaml
tags:
  - additive-combinatorics
  - finite-fields
  - polynomial-method
  - nullstellensatz
  - erdos-problems
related_proofs:
  - erdos-476-oq-05
  - erdos-476-oq-05-incomplete-01
difficulty: challenging
source: gallery-gap
created: 2026-04-22T09:05:08+02:00
```

**Significance**: 8/10
**Tractability**: 6/10
