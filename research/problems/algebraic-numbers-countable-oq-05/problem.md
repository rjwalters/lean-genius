# Problem: Algebraic Numbers Countable: Cantor Height Function Proof (1874)

**Slug**: algebraic-numbers-countable-oq-05
**Created**: 2026-04-23T13:50:28+02:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
H(a_0 + a_1 x + \cdots + a_n x^n) = n + |a_0| + |a_1| + \cdots + |a_n|
$$

For each $k \in \mathbb{N}$, the set $\{p \in \mathbb{Z}[x] \mid H(p) = k\}$ is finite,
each polynomial has finitely many roots, so the algebraic numbers are enumerable via
$\mathbb{A} = \bigcup_{k=0}^\infty \text{roots}(\{p : H(p) = k\})$.

### Plain Language

Cantor's 1874 original proof of the countability of algebraic numbers uses a **height
function** to organize polynomials. Define the height of a polynomial
$p(x) = a_0 + a_1 x + \cdots + a_n x^n$ as $H(p) = n + |a_0| + \cdots + |a_n|$.

Key steps:
1. For each height $k$, there are finitely many integer polynomials of height $k$
2. Each such polynomial has at most $\deg(p)$ roots
3. The union over all heights gives a countable enumeration of all algebraic numbers

This differs from the abstract Mathlib approach (using `Finsupp` or abstract countability)
by giving an **explicit bijection** $\mathbb{N} \to \mathbb{A}$.

### Why This Matters

- **Historical significance**: This is Cantor's original 1874 argument, predating
  his diagonalization proof by a decade
- **Constructive value**: An explicit height-function enumeration is more concrete
  than abstract cardinality arguments
- **Gallery complement**: The existing `algebraic-numbers-countable` proof uses Mathlib's
  abstract machinery; a height-function proof would showcase the constructive approach

## Known Results

### What's Already Proven

- `algebraic-numbers-countable` (gallery) — algebraic numbers are countable via Mathlib
- Mathlib: `Polynomial.roots` is finite for nonzero polynomials over integral domains
- Mathlib: countable union of finite sets is countable (`Set.countable_iUnion`)

### What's Still Open

- Explicit height function defined as `H : Polynomial ℤ → ℕ` in Lean 4
- Finite bound: `{p : Polynomial ℤ | height p = k}.Finite` for each `k`
- Explicit enumeration assembling all roots by height

### Our Goal

Formalize the height function proof:
1. Define `height : Polynomial ℤ → ℕ`
2. Prove `{p : Polynomial ℤ | height p = k}.Finite` for each `k`
3. Prove algebraic numbers are countable via this height enumeration

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| algebraic-numbers-countable | Parent proof — abstract countability | Mathlib countability |
| nth-root-irrational | Algebraic number properties | Minimal polynomial |
| sqrt2-minpoly | ℤ[X] polynomial theory | Eisenstein, irrationality |

## Initial Thoughts

### Potential Approaches

1. **Direct height function**: Define `height (p : Polynomial ℤ) : ℕ` as
   `p.natDegree + (p.support.sum (fun i => (p.coeff i).natAbs))`.
   Prove finiteness by showing height bounds both degree and coefficients.
   - Why it might work: `Polynomial.support` is finite; bounded degree and
     bounded coefficients give only finitely many candidates at each height
   - Risk: Lean 4 `Polynomial` API uses `Finsupp` — support-based arguments
     require some care

2. **Pairing function approach**: Use a computable pairing `ℕ × ℕ → ℕ` to enumerate
   polynomials, then filter by height and extract roots.
   - Why it might work: Avoids custom height function
   - Risk: Less direct, doesn't follow Cantor's original argument

### Key Difficulties

- Height bounds degree: `height p = k → p.natDegree ≤ k`
- Height bounds coefficients: `height p = k → ∀ i, (p.coeff i).natAbs ≤ k`
- Combining these to prove `{p : Polynomial ℤ | height p = k}` is Fintype

### What Would a Proof Need?

- Key lemma 1: `height p = k → p.natDegree ≤ k`
- Key lemma 2: `height p = k → ∀ i, (p.coeff i).natAbs ≤ k`
- Key lemma 3: finitely many polynomials with bounded degree and bounded coefficients
- Key lemma 4: `Polynomial.roots` is finite (already in Mathlib)

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematics is elementary and well-understood
- Mathlib has `Polynomial.roots`, `Polynomial.natDegree`, coefficient access
- Main challenge: engineering the height finiteness proof using Finsupp structure
- Support-based arguments on `Polynomial ℤ` should work

**Estimated Effort**:
- Exploration: 1 day (check Mathlib polynomial API for finiteness tools)
- If tractable: 1 week (height function + 3-4 supporting lemmas)

## References

### Papers
- Cantor, G. (1874) — "Über eine Eigenschaft des Inbegriffes aller reellen algebraischen
  Zahlen" (Crelle's Journal — original countability proof)

### Mathlib
- `Mathlib.Data.Polynomial.Basic` — polynomial ring structure
- `Mathlib.Data.Polynomial.Degree.Definitions` — degree and support
- `Mathlib.RingTheory.AlgebraicIndependent` — algebraic numbers context

## Metadata

```yaml
tags:
  - set-theory
  - countability
  - algebraic-numbers
  - cardinality
  - field-theory
  - cantor
related_proofs:
  - algebraic-numbers-countable
  - nth-root-irrational
  - sqrt2-minpoly
difficulty: medium
source: gallery-gap
created: 2026-04-23T13:50:28+02:00
```

**Significance**: 7/10
**Tractability**: 7/10
