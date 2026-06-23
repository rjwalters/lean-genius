# Problem: Failure of Unique Factorization in Z[sqrt(-5)]

**Slug**: fundamental-arithmetic-oq-02
**Created**: 2026-03-30
**Status**: Active
**Source**: gallery-extension (from fundamental-arithmetic openQuestion #2)

## Problem Statement

### Formal Statement

In $\mathbb{Z}[\sqrt{-5}]$, the element $6$ has two essentially distinct factorizations:
$$
6 = 2 \cdot 3 = (1 + \sqrt{-5})(1 - \sqrt{-5})
$$
where $2$, $3$, $1 + \sqrt{-5}$, and $1 - \sqrt{-5}$ are all irreducible but not prime.

### Plain Language

The integers have unique factorization (the Fundamental Theorem of Arithmetic). But in some larger number rings, this fails. In $\mathbb{Z}[\sqrt{-5}]$, the number 6 can be factored in two genuinely different ways into irreducible elements, providing a concrete counterexample to unique factorization.

### Why This Matters

- Classic motivating example for algebraic number theory and ideal theory
- Kummer's observation of UFD failure led to the invention of ideal numbers (later ideals)
- Connects to class numbers: $\mathbb{Z}[\sqrt{-5}]$ has class number 2
- Foundation for understanding when UFDs exist among rings of integers

## Known Results

### What's Already Proven

- `fundamental-arithmetic` gallery proof: FTA for $\mathbb{Z}$ -- fully verified, Mathlib-backed
- Mathlib has `GaussianInt` (ring of Gaussian integers $\mathbb{Z}[i]$, which IS a UFD)
- Mathlib has `NumberField`, `RingOfIntegers`, `IsDedekindDomain`

### What's Still Open

- Formalizing $\mathbb{Z}[\sqrt{-5}]$ as a concrete ring
- Proving 2, 3, $1 \pm \sqrt{-5}$ are irreducible
- Proving these give distinct factorizations of 6
- Proving $\mathbb{Z}[\sqrt{-5}]$ is NOT a UFD

### Our Goal

Formalize the failure of unique factorization in $\mathbb{Z}[\sqrt{-5}]$ by exhibiting two distinct irreducible factorizations of 6.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| fundamental-arithmetic | Parent proof, FTA for integers | Mathlib UniqueFactorizationDomain |
| sqrt2-irrational | Working with algebraic irrationals | Norm arguments |

## Initial Thoughts

### Potential Approaches

1. **Norm-based approach**: Define $N(a + b\sqrt{-5}) = a^2 + 5b^2$ and use it to prove irreducibility
   - Why it might work: Standard approach, norms are multiplicative
   - Risk: Need to set up the ring and norm from scratch if not in Mathlib

2. **Mathlib NumberField approach**: Use `NumberField` infrastructure
   - Why it might work: Mathlib may already have quadratic integer rings
   - Risk: Possibly heavy-weight for a concrete example

### Key Difficulties

- Defining $\mathbb{Z}[\sqrt{-5}]$ concretely in Lean 4
- Proving irreducibility of 2 in this ring (norm argument: $N(2) = 4$, no element of norm 2)

### What Would a Proof Need?

- Definition of $\mathbb{Z}[\sqrt{-5}]$ as a subring of $\mathbb{C}$ or an abstract ring
- Multiplicative norm function $N: \mathbb{Z}[\sqrt{-5}] \to \mathbb{N}$
- Irreducibility proofs for 2, 3, $1 + \sqrt{-5}$, $1 - \sqrt{-5}$
- Proof that the two factorizations of 6 are distinct (no unit multiple relation)

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Well-understood mathematically with a clear proof strategy
- Norm arguments are elementary
- Mathlib may have quadratic ring infrastructure to leverage

## References

### Mathlib
- `Mathlib.RingTheory.UniqueFactorizationDomain` -- UFD definition
- `Mathlib.NumberTheory.NumberField.Basic` -- NumberField infrastructure
- `Mathlib.RingTheory.DedekindDomain.Ideal` -- Dedekind domains

## Metadata

```yaml
tags:
  - algebraic-number-theory
  - ring-theory
  - counterexample
related_proofs:
  - fundamental-arithmetic
  - sqrt2-irrational
difficulty: medium
source: gallery-extension
created: 2026-03-30
```
