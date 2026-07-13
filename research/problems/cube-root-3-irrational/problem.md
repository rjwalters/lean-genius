# Problem: Irrationality of ∛3

**Slug**: cube-root-3-irrational
**Created**: 2025-12-30T16:02:07-08:00
**Status**: Graduated
**Source**: proof-suggestion (from cube-root-2-irrational)

## Problem Statement

### Formal Statement

$$
\sqrt[3]{3} \notin \mathbb{Q}
$$

Equivalently: there do not exist integers $p, q$ with $q \neq 0$ such that $\left(\frac{p}{q}\right)^3 = 3$.

### Plain Language

The cube root of 3 is irrational. This follows the same pattern as cube root of 2—the rational root theorem shows that x³ - 3 = 0 has no rational solutions.

### Why This Matters

1. **Generalization**: Demonstrates that the technique from ∛2 generalizes immediately
2. **Pattern recognition**: Same proof structure works for ∛n when n is not a perfect cube
3. **Mathlib practice**: Building familiarity with polynomial irreducibility proofs

## Known Results

### What's Already Proven

- **∛2 is irrational** — In our research (`cube-root-2-irrational`)
- **Rational Root Theorem** — Available in Mathlib
- **Eisenstein's Criterion** — x³ - 3 is irreducible over ℚ by Eisenstein with p=3

### What's Still Open (for us)

- Formalize ∛3 irrationality in Lean 4 (DONE)
- Connect to general n-th root theorem

### Our Goal

Prove in Lean 4 that `Irrational (3 : ℝ) ^ (1/3 : ℝ)` or equivalent formulation.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| sqrt2-irrational | Foundation technique | Contradiction, descent |
| cube-root-2-irrational | Direct analog | Rational root theorem |

## Initial Thoughts

### Potential Approaches

1. **Rational Root Theorem**: If p/q is a rational root of x³ - 3 = 0, then p divides 3 and q divides 1. Check candidates: ±1, ±3. None cube to 3.

2. **Prime Multiplicity**: If (p/q)³ = 3, then 3·v₃(p) - 3·v₃(q) = 1. But LHS is divisible by 3, RHS is 1. Contradiction.

3. **Eisenstein's Criterion**: x³ - 3 is irreducible over ℚ by Eisenstein with p=3.

### Key Difficulties

- Same as ∛2: parity argument fails
- Direct adaptation of cube-root-2 proof

## Tractability Assessment

**Difficulty**: Low
**Significance**: 3/10
**Tractability**: 9/10

**Justification**:
- Direct analog of completed ∛2 proof
- Same Mathlib machinery applies
- Minimal adaptation required

## References

### Mathlib
- `Mathlib.Data.Real.Irrational` — Irrational number definitions
- `Mathlib.RingTheory.Polynomial.RationalRoot` — Rational root theorem

## Metadata

```yaml
tags:
  - number-theory
  - irrationality
  - polynomial
  - algebraic-number-theory
related_proofs:
  - sqrt2-irrational
  - cube-root-2-irrational
difficulty: low
source: proof-suggestion
created: 2025-12-30T16:02:07-08:00
```
