# Problem: Sum of First n Cubes Closed Form (Nicomachus's Theorem)

**Slug**: sum-of-cubes
**Created**: 2026-01-26T18:01:08-08:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\sum_{k=1}^{n} k^3 = \left(\frac{n(n+1)}{2}\right)^2
$$

Equivalently: the sum of the first n cubes equals the square of the n-th triangular number.

### Plain Language

The sum 1^3 + 2^3 + 3^3 + ... + n^3 equals (1 + 2 + 3 + ... + n)^2. This is Nicomachus's theorem, known since antiquity.

### Why This Matters

- Elegant identity connecting cubes to triangular numbers
- Foundation for Faulhaber's formulas (sums of higher powers)
- Natural extension of our existing arithmetic series proof
- Well-suited for inductive proof in Lean 4

## Known Results

### What's Already Proven

- ArithmeticSeries.lean proves the sum of first n integers: n(n+1)/2
- Mathlib has `Finset.sum` and `Finset.range` infrastructure
- The identity is classical and has multiple proof techniques

### What's Still Open

- Not yet formalized in our gallery
- Extension to Faulhaber's general formula for sum of k-th powers

### Our Goal

Prove Nicomachus's theorem in Lean 4: for all n, sum of k^3 for k in 1..n equals (n(n+1)/2)^2. Add to the proof gallery as a natural extension of arithmetic series.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| arithmetic-series | Direct parent - proves sum of first n integers | Induction, Finset.sum |
| binomial-theorem | Related identity with powers | Polynomial manipulation |
| combinations-formula | Binomial coefficient identities | Finset, Nat arithmetic |

## Initial Thoughts

### Potential Approaches

1. **Induction on n**: Standard proof. Show base case and inductive step.
   - Why it might work: Direct, standard approach. Lean's `induction` tactic handles this.
   - Risk: Arithmetic simplification may need `ring` or `omega` tactics.

2. **Telescoping / algebraic identity**: Use (k+1)^4 - k^4 = 4k^3 + 6k^2 + 4k + 1, then telescope.
   - Why it might work: Avoids referencing the sum of squares formula.
   - Risk: More complex algebraic manipulation.

3. **Via Finset.sum and ring lemma**: Define as Finset.sum, use Mathlib's ring tactic.
   - Why it might work: Mathlib's `ring` tactic is powerful for polynomial identities.
   - Risk: May need careful setup of the Finset.sum expression.

### Key Difficulties

- Ensuring clean division by 4 (or using 4 * sum = (n(n+1))^2 to avoid fractions)
- Connecting Finset.sum over range to the closed-form expression
- May need sum of squares (1^2 + ... + n^2 = n(n+1)(2n+1)/6) as auxiliary lemma

### What Would a Proof Need?

- Key lemma 1: Base case sum_cubes 0 = 0
- Key lemma 2: Inductive step: sum_cubes (n+1) = sum_cubes n + (n+1)^3
- Key lemma 3: Algebraic identity (n(n+1)/2)^2 + (n+1)^3 = ((n+1)(n+2)/2)^2
- Technical requirements: Nat or Int arithmetic, possibly `ring` or `omega`

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- Classical identity with well-known inductive proof
- Mathlib has all required infrastructure (Finset.sum, Nat arithmetic, ring tactic)
- ArithmeticSeries.lean provides a template for the proof structure
- No deep mathematical machinery required

## References

### Papers
- Nicomachus of Gerasa, "Introduction to Arithmetic" (~100 CE) -- original statement
- Faulhaber, "Academia Algebrae" (1631) -- generalization to higher powers

### Online Resources
- https://en.wikipedia.org/wiki/Squared_triangular_number -- Nicomachus's theorem
- https://proofwiki.org/wiki/Sum_of_Sequence_of_Cubes -- multiple proof approaches

### Mathlib
- `Mathlib.Algebra.BigOperators.Group.Finset` -- Finset.sum
- `Mathlib.Data.Nat.Basic` -- natural number arithmetic
- `Mathlib.Tactic.Ring` -- ring tactic for polynomial identities

## Metadata

```yaml
tags:
  - number-theory
  - algebra
  - series
  - extension
related_proofs:
  - arithmetic-series
  - binomial-theorem
  - combinations-formula
difficulty: low
source: gallery-gap
created: 2026-01-26T18:01:08-08:00
```
