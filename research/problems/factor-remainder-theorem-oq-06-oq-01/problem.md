# Problem: A clean k-th-power irrationality criterion via the rational root theorem

**Slug**: factor-remainder-theorem-oq-06-oq-01
**Created**: 2026-07-02
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
\forall\, n \in \mathbb{Z},\ \forall\, k \in \mathbb{N}_{\ge 1},\quad
\big(\nexists\, m \in \mathbb{Z},\ m^k = n\big)\ \Longrightarrow\ \forall\, r \in \mathbb{Q},\ r^k \neq n .
$$

### Plain Language

The parent entry (`factor-remainder-theorem-oq-06`) applies the rational root theorem to
prove that `√2` is irrational — a single worked instance. The goal here is to generalize
that one-off application into a clean, reusable **criterion**: if an integer `n` is not a
perfect `k`-th power, then no rational number `r` satisfies `rᵏ = n`. Equivalently, the
real `k`-th root of a non-`k`-th-power integer is irrational.

### Why This Matters

This turns an ad hoc `√2` example into a general-purpose lemma covering `√3`, `∛2`, `⁴√5`,
etc., in one statement. It is exactly the kind of "promote the example to a theorem" step
that increases the gallery's reuse value, and it packages the rational-root-theorem
machinery behind a clean interface.

## Known Results

### What's Already Proven

- Parent `factor-remainder-theorem-oq-06`: rational root theorem applied to `x² - 2`.
- Mathlib `Polynomial.isIntegrallyClosed` / rational root machinery.
- Mathlib `Nat.Prime` factorization and `irrational_nrt_of_notint_nrt`,
  `irrational_sqrt_two`, `Nat.Prime.irrational_sqrt`.

### What's Still Open

- The general `n`, general `k` statement in a single reusable form.
- Bridging "not a perfect `k`-th power" (`∄ m, mᵏ = n`) to the polynomial `Xᵏ - n` having
  no rational root.

### Our Goal

State and prove the criterion above. Recover the parent's `√2` result and a `∛2` result as
corollaries, demonstrating the interface.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| factor-remainder-theorem-oq-06 | Direct parent; the `√2` special case | rational root theorem |
| nth-root-irrational-oq-02 | Sibling family on `k`-th root irrationality | prime factorization |

## Initial Thoughts

### Potential Approaches

1. **Via Mathlib `irrational_nrt_of_notint_nrt`**: it already states that an `n`-th root that
   is not an integer is irrational; reframe "not a perfect power" as the hypothesis.
   - Why it might work: the hard analytic content is already in Mathlib.
   - Risk: matching the exact hypothesis shape (integer-vs-natural, positivity).

2. **Rational root theorem on `Xᵏ - n`**: any rational root has denominator dividing the
   leading coefficient `1`, hence is an integer `m` with `mᵏ = n`, contradicting the
   not-a-perfect-power hypothesis.
   - Why it might work: mirrors the parent's method directly, so it composes.
   - Risk: care with `k = 0` and sign of `n`.

### Key Difficulties

- Handling edge cases `k = 0`, `k = 1`, and negative `n` cleanly in the statement.
- Choosing the canonical "not a perfect `k`-th power" predicate so it is ergonomic downstream.

### What Would a Proof Need?

- Key lemma 1: a rational root of a monic integer polynomial is an integer.
- Key lemma 2: `rᵏ = n` with `r ∈ ℚ` forces `r ∈ ℤ`, then contradicts non-power hypothesis.
- Technical requirements: monic rational root theorem, `Rat.den` divisibility.

## Tractability Assessment

**Difficulty**: Low-to-Medium

**Justification**:
- Mathlib already provides `irrational_nrt_of_notint_nrt` and rational-root infrastructure.
- The parent proves the `k = 2` case; this is a direct generalization.
- Main work is statement hygiene and corollary extraction.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–3 days

## References

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Pow.NNRat` / `Mathlib.RingTheory.Int.Basic` — root theory.
- `Mathlib.Data.Real.Irrational` — `irrational_nrt_of_notint_nrt`, `irrational_sqrt_two`.
- `Mathlib.RingTheory.Polynomial.RationalRoot` — rational root theorem.

## Metadata

```yaml
tags:
  - algebra
  - polynomials
  - number-theory
  - rational-root-theorem
related_proofs:
  - factor-remainder-theorem-oq-06
difficulty: medium
source: proof-suggestion
created: 2026-07-02
```

**Significance**: 6/10
**Tractability**: 6/10
