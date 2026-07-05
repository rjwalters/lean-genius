# Problem: Faulhaber's Fifth-Power Sum

**Slug**: nicomachus-sum-of-cubes-oq-04
**Created**: 2026-07-04
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Prove the Faulhaber closed form for the sum of the first $n$ fifth powers:

$$
\sum_{k=1}^{n} k^5 \;=\; \frac{n^2 (n+1)^2 \,(2n^2 + 2n - 1)}{12}.
$$

Equivalently, over $\mathbb{N}$ (clearing the denominator so no division is needed):

$$
12 \sum_{k=1}^{n} k^5 \;=\; n^2 (n+1)^2 (2n^2 + 2n - 1).
$$

The identity should be established axiom-free by induction on $n$, matching the style of
the sibling power-sum entries already in the gallery.

### Plain Language

Add up $1^5 + 2^5 + 3^5 + \dots + n^5$. Just like the sum of squares and the sum of cubes
have neat closed formulas, the sum of fifth powers does too: it equals
$\tfrac{1}{12}n^2(n+1)^2(2n^2+2n-1)$. Notice the factor $n^2(n+1)^2 = (2\sum k)^2$, so the
fifth-power sum is a multiple of the *square* of the triangular number — a cousin of
Nicomachus's theorem $\sum k^3 = (\sum k)^2$.

### Why This Matters

This completes the "small Faulhaber" family in the gallery. The parent entry
`nicomachus-sum-of-cubes-oq-01` proves $\sum k^3 = (\sum k)^2$, `oq-02` proves the
fourth-power sum, and `oq-03` proves $\sum(2k-1)^3 = n^2(2n^2-1)$. The fifth-power sum is
the next natural rung, and it exhibits the recurring $n^2(n+1)^2$ divisibility structure
(a square-of-triangular factor) that distinguishes odd-exponent Faulhaber polynomials from
even-exponent ones. Having $\sum k^p$ for $p \le 5$ machine-checked gives a clean, reusable
base for Faulhaber/Bernoulli-number formalizations.

## Known Results

### What's Already Proven

- $\sum k = n(n+1)/2$, $\sum k^2 = n(n+1)(2n+1)/6$, $\sum k^3 = (n(n+1)/2)^2$ — classical,
  and the cube case is `nicomachus-sum-of-cubes-oq-01`.
- $\sum k^4 = n(n+1)(2n+1)(3n^2+3n-1)/30$ — `nicomachus-sum-of-cubes-oq-02`.
- $\sum (2k-1)^3 = n^2(2n^2-1)$ — `nicomachus-sum-of-cubes-oq-03`.

### What's Still Open (for this entry)

- A formalized closed form for $\sum_{k=1}^n k^5$ (this entry).

### Our Goal

Formalize $12\sum_{k=1}^n k^5 = n^2(n+1)^2(2n^2+2n-1)$ over $\mathbb{N}$ (or the rational
identity with the $/12$), axiom-free, by induction. Base case $n=0$ (empty sum $=0$) or
$n=1$ ($1 = 1\cdot4\cdot3/12$). Inductive step reduces to the polynomial identity
$12(n+1)^5 = (n+1)^2(n+2)^2(2(n+1)^2+2(n+1)-1) - n^2(n+1)^2(2n^2+2n-1)$, dischargeable by
`ring`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| nicomachus-sum-of-cubes-oq-01 | parent: $\sum k^3 = (\sum k)^2$ | induction, `ring` |
| nicomachus-sum-of-cubes-oq-02 | sibling: fourth-power sum | induction, `ring` |
| nicomachus-sum-of-cubes-oq-03 | sibling: odd-cube sum | induction, `ring` |
| arithmetic-series / geometric-series | ambient finite-sum machinery | `Finset.sum`, induction |

## Initial Thoughts

### Potential Approaches

1. **Direct induction with `ring`**: state `12 * ∑_{k∈range(n+1)} k^5 = n^2(n+1)^2(2n^2+2n-1)`
   over `ℕ`, induct on `n`, and let `Finset.sum_range_succ` + `ring` close the step.
   - Why it might work: identical shape to the already-formalized sibling entries.
   - Risk: `ℕ` subtraction if the polynomial is stated with a bare `2n^2+2n-1`; keep the
     `-1` inside a form that stays non-negative, or work over `ℤ`/`ℚ` and cast.

2. **Rational statement**: prove `∑ k^5 = n^2*(n+1)^2*(2n^2+2n-1)/12` in `ℚ`, avoiding all
   `ℕ`-subtraction pitfalls; `field_simp; ring` on the step.
   - Why it might work: cleanest algebra; matches how oq-02's `/30` form is handled.

### Key Difficulties

- Avoiding `ℕ` truncated subtraction in `2n^2 + 2n - 1` (for `n ≥ 1` it is positive, but
  the cleanest fix is to prove the `×12` integer identity or the `ℚ` identity).
- Nothing analytically hard — this is a polynomial identity per induction step.

### What Would a Proof Need?

- `Finset.sum_range_succ` to peel the top term.
- `ring` (over `ℤ` or `ℚ`) for the polynomial step identity.
- A cast lemma if the public statement is over `ℚ` but the induction runs over `ℤ`.

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- Structurally identical to three sibling entries already machine-checked in the gallery.
- Single polynomial identity per step; `ring` handles it.

**Estimated Effort**:
- Exploration: minutes–hours
- If tractable: <1 day

## References

### Mathlib
- `Mathlib.Algebra.BigOperators.Basic` — `Finset.sum_range_succ`.
- `Mathlib.Tactic.Ring` — polynomial identity discharge.
- `Mathlib.Data.Nat.Cast` / `Mathlib.Data.Rat` — casting for the rational form.

### Online Resources
- Faulhaber's formula (Wikipedia) — fifth-power case and Bernoulli-number derivation.
- OEIS A000539 (sum of fifth powers).

## Metadata

```yaml
tags:
  - number-theory
  - power-sums
  - faulhaber
  - induction
  - closed-form
related_proofs:
  - nicomachus-sum-of-cubes-oq-01
  - nicomachus-sum-of-cubes-oq-02
  - nicomachus-sum-of-cubes-oq-03
difficulty: low
source: gallery-gap
created: 2026-07-04
```

**Significance**: 5/10
**Tractability**: 8/10
