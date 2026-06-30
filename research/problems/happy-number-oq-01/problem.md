# Problem: Happy Numbers — Dichotomy of the Digit-Square Map

**Slug**: happy-number-oq-01
**Created**: 2026-06-16
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $S(n) = \sum_i d_i^2$ where $d_i$ are the decimal digits of $n$. Then for every
$n \ge 1$, the orbit $n, S(n), S^2(n), \dots$ eventually either reaches the fixed point
$1$ (in which case $n$ is *happy*) or enters the cycle

$$
4 \to 16 \to 37 \to 58 \to 89 \to 145 \to 42 \to 20 \to 4 .
$$

These are the only two terminal behaviors.

### Plain Language

Square each digit of a number and add the squares; repeat. Every starting number
eventually settles at 1 ("happy") or falls into a fixed loop of eight numbers starting
at 4 ("unhappy"). There is no third possibility.

### Why This Matters

A finite, decidable statement about the dynamics of a digit map: the key structural fact
is $S(n) < n$ for $n \ge 100$, which traps every orbit inside the finite set
$\{1, \dots, 99\}$ after finitely many steps, reducing an a-priori-infinite dynamical
claim to a finite case check. A tidy showcase of "eventual confinement + finite
enumeration" reasoning in Lean.

## Known Results

### What's Already Proven

- Classical folklore result; the eight-element unhappy cycle is well known and verified by enumeration.
- Bound $S(n) \le 81 \cdot (\text{number of digits})$ gives the contraction $S(n) < n$ for $n \ge 100$.

### What's Still Open

- Nothing mathematically open for base 10; density of happy numbers is studied but out of scope.
- Optional extension: behavior in other bases / for higher powers of digits.

### Our Goal

Formalize the base-10 dichotomy: define $S$, prove $S(n) < n$ for $n \ge 100$, conclude
every orbit reaches $\{1,\dots,99\}$, and finitely classify those into the fixed point 1
or the 8-cycle.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| niven-theorem-oq-01 | decimal-digit functions in Lean | `Nat.digits`, digit sums |
| kaprekar-constant-oq-01 | bounded-orbit digit dynamics | confinement + finite enumeration |

## Initial Thoughts

### Potential Approaches

1. **Contraction + finite enumeration**: prove $S(n) < n$ for $n \ge 100$, so orbits
   descend into $\{1,\dots,99\}$; then `decide` the dynamics on that finite set.
   - Why it might work: reduces the infinite claim to a bounded, decidable check.
   - Risk: the digit-square bound and the strong-induction descent need careful ℕ arithmetic.

2. **Direct invariant set**: identify the reachable set under $S$ and show it is finite and
   partitions into the two attractors.
   - Why it might work: avoids re-deriving the bound for each orbit.
   - Risk: more setup to characterize the reachable set explicitly.

### Key Difficulties

- Proving $S(n) < n$ for $n \ge 100$ from a digit-length bound on $S$.
- Strong induction / well-founded descent to guarantee entry into $\{1,\dots,99\}$.

### What Would a Proof Need?

- Key lemma 1: $S(n) \le 81 \cdot (\lfloor \log_{10} n\rfloor + 1)$, hence $S(n) < n$ for $n \ge 100$.
- Key lemma 2: classification of $S$ on $\{1,\dots,99\}$ (fixed point 1 vs. the 8-cycle) by `decide`.
- Technical requirements: `Nat.digits`, strong induction, `Finset`/`decide`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematics is elementary; the work is the digit bound plus a finite check.
- Strong-induction descent and the digit-length estimate are the main engineering.
- Mathlib provides `Nat.digits` and decidable enumeration.

**Estimated Effort**:
- Exploration: hours
- If tractable: days
- If hard: days (digit-bound bookkeeping)

## References

### Papers
- R. Honsberger, "Ingenuity in Mathematics", 1970 — popular account of happy numbers.

### Online Resources
- https://en.wikipedia.org/wiki/Happy_number — definition, the unhappy cycle, and the contraction bound.
- OEIS A007770 — happy numbers.

### Mathlib
- `Mathlib.Data.Nat.Digits` — decimal digit extraction for $S$.
- `Mathlib.Data.Finset.Basic` — finite classification on $\{1,\dots,99\}$.

## Metadata

```yaml
tags:
  - number-theory
  - digits
  - dynamics
  - happy-numbers
  - decidable
related_proofs:
  - niven-theorem-oq-01
  - kaprekar-constant-oq-01
difficulty: medium
source: gallery-gap
created: 2026-06-16
```
