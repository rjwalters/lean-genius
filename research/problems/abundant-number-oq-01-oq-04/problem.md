# Problem: Primitive abundant numbers — definition, smallest witness (20), and infinitude

**Slug**: abundant-number-oq-01-oq-04
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{IsPrimitiveAbundant}(n) \;:\Longleftrightarrow\; \sigma(n) > 2n \;\wedge\; \forall\, d \mid n,\ d < n \Rightarrow \sigma(d) < 2d,
$$
$$
\text{IsLeast}\,\{\,n : \text{IsPrimitiveAbundant}(n)\,\}\ 20, \qquad \{\,n : \text{IsPrimitiveAbundant}(n)\,\}\ \text{is infinite.}
$$

### Plain Language

A *primitive abundant number* is an abundant number (sum of proper divisors exceeds the number) **all of whose proper divisors are deficient** (each has proper-divisor sum strictly below itself). The smallest is 20: its proper divisors 1, 2, 4, 5, 10 are each deficient, while 20 itself is abundant. These are exactly the abundant numbers the parent's closure theorem cannot manufacture from a smaller abundant witness — if some proper divisor were already abundant, closure would make `n` abundant, so primitivity is precisely the failure of any proper divisor to be abundant.

### Why This Matters

The parent proof (`abundant-number-oq-01`) shows 12 is the smallest abundant number and that abundant numbers are infinite, partly via a closure argument (a multiple of an abundant number is abundant). Primitive abundant numbers are the *generators* of that closure: every abundant number is a multiple of a primitive abundant number. Formalizing them isolates the irreducible core of abundance and sets up Erdős's 1935 theorem that they are infinite yet sparse (their reciprocal sum converges).

## Known Results

### What's Already Proven

- Parent `abundant-number-oq-01`: 12 is the least abundant number; there are infinitely many abundant numbers (closure under multiples).
- Mathlib: `Nat.sigma`, `Nat.Perfect`/`Nat.sigma_one_eq_sigmaOne`, `Nat.divisors`, `Nat.sum_divisors_*`, decidability of `n ∣ m` and finite divisor sums (`Decidable`, `decide`).

### What's Still Open

- A clean Lean definition `IsPrimitiveAbundant` and the `IsLeast … 20` characterization.
- Infinitude of primitive abundant numbers.
- (Stretch, Erdős 1935) convergence of the sum of reciprocals of primitive abundant numbers — a genuinely analytic result, out of scope for the first pass.

### Our Goal

Define `IsPrimitiveAbundant`, prove `IsLeast {n | IsPrimitiveAbundant n} 20` by `decide`/explicit divisor computation for the lower bound plus a witness check, and prove the set is infinite (e.g. exhibit an infinite family such as `2·p` for odd primes `p`, or `2^k · p` patterns, each primitive abundant for suitable parameters).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `abundant-number-oq-01` | parent: 12 smallest abundant, infinitude via closure | `Nat.sigma`, decidability, closure under multiples |
| `abundant-number` | base abundant-number entry | divisor sums |

## Initial Thoughts

### Potential Approaches

1. **Decide the smallest witness**: `IsLeast` splits into membership (`IsPrimitiveAbundant 20`, a finite divisor computation closable by `decide`) and the lower bound (`∀ m < 20, ¬ IsPrimitiveAbundant m`, an `interval_cases`/`decide` sweep).
   - Why it might work: everything below 20 is a finite check; Mathlib's `Nat.sigma` is computable.
   - Risk: `decide` performance on `Nat.sigma` for the membership of each `m < 20` — should be trivial at this scale.

2. **Infinite family**: identify a parametric family of primitive abundant numbers (Erdős used `2p` for primes `p` in a range, and more general `2^a m` constructions). Prove the predicate for the family and inject `ℕ ↪ {n | IsPrimitiveAbundant n}`.
   - Why it might work: primitivity for a 2-times-odd-prime form reduces to checking the few divisors symbolically.
   - Risk: choosing a family whose primitivity has a clean uniform proof.

### Key Difficulties

- Pinning a parametric infinite family whose primitivity is provable without case explosion.
- Avoiding `native_decide` to keep the entry 0-axiom (kernel `decide` only).

### What Would a Proof Need?

- Key lemma 1: `IsPrimitiveAbundant 20` (witness, finite check).
- Key lemma 2: lower bound `∀ m < 20, ¬ IsPrimitiveAbundant m`.
- Key lemma 3: an injective infinite family into the predicate.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Definition and smallest-witness are concrete finite computations (kernel `decide`).
- Parent is verified and 0-axiom; its `Nat.sigma` machinery is reusable.
- The reciprocal-convergence (Erdős) part is hard and explicitly deferred.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–3 days for definition + smallest + an infinite family
- If hard: the analytic sparsity (reciprocal sum) is open-ended

## References

### Papers
- P. Erdős, "On the density of the abundant numbers", J. London Math. Soc. (1935) — primitive abundant numbers are infinite, reciprocal sum converges.

### Online Resources
- OEIS A091191 (primitive abundant numbers); A071395 (primitive abundant of a related flavor).

### Mathlib
- `Mathlib/NumberTheory/Divisors.lean` — `Nat.divisors`, divisor sums.
- `Mathlib/NumberTheory/ArithmeticFunction.lean` — `Nat.ArithmeticFunction.sigma`.

## Metadata

```yaml
tags:
  - number-theory
  - divisor-sum
  - abundant-numbers
  - decidability
  - infinitude
related_proofs:
  - abundant-number-oq-01
  - abundant-number
difficulty: medium
source: gallery-gap
created: 2026-06-24
```
