# Problem: Mersenne Prime Exponents Are Prime

**Slug**: mersenne-prime-exponent
**Created**: 2026-07-04
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\forall n \in \mathbb{N}, \qquad
\bigl(2^{n} - 1 \text{ is prime}\bigr) \;\Longrightarrow\; \bigl(n \text{ is prime}\bigr).
$$

The proof runs through the contrapositive and the geometric factorization: if $n = ab$ with
$1 < a < n$, then

$$
2^{a} - 1 \;\bigm|\; 2^{ab} - 1 \;=\; 2^{n} - 1,
\qquad\text{with}\quad 1 < 2^{a}-1 < 2^{n}-1,
$$

so $2^n - 1$ has a nontrivial divisor and is composite. In Lean:
`theorem mersenne_prime_exponent (n : ℕ) (h : Nat.Prime (2 ^ n - 1)) : Nat.Prime n`.

### Plain Language

A *Mersenne number* is one of the form $2^n - 1$: $3, 7, 15, 31, 63, 127, \dots$. Some are
prime (3, 7, 31, 127, ...) and some are not (15, 63, ...). This problem asks us to prove a
necessary condition on the exponent: whenever $2^n - 1$ is prime, the exponent $n$ must
itself be prime. (The converse fails — $2^{11}-1 = 2047 = 23 \times 89$ — so this is only
one direction.) The engine is the algebraic factorization $x^{ab} - 1 = (x^a - 1)\cdot(\ldots)$,
which forces a composite exponent to produce a composite Mersenne number.

### Why This Matters

This is the exponent-restriction half of the Euclid–Euler theory of even perfect numbers
and the classical prerequisite for the Lucas–Lehmer primality test (Mathlib's
`Mathlib.NumberTheory.LucasLehmer`, which tests `mersenne p` for *prime* `p`). It packages
the reusable "same-base power difference divisibility" lemma
$a - 1 \mid a^{k} - 1$ into a clean number-theory result and complements the gallery's
existing prime-structure entries (`infinitude-primes`, the Fermat-number family) with the
Mersenne side of the story.

## Known Results

### What's Already Proven

- `mersenne` is defined in Mathlib as `mersenne p = 2 ^ p - 1`
  (`Mathlib.NumberTheory.LucasLehmer`).
- Same-base power-difference divisibility: `nat_sub_dvd_pow_sub_pow`
  (`(a - b) ∣ a ^ n - b ^ n`), specializing to `(2^a - 1) ∣ (2^a)^b - 1 = 2^(ab) - 1`.
- `Nat.Prime` API: `Nat.prime_def_lt`, `Nat.Prime.eq_one_or_self_of_dvd`, and the
  decomposition of composites via `Nat.exists_dvd_of_not_prime`.

### What's Still Open (for this entry)

- A machine-checked statement and proof of `Nat.Prime (2^n - 1) → Nat.Prime n`.
- Optional: the explicit witness form — if `n = a*b` (`1 < a`, `1 < b`) then
  `2^a - 1` properly divides `2^n - 1`.

### Our Goal

Prove, axiom-free and `sorry`-free,
`theorem mersenne_prime_exponent (n : ℕ) (h : Nat.Prime (2 ^ n - 1)) : Nat.Prime n`,
building the supporting divisibility lemma `(2^a - 1) ∣ (2^(a*b) - 1)` and the strict
bounds `1 < 2^a - 1` and `2^a - 1 < 2^(a*b) - 1` for `1 < a`, `1 < b`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| infinitude-primes | shared `Nat.Prime` structural reasoning | prime divisibility |
| fermat-two-squares | sibling classical prime-structure result | number theory |
| binomial-theorem | `2^n` expansion / power identities backdrop | algebra of powers |

## Initial Thoughts

### Potential Approaches

1. **Contrapositive via factorization**: assume `n` composite, write `n = a*b` with
   `1 < a, b`, exhibit `2^a - 1` as a proper divisor of `2^n - 1`, contradict primality.
   - Why it might work: `nat_sub_dvd_pow_sub_pow` gives the divisibility immediately after
     rewriting `2^(a*b) = (2^a)^b`.
   - Risk: `Nat` subtraction bounds — must show `2^a - 1 ≠ 1` (needs `a ≥ 2`) and
     `2^a - 1 ≠ 2^n - 1` (proper divisor), both via monotonicity of `2^·`.

2. **`Nat.Prime.eq_one_or_self_of_dvd` on the divisor**: feed `2^a - 1 ∣ 2^n - 1` into the
   primality of `2^n - 1` and rule out both `=1` and `=2^n-1` by size.
   - Why it might work: reduces the whole argument to two inequalities.
   - Risk: same subtraction/monotonicity bookkeeping.

### Key Difficulties

- `Nat` truncated subtraction: carefully establish `1 < 2^a - 1` and the strict
  divisor inequality `2^a - 1 < 2^n - 1` (use `Nat.one_lt_two_pow` and
  `Nat.pow_lt_pow_right`).
- Extracting a factorization `n = a * b` with `1 < a`, `1 < b` from "`n` is not prime"
  (also handle `n = 0` and `n = 1`, where `2^n - 1 ∈ {0, 1}` is not prime).

### What Would a Proof Need?

- Key lemma: `(2^a - 1) ∣ (2^(a*b) - 1)` via `nat_sub_dvd_pow_sub_pow` + `pow_mul`.
- Key lemma: strict bounds `1 < 2^a - 1 < 2^(a*b) - 1` for `1 < a`, `1 < b`.
- `Nat.Prime.eq_one_or_self_of_dvd` (or `Nat.prime_def_lt`) to derive the contradiction.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- The core divisibility lemma exists in Mathlib (`nat_sub_dvd_pow_sub_pow`).
- The argument is a short, standard contrapositive; the only work is `Nat`-subtraction
  inequalities, which `omega` / monotonicity lemmas dispatch.
- Comparable in scope to solved elementary number-theory gallery entries.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1 day

## References

### Online Resources
- OEIS A000668 (Mersenne primes) and A000043 (exponents) — background.

### Mathlib
- `Mathlib.NumberTheory.LucasLehmer` — `mersenne` definition and primality-test context.
- `Mathlib.Algebra.GeomSum` — `nat_sub_dvd_pow_sub_pow` (power-difference divisibility).
- `Mathlib.Data.Nat.Prime.Basic` — `Nat.Prime` API (`eq_one_or_self_of_dvd`, `prime_def_lt`).

## Metadata

```yaml
tags:
  - number-theory
  - prime-numbers
  - divisibility
  - mersenne
related_proofs:
  - infinitude-primes
  - fermat-two-squares
  - binomial-theorem
difficulty: medium
source: gallery-gap
created: 2026-07-04
```

**Significance**: 5/10
**Tractability**: 7/10
