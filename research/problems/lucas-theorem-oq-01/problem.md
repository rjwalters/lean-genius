# Problem: Lucas's Theorem — Binomial Coefficients Modulo a Prime

**Slug**: lucas-theorem-oq-01
**Created**: 2026-06-16
**Status**: Active
**Source**: seeker-selected <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\binom{m}{n} \equiv \prod_{i=0}^{k} \binom{m_i}{n_i} \pmod{p}
$$

where $p$ is prime and $m = \sum_i m_i p^i$, $n = \sum_i n_i p^i$ are the base-$p$
expansions of $m$ and $n$ (with $0 \le m_i, n_i < p$). A useful corollary: if any
digit satisfies $n_i > m_i$, then $\binom{m}{n} \equiv 0 \pmod{p}$.

### Plain Language

To reduce a binomial coefficient modulo a prime $p$, write both the top number $m$
and the bottom number $n$ in base $p$. Then $\binom{m}{n} \bmod p$ is just the
product of the digit-wise binomial coefficients. In particular the coefficient
vanishes mod $p$ exactly when some base-$p$ digit of $n$ exceeds the corresponding
digit of $m$.

### Why This Matters

Lucas's theorem (1878) is the foundational tool for understanding binomial
coefficients modulo a prime. It underlies Kummer's theorem on $p$-adic valuations of
binomial coefficients, the self-similar (Sierpiński) structure of Pascal's triangle
mod $p$, and many divisibility results in combinatorial number theory. It is a
standard named theorem with no current gallery entry, making it a clean,
self-contained formalization target.

## Known Results

### What's Already Proven

- The single-step recurrence $\binom{ap+b}{cp+d} \equiv \binom{a}{c}\binom{b}{d}
  \pmod p$ for $0 \le b,d < p$ is the inductive heart of the theorem.
- Mathlib provides `Nat.choose`, `Nat.Prime`, `ZMod p`, the Frobenius/freshman's-dream
  identity `add_pow_char` / `add_pow_prime_pow`, and `Nat.digits p` for base-$p$
  expansions.
- The generating-function proof works in `(ZMod p)[X]`: $(1+X)^m = \prod_i
  ((1+X)^{p^i})^{m_i} = \prod_i (1 + X^{p^i})^{m_i}$ using $(1+X)^{p^i} = 1 + X^{p^i}$
  in characteristic $p$, then comparing coefficients.

### What's Still Open

- No Lean formalization of the full digit-product statement exists in this gallery.
- The clean coefficient-extraction argument over `(ZMod p)[X]` has not been assembled
  here, nor the `Nat.digits`-indexed product form of the conclusion.

### Our Goal

Formalize the full theorem `Nat.choose m n` congruent to the digit-indexed product in
`ZMod p` for prime `p`, stated with `Nat.digits p m` and `Nat.digits p n`, together
with the divisibility corollary. Prove it by the generating-function/`add_pow_char`
route in `(ZMod p)[X]`, which avoids delicate digit bookkeeping in the induction.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| wolstenholme-theorem | Congruences on binomial coefficients modulo a prime power | `ZMod`, harmonic sums, prime arithmetic |
| fermat-two-squares | Prime-indexed number theory with characteristic-$p$ arguments | `ZMod p`, quadratic residues |
| frobenius-number | Base-representation / digit reasoning over the naturals | `Nat.digits`, induction on representation |

## Initial Thoughts

### Potential Approaches

1. **Generating functions over `(ZMod p)[X]`**: expand $(1+X)^m$ using
   $(1+X)^{p^i} = 1 + X^{p^i}$ (freshman's dream, `add_pow_char`), regroup by
   base-$p$ digits, then read off the coefficient of $X^n$.
   - Why it might work: Mathlib already has `add_pow_char` and polynomial coefficient
     lemmas; the algebra is clean and avoids carries.
   - Risk: bookkeeping to translate `Polynomial.coeff` of a product into the
     digit-indexed product of `Nat.choose`.

2. **Single-digit recurrence plus strong induction on `m`**: prove $\binom{ap+b}{cp+d}
   \equiv \binom{a}{c}\binom{b}{d}$ directly, then induct.
   - Why it might work: each step is elementary.
   - Risk: managing the $n_i > m_i$ vanishing case and the `Nat.digits` recursion
     cleanly in Lean.

### Key Difficulties

- Aligning `Nat.digits p m` and `Nat.digits p n` when they have different lengths
  (pad the shorter with zero digits; $\binom{0}{k+1} = 0$ gives the vanishing).
- Converting between `Polynomial.coeff` of a finite product and a `Finset.prod` of
  binomial coefficients indexed by digit position.

### What Would a Proof Need?

- Key lemma 1: $(1+X)^{p^i} = 1 + X^{p^i}$ in `(ZMod p)[X]` (from `add_pow_char`).
- Key lemma 2: coefficient of $X^n$ in $\prod_i (1 + X^{p^i})^{m_i}$ equals
  $\prod_i \binom{m_i}{n_i}$, where $n_i$ are the base-$p$ digits of $n$ (uniqueness of
  base-$p$ representation drives the selection).
- Technical requirements: `Nat.digits`, `Polynomial.coeff_prod`, `add_pow_char`,
  `ZMod.natCast_self_eq_zero`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Standard textbook theorem with a well-understood Lean-friendly proof route.
- All core ingredients (`ZMod p`, `add_pow_char`, `Nat.digits`, polynomial
  coefficients) already exist in Mathlib.
- Comparable congruence results (Wolstenholme, Fermat two-squares) are already in the
  gallery, so the techniques are proven to land here.

**Estimated Effort**:
- Exploration: 1 day
- If tractable: 3 to 5 days
- If hard: 1 to 2 weeks (if the coefficient-extraction lemma proves fiddly)

## References

### Papers
- E. Lucas, "Théorie des fonctions numériques simplement périodiques", 1878 — original.
- N. J. Fine, "Binomial coefficients modulo a prime", Amer. Math. Monthly, 1947 —
  the clean generating-function proof.

### Online Resources
- Andrew Granville, "Binomial coefficients modulo prime powers" — survey including
  Lucas and Kummer.

### Mathlib
- `Mathlib.FieldTheory.Finite.Basic` / `add_pow_char` — freshman's dream in char $p$.
- `Mathlib.Data.Nat.Digits` — base-$p$ expansions.
- `Mathlib.Data.Polynomial.Coeff` — coefficient extraction from products.
- `Mathlib.Data.ZMod.Basic` — arithmetic modulo a prime.

## Metadata

```yaml
tags:
  - number-theory
  - combinatorics
  - prime
  - binomial-coefficients
related_proofs:
  - wolstenholme-theorem
  - fermat-two-squares
difficulty: medium
source: seeker-selected
created: 2026-06-16
```
