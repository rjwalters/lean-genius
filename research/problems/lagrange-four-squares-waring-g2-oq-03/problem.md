# Problem: Legendre's Three-Square Theorem — the "if" Direction

**Slug**: lagrange-four-squares-waring-g2-oq-03
**Created**: 2026-06-14
**Status**: Active (OBSERVE)
**Source**: gallery-gap (parent: `lagrange-four-squares-waring-g2`)

## Problem Statement

### Formal Statement

A natural number $n$ is a sum of three squares iff it is **not** of the form $4^a(8b+7)$:

$$
n = x^2+y^2+z^2 \ \text{has a solution} \iff n \neq 4^a(8b+7)\ \text{for all } a,b\ge 0.
$$

The parent gallery proof establishes Waring's $g(2)=4$ (every $n$ is a sum of four squares) and
the **"only if"** direction of the three-square exclusion: if $n = 4^a(8b+7)$ then $n$ is not a
sum of three squares (an elementary $\bmod 8$ / descent argument). The open piece is the
**"if"** direction: every $n$ **not** of that form *is* a sum of three squares.

### Plain Language

It is easy to show numbers like $7, 15, 23, 28, \dots$ (the $4^a(8b+7)$ family) can never be
written as $x^2+y^2+z^2$ — just reduce mod 8 and peel off factors of 4. The hard, still-unformalized
half is the converse: that *every other* number can be so written. Classically this follows from
the theory of ternary quadratic forms / Gauss's theorem on sums of three squares.

### Why This Matters

Three squares is the genuinely hard case between two squares (Fermat, fully in Mathlib) and four
squares (Lagrange, in Mathlib). The exclusion set $4^a(8b+7)$ is exactly why $g(2)=4$ rather than
$3$. Completing the "if" direction closes the characterization and gives the gallery a full,
self-contained account of sums of three squares — a long-standing gap because the converse needs
more than congruences.

## Known Results

### What's Already Proven

- `lagrange-four-squares-waring-g2` — Lagrange four-square theorem and $g(2)=4$ (parent).
- "Only if" direction: $4^a(8b+7)$ is not a sum of three squares (congruence + descent), already in the parent file.
- Mathlib: `Nat.sum_four_squares` (Lagrange), `ZMod` congruence tooling, `Nat.factorization`.

### What's Still Open

- The "if" direction (Gauss / Davenport–Cassels): $n \neq 4^a(8b+7) \Rightarrow n = x^2+y^2+z^2$.
- A Mathlib-level theory of ternary forms or the Davenport–Cassels lemma to support it.

### Our Goal

Formalize the "if" direction. The most tractable route is the **Davenport–Cassels** approach:
prove that if a positive-definite ternary form represents $n$ rationally then it represents $n$
integrally, then exhibit a rational representation for every admissible $n$. Target: a Lean
theorem `n ≠ 4^a(8b+7) → ∃ x y z, n = x^2+y^2+z^2`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| lagrange-four-squares-waring-g2 | Direct parent; supplies four-square + "only if" | descent, congruences, Lagrange |
| sum-of-two-squares / fermat-christmas | Two-square characterization analogue | Gaussian integers, congruences |
| zsqrtd-neg-two | Binary-form representation by norms | quadratic ring norms |

## Initial Thoughts

### Potential Approaches

1. **Davenport–Cassels lemma (recommended)**: rational $\Rightarrow$ integral representability for
   $x^2+y^2+z^2$, then reduce $n$ to a residue with a rational solution via Dirichlet on primes in
   an arithmetic progression.
   - Why it might work: it is the standard "elementary" modern proof; the descent lemma is finite and explicit.
   - Risk: the "there exists a prime $\equiv$ ..." input may pull in Dirichlet's theorem (heavy in Lean).

2. **Gauss / class-number route**: count representations via the class number of binary forms of the relevant discriminant.
   - Why it might work: conceptually complete.
   - Risk: requires substantial form/class-group infrastructure not yet in Mathlib.

### Key Difficulties

- The converse inherently needs an existence input (a prime or a rational point), unlike the purely congruential "only if".
- Davenport–Cassels needs careful handling of the "nearest lattice point" rounding step in Lean.

### What Would a Proof Need?

- Key lemma 1: Davenport–Cassels (rational ⇒ integral) for the sum-of-three-squares form.
- Key lemma 2: existence of a prime in a suitable residue class (or an explicit ternary rational solution).
- Technical requirements: `ZMod`, `Nat.factorization`, rational arithmetic, possibly `Nat.Prime` existence lemmas.

## Tractability Assessment

**Difficulty**: Medium–High

**Justification**:
- "Only if" is done; the converse is the classically hard half.
- Davenport–Cassels is elementary but fiddly; the prime-existence input is the main risk to tractability.
- A partial result (assuming the prime-existence lemma as a hypothesis) is a realistic intermediate milestone.

**Estimated Effort**:
- Exploration: days
- If tractable: 2–4 weeks
- If hard: unknown (if full Dirichlet input is unavoidable)

## References

### Papers
- Davenport & Cassels (1955), short proof of the three-square theorem.
- Gauss, *Disquisitiones Arithmeticae* (1801), Art. 291 — sums of three squares.
- Serre, *A Course in Arithmetic*, Ch. IV — three squares via Hasse–Minkowski / Davenport–Cassels.

### Online Resources
- Parent gallery entry `lagrange-four-squares-waring-g2`.

### Mathlib
- `Mathlib.NumberTheory.SumFourSquares` — Lagrange, the four-square baseline.
- `Mathlib.NumberTheory.LegendreSymbol` and `ZMod` — congruence inputs.

## Metadata

```yaml
tags:
  - number-theory
  - sums-of-squares
  - quadratic-forms
  - davenport-cassels
related_proofs:
  - lagrange-four-squares-waring-g2
  - zsqrtd-neg-two
difficulty: high
source: proof-suggestion
created: 2026-06-14
```
