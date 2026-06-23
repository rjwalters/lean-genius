# Problem: Sylvester's Sequence — Reciprocal Sum and Pairwise Coprimality

**Slug**: sylvester-sequence-oq-01
**Created**: 2026-06-16
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
a_0 = 2,\quad a_{n+1} = a_n^2 - a_n + 1,\qquad
\sum_{k=0}^{n-1} \frac{1}{a_k} = 1 - \frac{1}{a_n - 1},\qquad
\gcd(a_i, a_j) = 1\ \text{for } i \ne j.
$$

In particular $\sum_{k=0}^{\infty} 1/a_k = 1$, the fastest-converging Egyptian-fraction
representation of unity.

### Plain Language

Sylvester's sequence starts 2, 3, 7, 43, 1807, … where each term is one plus the product
of all previous terms. The reciprocals add up to exactly 1, and any two terms share no
common factor.

### Why This Matters

The sequence is the engine behind the greedy ("Sylvester–Fibonacci") algorithm for unit
fractions and underlies bounds on Egyptian-fraction representations and Znám's problem.
Both claims (the telescoping reciprocal identity and pairwise coprimality) are clean
inductions, making this an accessible but genuinely arithmetic formalization target.

## Known Results

### What's Already Proven

- Telescoping identity $1/a_n = 1/(a_n-1) - 1/(a_{n+1}-1)$ follows from $a_{n+1}-1 = a_n(a_n-1)$ (classical).
- Pairwise coprimality is standard: $a_{n+1} \equiv 1 \pmod{a_k}$ for all $k \le n$.

### What's Still Open

- Whether every term of Sylvester's sequence is squarefree is an open conjecture (NOT in scope here).
- Our scope is only the reciprocal-sum identity and pairwise coprimality, both fully provable.

### Our Goal

Define the sequence in Lean and prove (1) the closed form of the partial reciprocal sum
$\sum_{k<n} 1/a_k = 1 - 1/(a_n-1)$ over $\mathbb{Q}$, and (2) pairwise coprimality of the terms.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| niven-theorem-oq-01 | recurrence + arithmetic over ℕ/ℚ | induction on a recursively defined sequence |
| thue-morse-oq-01 | sequence defined by a simple recurrence | structural induction |

## Initial Thoughts

### Potential Approaches

1. **Direct induction on the telescoping identity**: prove $a_{n+1}-1 = a_n(a_n-1)$, then
   sum $1/a_k = 1/(a_k-1) - 1/(a_{k+1}-1)$ telescopes.
   - Why it might work: each step is a one-line algebraic rewrite over ℚ.
   - Risk: managing the ℕ→ℚ cast and the positivity $a_n \ge 2$ side conditions.

2. **Coprimality via the product invariant**: show $a_{n+1} = 1 + \prod_{k\le n} a_k$ and
   reduce mod $a_k$.
   - Why it might work: gives $a_{n+1} \equiv 1$, hence $\gcd(a_{n+1}, a_k)=1$, then induct.
   - Risk: proving the product form alongside the squared recurrence requires a joint induction.

### Key Difficulties

- Keeping ℕ subtraction ($a_n - 1$) well-behaved or working over ℚ/ℤ throughout.
- A clean monotonicity lemma $a_n \ge 2$ (and strictly increasing) to license the casts.

### What Would a Proof Need?

- Key lemma 1: $a_n \ge 2$ and $a_{n+1} - 1 = a_n (a_n - 1)$.
- Key lemma 2: $a_{n+1} = 1 + \prod_{k \le n} a_k$ (for coprimality).
- Technical requirements: induction, `Nat.Coprime`/`Int.gcd`, rational arithmetic.

## Tractability Assessment

**Difficulty**: Low-Medium

**Justification**:
- Both targets are elementary inductions with no deep dependencies.
- Main friction is cast discipline (ℕ vs ℚ) and the monotonicity bookkeeping.
- Mathlib has `Nat.Coprime`, `Finset.prod`, and rational arithmetic support.

**Estimated Effort**:
- Exploration: hours
- If tractable: days
- If hard: unlikely; worst case is cast/automation friction

## References

### Papers
- J. J. Sylvester, "On a point in the theory of vulgar fractions", Amer. J. Math., 1880.
- Curtiss, "On Kellogg's diophantine problem", Amer. Math. Monthly, 1922 — bounds via the sequence.

### Online Resources
- https://en.wikipedia.org/wiki/Sylvester%27s_sequence — overview and identities.
- OEIS A000058 — Sylvester's sequence.

### Mathlib
- `Mathlib.Data.Nat.GCD.Basic` — coprimality lemmas.
- `Mathlib.Algebra.BigOperators.Basic` — finite products/sums for the telescoping identity.

## Metadata

```yaml
tags:
  - number-theory
  - recurrence
  - egyptian-fractions
  - coprimality
  - sylvester
related_proofs:
  - niven-theorem-oq-01
  - thue-morse-oq-01
difficulty: medium
source: gallery-gap
created: 2026-06-16
```
