# Problem: Chebyshev Mixed Product U_m · T_n Linearization

**Slug**: de-moivre-oq-02-oq-02-oq-01-oq-02
**Created**: 2026-07-04T06:28:11-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For every commutative ring $R$, $m : \mathbb{Z}$ and $n : \mathbb{N}$, prove the mixed
product-to-sum (linearization) identity in $R[X]$:

$$
U_m \cdot T_n = \tfrac{1}{2}\left(U_{m+n} + U_{m-n}\right)
$$

where $T_k$ (resp. $U_k$) is the first-kind (resp. second-kind) Chebyshev polynomial.
Because of the factor $\tfrac12$, the clean ring-theoretic form to formalize is the
scaled identity avoiding division:

$$
2\,U_m \cdot T_n = U_{m+n} + U_{m-n} \quad \text{in } R[X].
$$

### Plain Language

The parent entry established the pure second-kind linearization
$U_m \cdot U_n = \sum_{k=0}^{n} U_{m+n-2k}$. This problem asks for the *mixed* product
of a second-kind $U_m$ with a first-kind $T_n$: it should collapse to just **two**
second-kind terms, $U_{m+n} + U_{m-n}$ (up to the factor 2), mirroring the trig identity
$2\sin((m+1)\theta)\cos(n\theta) = \sin((m+n+1)\theta) + \sin((m-n+1)\theta)$.

### Why This Matters

Completing the mixed product $U \cdot T$ finishes the Chebyshev product table:
$T\cdot T$, $T\cdot U$, $U\cdot U$ are already formalized in the gallery, and this is
the remaining $U\cdot T$ cell. Together they express that the $\mathbb{Z}$-span of the
Chebyshev families is closed under multiplication with explicit structure constants — a
complete, machine-checked multiplication table for a classical polynomial family over an
arbitrary commutative ring.

## Known Results

### What's Already Proven

- **Parent entry `de-moivre-oq-02-oq-02-oq-01`**: $U_m \cdot U_n = \sum_{k=0}^{n} U_{m+n-2k}$ over any CommRing, via a product-free sum recurrence + two-step induction.
- **Grandparent `de-moivre-oq-02-oq-02`**: the mixed $2\,T_m U_n = U_{m+n} + U_{n-m}$ and the $(1-x^2)$-scaled $U\cdot U$ product-to-difference.
- **Ancestor `de-moivre-oq-02`**: first-kind $2\,T_m T_n = T_{m+n} + T_{m-n}$.
- Mathlib `Polynomial.Chebyshev`: recurrences `T_add_two`, `U_add_two`, the mixed
  relations `T_mul_U`-style lemmas, and `U`/`T` at negative $\mathbb{Z}$ indices.

### What's Still Open

- The bare $U_m \cdot T_n = \tfrac12(U_{m+n} + U_{m-n})$ linearization as a formal
  polynomial identity over $R[X]$ (this problem).

### Our Goal

Prove `2 * U R m * T R n = U R (m+n) + U R (m-n)` in Lean 4 / Mathlib for all
`m : ℤ`, `n : ℕ` (or `n : ℤ`), over an arbitrary `CommRing R`, ideally with `n : ℤ`
so no case split on sign is needed.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| de-moivre-oq-02-oq-02-oq-01 | Direct parent; U·U linearization | sum recurrence, two-step induction, `linear_combination` |
| de-moivre-oq-02-oq-02 | Grandparent; T·U cross product 2·T_m·U_n | paired integer induction over ℤ |
| de-moivre-oq-02 | First-kind product-to-sum 2·T_m·T_n | recurrence matching |

## Initial Thoughts

### Potential Approaches

1. **Direct recurrence matching in `n`** (recommended): Fix $m$ and induct on $n$ using
   $T_{n+2} = 2X\,T_{n+1} - T_n$. The RHS $U_{m+n} + U_{m-n}$ satisfies the same
   second-order recurrence in $n$ (since $U$ satisfies it in its index), so a two-step
   induction — exactly the parent's technique — should close it via `linear_combination`.
   Base cases: $n=0$ gives $2 U_m T_0 = 2 U_m = U_m + U_m$ (using $T_0 = 1$, $U_{m} + U_{m}$);
   $n=1$ gives $2 U_m T_1 = 2 U_m X = U_{m+1} + U_{m-1}$ (using $T_1 = X$ and $2X U_m = U_{m+1}+U_{m-1}$).
2. **Reduce to existing lemmas**: Combine the grandparent's $2 T_n U_m = U_{m+n} + U_{m-n}$
   (note $T\cdot U = U\cdot T$ by commutativity) — if the grandparent already proves
   $2 T_m U_n = U_{m+n} + U_{n-m}$, then swapping roles gives this directly. **Check first
   whether this is literally the grandparent lemma with variables renamed** — it may be a
   near-trivial corollary rather than new content.

### Key Difficulties

- Verifying whether approach 2 makes this a trivial restatement of an existing lemma
  (in which case the quality gate suggests picking a fresher problem instead).
- Handling the $T_{m-n}$ / $U_{m-n}$ negative-index convention for $n > m$; using
  $\mathbb{Z}$ indices sidesteps a case split.

### What Would a Proof Need?

- The rearranged recurrence `2 * X * U R k = U R (k+1) + U R (k-1)` (already in the parent as `two_X_U`).
- `T_add_two`, `U_add_two`, `T_zero`, `T_one`, `U_zero`, `U_one` from Mathlib.
- `linear_combination` to discharge the inductive step.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- The parent proof of the harder $U\cdot U$ full-sum linearization is only ~146 lines;
  this two-term identity should be shorter.
- All ingredients (recurrences, `two_X_U`, paired induction) are already demonstrated in
  the immediate parent, so this is a near-copy with a two-term (rather than sum) RHS.
- **First action**: confirm this is not already the grandparent lemma up to renaming.

**Estimated Effort**:
- Exploration: 1–2 hours (check grandparent lemma statement)
- If tractable: 0.5–1 day

## References

### Papers
- J. C. Mason, D. C. Handscomb, *Chebyshev Polynomials*, CRC Press, 2003 — product and linearization formulas, §2.4.

### Online Resources
- https://en.wikipedia.org/wiki/Chebyshev_polynomials#Products_of_Chebyshev_polynomials

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Polynomials` / `Polynomial.Chebyshev` — `T`, `U`, recurrences, negative-index conventions.

## Metadata

```yaml
tags:
  - algebra
  - chebyshev-polynomials
  - polynomial-identity
  - linearization
  - product-to-sum
related_proofs:
  - de-moivre-oq-02-oq-02-oq-01
  - de-moivre-oq-02-oq-02
difficulty: low
source: gallery-gap
created: 2026-07-04T06:28:11-07:00
```

**Significance**: 5/10
**Tractability**: 7/10
