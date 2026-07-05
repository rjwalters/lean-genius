# Problem: Doubly-Exponential Lower Bound for Sylvester's Sequence

**Slug**: sylvester-sequence-oq-01-oq-02
**Created**: 2026-07-04
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $a_0 = 2$ and $a_{n+1} = a_n^2 - a_n + 1$ be Sylvester's sequence. Prove the
doubly-exponential lower bound

$$
a_n \;\ge\; 2^{\,2^{\,n-1}} \qquad (n \ge 1),
$$

and the matching product/growth identities that drive it: the telescoping recurrence

$$
a_{n+1} - 1 = a_n\,(a_n - 1) = \prod_{k=0}^{n} a_k,
$$

so that $a_{n+1} > a_n^2 - a_n$ forces at-least-squaring growth. Equivalently, establish
that $\log_2 \log_2 a_n$ grows linearly, pinning the double-exponential rate that makes
$\sum 1/a_k$ the fastest-converging Egyptian-fraction representation of $1$.

### Plain Language

Sylvester's sequence $2, 3, 7, 43, 1807, \dots$ roughly *squares* at each step, so it
grows astronomically fast — like $2$ raised to $2$ raised to $n$. This problem asks for a
clean, machine-checked lower bound capturing that double-exponential growth, together with
the product formula $a_{n+1}-1 = a_0 a_1 \cdots a_n$ that explains why: each term is one
more than the product of all earlier terms, so the sequence at least squares every step.

### Why This Matters

The doubly-exponential growth rate is *the* quantitative content of Sylvester's sequence:
it is what makes the greedy Egyptian-fraction / Sylvester–Fibonacci expansion converge
fastest, and it underlies bounds in Znám's problem and Curtiss's theorem on unit-fraction
representations of $1$. The parent entry `sylvester-sequence-oq-01` proves the exact
reciprocal-sum and pairwise-coprimality facts; this entry supplies the growth-rate half,
completing the elementary theory of the sequence in the gallery.

## Known Results

### What's Already Proven

- $\sum_{k<n} 1/a_k = 1 - 1/(a_n-1)$ and pairwise coprimality — parent
  `sylvester-sequence-oq-01`.
- Product formula $a_{n+1} - 1 = \prod_{k \le n} a_k$ is classical and short to prove by
  induction from the recurrence.

### What's Still Open (for this entry)

- A formalized doubly-exponential lower bound $a_n \ge 2^{2^{n-1}}$ (or an equivalent
  clean rate).
- The telescoping product identity as a reusable lemma.

### Our Goal

Formalize the product identity and the lower bound $a_n \ge 2^{2^{n-1}}$ for $n \ge 1$,
axiom-free, by induction (base cases $a_1 = 3 \ge 2$, $a_2 = 7 \ge 4$, and
$a_{n+1} = a_n^2 - a_n + 1 \ge a_n^2 / 2 \ge (2^{2^{n-1}})^2/2 = 2^{2^{n}-1} \ge 2^{2^{n-1}}$-style step).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| sylvester-sequence-oq-01 | parent: reciprocal sum + coprimality | induction, telescoping |
| fermat-numbers / double-exponential growth entries | analogous doubly-exponential recurrences | induction, monotone bounds |
| egyptian-fractions (if present) | application context | greedy expansion |

## Initial Thoughts

### Potential Approaches

1. **Direct induction on the bound**: prove $a_n \ge 2^{2^{n-1}}$ by strong induction,
   using $a_{n+1} \ge a_n^2 - a_n \ge \tfrac{1}{2}a_n^2$ for $a_n \ge 2$.
   - Why it might work: purely arithmetic; `Nat`/`pow` monotonicity lemmas suffice.
   - Risk: the $\tfrac12 a_n^2$ step needs `a_n ≥ 2` maintained as an invariant.

2. **Via the product formula**: prove $a_{n+1}-1 = \prod_{k\le n} a_k$ first, then bound
   the product from below.
   - Why it might work: gives a stronger structural identity as a byproduct.
   - Risk: product manipulation in `Nat` is slightly heavier.

### Key Difficulties

- Keeping the invariant $a_n \ge 2$ (needed to drop the $-a_n$ term).
- `pow`-of-`pow` rewriting: $2^{2^{n-1}} \cdot 2^{2^{n-1}} = 2^{2^n}$.

### What Would a Proof Need?

- Lemma: `2 ≤ a n` for all `n` (monotone invariant).
- Lemma: `a (n+1) = a n * a n - a n + 1` and `a (n+1) - 1 = a n * (a n - 1)`.
- `Nat.pow_le_pow_left` / `pow_mul` for the exponent arithmetic.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- Elementary induction; no analysis needed.
- Similar doubly-exponential bounds (Fermat numbers) are already formalizable in Mathlib.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–2 days

## References

### Mathlib
- `Mathlib.Algebra.Order.Monoid.Lemmas` — `pow` monotonicity.
- `Mathlib.Data.Nat.Basic` — `Nat` arithmetic, strong induction.

### Online Resources
- OEIS A000058 (Sylvester's sequence) — growth and product-formula notes.

## Metadata

```yaml
tags:
  - number-theory
  - recurrence-sequences
  - egyptian-fractions
  - growth-bounds
related_proofs:
  - sylvester-sequence-oq-01
  - sylvester-sequence
difficulty: medium
source: gallery-gap
created: 2026-07-04
```

**Significance**: 5/10
**Tractability**: 7/10
