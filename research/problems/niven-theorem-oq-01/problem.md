# Problem: Niven's Theorem — Rational Angles with Rational Cosine

**Slug**: niven-theorem-oq-01
**Created**: 2026-06-16
**Status**: Active
**Source**: seeker-selected <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\text{If } \theta \in \mathbb{Q}\cdot\pi \text{ and } \cos\theta \in \mathbb{Q},
\text{ then } \cos\theta \in \left\{0, \pm\tfrac12, \pm 1\right\}.
$$

Equivalently, the only rational multiples of $\pi$ whose cosine is rational are those
with $\cos\theta \in \{0, \pm\frac12, \pm1\}$, i.e. $\theta$ a multiple of $\pi/3$ or
$\pi/2$. The same conclusion holds with $\sin$ or $\tan$ in place of $\cos$ (for
$\tan$, the rational values are $0, \pm 1$).

### Plain Language

If you take a "nice" angle — a rational number of degrees, or equivalently a rational
multiple of $\pi$ radians — then its cosine is almost never a nice rational number.
The only exceptions are the familiar special angles: $\cos$ equals $0$, $\pm\frac12$,
or $\pm1$. Every other rational angle has an irrational (in fact algebraic of higher
degree) cosine.

### Why This Matters

Niven's theorem (Ivan Niven, 1956) is a clean, surprising rationality result bridging
trigonometry and algebraic number theory. The standard proof shows $2\cos\theta$ is an
algebraic integer (via Chebyshev polynomials: $2\cos(n\theta)$ is a monic integer
polynomial in $2\cos\theta$), and a rational algebraic integer must be an ordinary
integer; combined with $|2\cos\theta| \le 2$ this forces $2\cos\theta \in
\{0,\pm1,\pm2\}$. It is a "named theorem" with no current gallery entry and exercises
Mathlib's Chebyshev-polynomial and algebraic-integer machinery.

## Known Results

### What's Already Proven

- Mathlib has `Polynomial.Chebyshev.T` (Chebyshev polynomials of the first kind) with
  `Polynomial.Chebyshev.T_complex_cos` / real-cos evaluation lemmas giving
  $T_n(\cos\theta) = \cos(n\theta)$.
- Mathlib has `IsIntegral`, `IsIntegrallyClosed`, and the fact that $\mathbb{Z}$ is
  integrally closed in $\mathbb{Q}$ (`Rat.isIntegrallyClosed` / a rational integral over
  $\mathbb{Z}$ is an integer).
- If $\theta = 2\pi k / n$ then $\cos(n\theta) = 1$, so $2\cos\theta$ is a root of a
  monic integer polynomial built from $2T_n(x/2) - 2$.

### What's Still Open

- No Lean formalization of Niven's theorem exists in this gallery.
- The chain "rational + algebraic integer ⟹ integer" applied to $2\cos\theta$, and the
  bounded enumeration $2\cos\theta \in \{0,\pm1,\pm2\}$, has not been assembled here.

### Our Goal

Formalize the cosine form of Niven's theorem: for $\theta = r\pi$ with $r \in
\mathbb{Q}$, if $\cos\theta \in \mathbb{Q}$ then $\cos\theta \in
\{0,\pm\frac12,\pm1\}$. Prove $2\cos\theta$ is an algebraic integer via the monic
Chebyshev relation, conclude it is a rational algebraic integer hence an integer in
$[-2,2]$, and finish by enumeration.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| abel-ruffini | Algebraic-number-theory rationality / degree arguments | minimal polynomials, integrality |
| nth-root-irrational | Rational-root / integrally-closed reasoning over $\mathbb{Q}$ | rational root theorem, `IsIntegral` |
| cube-root-2-irrational | Irrationality from monic integer polynomial constraints | algebraic integers, bounding |

## Initial Thoughts

### Potential Approaches

1. **Chebyshev + integrally-closed**: show $2\cos(n\theta)$ is monic-integer-polynomial
   in $2\cos\theta$; with $\cos(n\theta) = \pm1$ for the right $n$, deduce $2\cos\theta$
   is an algebraic integer, hence (being rational) an integer in $[-2,2]$.
   - Why it might work: Mathlib's `Chebyshev.T` and `IsIntegrallyClosed` give both
     halves directly.
   - Risk: massaging $T_n$ into the explicit monic integer polynomial whose root is
     $2\cos\theta$; handling the doubling $x \mapsto x/2$ cleanly.

2. **Minimal-polynomial / field-degree argument**: study $\mathbb{Q}(\cos\theta)$
   over $\mathbb{Q}$ using cyclotomic degrees.
   - Why it might work: leverages Mathlib's cyclotomic API.
   - Risk: heavier machinery than needed; degree computations can be fiddly.

### Key Difficulties

- Relating Mathlib's Chebyshev evaluation lemmas (often stated over $\mathbb{C}$ or for
  $\cos$) to a monic **integer**-coefficient polynomial in the variable $2\cos\theta$.
- Cleanly invoking "rational + integral over $\mathbb{Z}$ ⟹ integer" and bounding by
  $|2\cos\theta| \le 2$.

### What Would a Proof Need?

- Key lemma 1: a monic polynomial $P \in \mathbb{Z}[X]$ with $P(2\cos\theta) = 0$ when
  $\theta$ is a rational multiple of $\pi$ (from $\cos(n\theta) \in \{1,-1\}$).
- Key lemma 2: a rational number integral over $\mathbb{Z}$ is an integer
  (`IsIntegrallyClosed` / rational root theorem).
- Technical requirements: `Polynomial.Chebyshev.T`, `Real.cos`, `IsIntegral`,
  `Int.cast` bounds, finite enumeration over $[-2,2] \cap \mathbb{Z}$.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Classic theorem with a single, well-trodden proof that maps onto existing Mathlib
  components (Chebyshev polynomials, integral closure of $\mathbb{Z}$ in $\mathbb{Q}$).
- Closely related to gallery proofs (abel-ruffini, nth-root-irrational) that already use
  integrality and minimal-polynomial reasoning.

**Estimated Effort**:
- Exploration: 1 to 2 days
- If tractable: 4 to 7 days
- If hard: 2 to 3 weeks (if the Chebyshev-to-monic-integer step is awkward in Mathlib)

## References

### Papers
- I. Niven, "Irrational Numbers", Carus Mathematical Monographs No. 11, 1956 — Corollary
  3.12 (the theorem and proof).
- J. M. H. Olmsted, "Rational values of trigonometric functions", Amer. Math. Monthly,
  1945.

### Online Resources
- Wikipedia, "Niven's theorem" — statement and the algebraic-integer proof sketch.

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev` — $T_n(\cos\theta) =
  \cos(n\theta)$.
- `Mathlib.RingTheory.Polynomial.Chebyshev` — Chebyshev polynomials over a ring.
- `Mathlib.RingTheory.IntegrallyClosed` — $\mathbb{Z}$ integrally closed in $\mathbb{Q}$.
- `Mathlib.RingTheory.IntegralClosure` / `IsIntegral` — algebraic integers.

## Metadata

```yaml
tags:
  - analysis
  - number-theory
  - trigonometry
  - algebraic-number-theory
related_proofs:
  - abel-ruffini
  - nth-root-irrational
difficulty: medium
source: seeker-selected
created: 2026-06-16
```
