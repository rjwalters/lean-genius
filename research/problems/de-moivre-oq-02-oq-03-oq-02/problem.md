# Problem: Degree and leading coefficient of Chebyshev polynomials

**Slug**: de-moivre-oq-02-oq-03-oq-02
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For the Chebyshev polynomials of the first kind $T_n$ (defined by
$T_0 = 1$, $T_1 = X$, $T_{n+2} = 2X\,T_{n+1} - T_n$):

$$
\deg T_n = n \quad\text{and}\quad \operatorname{lead}(T_n) = 2^{\,n-1}
\qquad (n \ge 1).
$$

### Plain Language

Chebyshev polynomials arise from de Moivre's formula via
$\cos(n\theta) = T_n(\cos\theta)$. Each $T_n$ is a genuine degree-$n$ polynomial,
and its top coefficient is $2^{n-1}$ for $n \ge 1$ (and $1$ for $n = 0$). The
goal is an axiom-free Lean proof of the degree and leading-coefficient formulas
straight from the recurrence.

### Why This Matters

These two facts are the gateway to the rest of Chebyshev theory: the minimax /
equioscillation property, orthogonality, and the monic rescaling
$2^{1-n}T_n$ that minimizes the sup norm on $[-1,1]$. They are a clean,
self-contained companion to the parent de Moivre gallery proof and a good test of
Mathlib's `Polynomial.Chebyshev` API.

## Known Results

### What's Already Proven

- Mathlib defines `Polynomial.Chebyshev.T R n` with the defining recurrence
  (`Polynomial.Chebyshev.T_add_two`).
- Mathlib has `Polynomial.Chebyshev.natDegree_T` and leading-coefficient lemmas
  in characteristic-zero / suitable rings (to be confirmed and reused).
- Gallery parent `de-moivre-oq-02-oq-03` establishes the
  $\cos(n\theta) = T_n(\cos\theta)$ bridge (verified, 0-axiom).

### What's Still Open

- A registered, self-contained statement of `natDegree (T ℤ n) = n` and
  `leadingCoeff (T ℤ n) = 2^(n-1)` for $n \ge 1$, even if it merely repackages
  existing Mathlib lemmas with the recurrence.

### Our Goal

Prove, over $\mathbb{Z}$ (or a general ordered/char-zero commutative ring):
- `(Polynomial.Chebyshev.T ℤ n).natDegree = n` for all $n$ (with the $n = 0$ edge
  case handled);
- `(Polynomial.Chebyshev.T ℤ n).leadingCoeff = 2^(n-1)` for $n \ge 1$,
  by strong/two-step induction on the recurrence $T_{n+2} = 2X T_{n+1} - T_n$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| de-moivre-oq-02-oq-03 | Direct parent; cos(nθ) = Tₙ(cos θ) bridge | de Moivre, induction |
| de-moivre-oq-02-oq-03-oq-02 (this) | degree/leading-coeff base for minimax | polynomial degree |

## Initial Thoughts

### Potential Approaches

1. **Induction on the recurrence**: in $2X\,T_{n+1} - T_n$, the degree of the
   first term ($1 + \deg T_{n+1} = n+2$) dominates $\deg T_n = n$, so degrees add
   and the leading coefficient doubles each step.
   - Why it might work: the recurrence makes both claims a one-step induction
     once the dominance is established.
   - Risk: ensuring `Polynomial.natDegree_add_eq_left_of_natDegree_lt` hypotheses
     (no cancellation) hold at the top degree.

2. **Reuse Mathlib lemmas** if `natDegree_T` / leading-coeff lemmas already exist,
   reducing the task to packaging and the $2^{n-1}$ closed form.
   - Why it might work: minimal new proof obligation.
   - Risk: Mathlib may state these only over specific rings; may need a cast.

### Key Difficulties

- The $n = 0$ vs $n \ge 1$ split for the $2^{n-1}$ formula.
- Degree-dominance bookkeeping so leading terms do not cancel in $2X T_{n+1}-T_n$.

### What Would a Proof Need?

- Key lemma 1: `Polynomial.Chebyshev.T_add_two` (the recurrence).
- Key lemma 2: `Polynomial.natDegree_add_eq_left_of_natDegree_lt`,
  `Polynomial.leadingCoeff` / `Polynomial.coeff_natDegree`.
- Technical requirements: two-step induction, `ring`, degree lemmas over
  $\mathbb{Z}$.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Mathlib already provides the Chebyshev recurrence and degree machinery.
- The induction is short; the main care is the no-cancellation degree argument.
- Similar polynomial degree/leading-coefficient inductions exist in the gallery.

**Estimated Effort**:
- Exploration: half a day
- If tractable: 2–3 days

## References

### Mathlib
- `Mathlib.RingTheory.Polynomial.Chebyshev` — `Polynomial.Chebyshev.T`,
  `T_add_two`, degree lemmas.
- `Mathlib.Algebra.Polynomial.Degree.Lemmas` — degree-of-sum / leading-coeff API.

## Metadata

```yaml
tags:
  - algebra
  - polynomials
  - chebyshev
  - de-moivre
related_proofs:
  - de-moivre-oq-02-oq-03
difficulty: medium
source: gallery-gap
created: 2026-06-24
```
