# Problem: Signed-input Newton inequality

**Slug**: amgm-inequality-oq-02-oq-02-oq-01
**Created**: 2026-07-04T22:03:38-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For real numbers $x_1, \dots, x_n$, let $e_k$ denote the $k$-th elementary symmetric
polynomial and $p_k = e_k / \binom{n}{k}$ its normalized ("Newton mean") form. Newton's
inequality states

$$
p_k^2 \ge p_{k-1}\, p_{k+1}, \qquad 1 \le k \le n-1,
$$

equivalently $e_k^2 \ge e_{k-1} e_{k+1} \cdot \tfrac{\binom{n}{k}^2}{\binom{n}{k-1}\binom{n}{k+1}}$
up to the standard binomial normalization. The parent entry proves this under the
hypothesis $x_i \ge 0$ via a cleared-denominator argument. The goal is to **prove Newton's
inequality for general signed inputs** $x_i \in \mathbb{R}$ (not all non-negative), where
the cleared-denominator argument fails.

### Plain Language

Newton's inequality says the normalized symmetric means of a list of numbers are
log-concave. The gallery already proves this when every input is non-negative. But the
inequality is actually true for *all real* inputs — the non-negativity was only needed for
the particular proof technique used. This problem asks for a proof that works for negative
inputs too, which requires a genuinely different method.

### Why This Matters

The signed case is the "real" theorem (Newton's inequality is a statement about real-rooted
polynomials). Removing the non-negativity hypothesis strengthens the gallery entry from a
special case to the full classical result, and exercises the connection to the
Hermite–Biehler / real-rootedness machinery.

## Known Results

### What's Already Proven

- Parent `amgm-inequality-oq-02-oq-02`: Newton's inequality for $x_i \ge 0$ (cleared
  denominators).
- Classical fact: for a **real-rooted** polynomial, the coefficient sequence is
  ultra-log-concave — this is exactly Newton's inequality and holds regardless of root signs.
- Maclaurin's inequalities (the non-negative refinement) sit above Newton's inequality.

### What's Still Open (in this gallery)

- Newton's inequality $e_k^2 \ge e_{k-1} e_{k+1}$ (normalized) for signed real inputs.
- The bridge lemma: differentiating $\prod (X - x_i)$ preserves real-rootedness (Rolle),
  reducing the general $k$ case to the $k=1$ base case.

### Our Goal

Prove the signed-input Newton inequality. The cleanest route is the real-rooted-polynomial
argument: repeatedly differentiate the polynomial with roots $x_i$ (Rolle keeps it
real-rooted) to reduce $p_k^2 \ge p_{k-1}p_{k+1}$ to the discriminant-nonnegativity of a
quadratic ($k=1$), which holds for any real coefficients.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| amgm-inequality-oq-02-oq-02 | Direct parent; non-negative case | cleared denominators |
| amgm-inequality (parent chain) | AM–GM / symmetric function inequalities | Maclaurin, Newton |

## Initial Thoughts

### Potential Approaches

1. **Real-rooted reduction (Rolle)**: $P(X) = \prod (X - x_i)$ is real-rooted; each
   derivative $P', P'', \dots$ stays real-rooted (Rolle), and $p_k^2 \ge p_{k-1}p_{k+1}$
   for general $k$ reduces to the $k=1$ case for a differentiated polynomial.
   - Why it might work: the $k=1$ case is a quadratic discriminant $\ge 0$, true for any
     reals; this is the standard textbook proof.
   - Risk: formalizing "derivative of real-rooted stays real-rooted" (Rolle counting) in
     Mathlib may be the bulk of the work.

2. **Hermite–Biehler / interlacing**: use interlacing of $P$ and $P'$ roots.
   - Why it might work: gives log-concavity directly.
   - Risk: heavier machinery, likely not in Mathlib.

### Key Difficulties

- Formalizing that differentiation preserves real-rootedness with correct root counts.
- Managing the elementary-symmetric ↔ polynomial-coefficient dictionary in Mathlib
  (`MvPolynomial` / `Polynomial` esymm lemmas).

### What Would a Proof Need?

- Key lemma 1: $\prod(X - x_i)$ is real-rooted ⇒ $P'$ is real-rooted (Rolle, multiplicity
  accounting).
- Key lemma 2: reduction of general-$k$ Newton to $k=1$ via differentiation.
- Key lemma 3: $k=1$ base case ($p_1^2 \ge p_0 p_2$) = quadratic discriminant $\ge 0$.

## Tractability Assessment

**Difficulty**: Medium–High

**Justification**:
- The mathematics is classical and well-understood (real-rooted reduction).
- The obstruction is Lean formalization of Rolle-based root counting, which may or may not
  have adequate Mathlib support.
- The $k=1$ base case is easy; the induction machinery is the risk.

**Estimated Effort**:
- Exploration: 1–2 days (survey Mathlib `Polynomial` real-root / derivative lemmas).
- If tractable: 1–2 weeks.
- If hard: root-counting formalization could stall the general-$k$ step.

## References

### Papers
- I. Newton; Maclaurin — classical symmetric-mean inequalities.
- Hardy, Littlewood, Pólya, *Inequalities*, §2.22 (Newton's inequalities).
- Marcus & Minc / Marden, real-rooted polynomials and interlacing.

### Mathlib
- `Polynomial` esymm / `MvPolynomial.esymm` — elementary symmetric functions.
- `Polynomial.derivative`, Rolle's theorem (`exists_deriv_eq_zero`), root-count lemmas.

## Metadata

```yaml
tags:
  - inequalities
  - elementary-symmetric-polynomials
  - newton-inequalities
  - maclaurin-inequalities
  - log-concavity
  - real-rooted-polynomials
  - am-gm
related_proofs:
  - amgm-inequality-oq-02-oq-02
difficulty: high
source: gallery-gap
created: 2026-07-04T22:03:38-07:00
```

**Significance**: 6/10
**Tractability**: 4/10
