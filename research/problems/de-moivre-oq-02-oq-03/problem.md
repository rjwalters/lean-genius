# Problem: Minimax Property of Chebyshev Polynomials

**Slug**: de-moivre-oq-02-oq-03
**Created**: 2026-06-18
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Let $T_n$ be the degree-$n$ Chebyshev polynomial of the first kind and $\tilde T_n = 2^{-(n-1)} T_n$ its monic normalization ($n \ge 1$). Then among all **monic** real polynomials of degree $n$,

$$
\| \tilde T_n \|_{\infty,[-1,1]} \;=\; 2^{-(n-1)} \;=\; \min_{\substack{p \text{ monic} \\ \deg p = n}} \ \max_{x \in [-1,1]} |p(x)|.
$$

That is, the monic Chebyshev polynomial uniquely minimizes the sup-norm on $[-1,1]$.

### Plain Language

Among all degree-$n$ polynomials with leading coefficient $1$, the one that stays closest to zero on the interval $[-1,1]$ is the (rescaled) Chebyshev polynomial, and its largest deviation is exactly $2^{-(n-1)}$. We want a formal proof of this classical extremal/minimax property.

### Why This Matters

The Chebyshev minimax property is the foundational result of approximation theory (best uniform approximation, optimal interpolation nodes, polynomial conditioning). It extends the gallery's Chebyshev-via-De-Moivre entry (`de-moivre-oq-02`) from algebraic identities to the central extremal characterization.

## Known Results

### What's Already Proven

- `de-moivre-oq-02` ("Chebyshev Polynomial Properties via De Moivre's Theorem") — recurrences, parity, product-to-sum, roots, and $T_n(\cos\theta) = \cos(n\theta)$.
- Mathlib `Polynomial.Chebyshev.T` with `Polynomial.Chebyshev.cos_T` (the $\cos$ evaluation) and degree/leading-coefficient lemmas.

### What's Still Open

- The minimax/extremal statement is not in the gallery.
- The equioscillation argument (the $n+1$ alternating extrema of $T_n$ on $[-1,1]$) in Lean.

### Our Goal

Prove the minimax property via the classical equioscillation/sign-change contradiction: if a monic $p$ had strictly smaller sup-norm, then $\tilde T_n - p$ would change sign at the $n+1$ extrema of $\tilde T_n$ (where $T_n(\cos(k\pi/n)) = (-1)^k$), forcing $n$ roots in a degree $< n$ polynomial — a contradiction.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| de-moivre-oq-02 | Chebyshev identities, extrema values $T_n(\cos(k\pi/n))=(-1)^k$ | De Moivre, recurrences |
| Mathlib `Polynomial.Chebyshev` | Definition, $\cos$-evaluation, leading coefficient $2^{n-1}$ | polynomial algebra |

## Initial Thoughts

### Potential Approaches

1. **Approach A — equioscillation contradiction**: assume monic $p$ with $\|p\|_\infty < 2^{-(n-1)}$; evaluate $q = \tilde T_n - p$ (degree $\le n-1$) at the $n+1$ alternating extrema; the strict inequality forces $\operatorname{sign} q$ to alternate, giving $\ge n$ roots, contradicting $\deg q \le n-1$. Risk: formalizing "n sign changes ⇒ n roots" and the extrema enumeration.
2. **Approach B — inner-product / orthogonality slant**: less direct; the sign-change argument is the standard and most tractable route.

### Key Difficulties

- Enumerating the $n+1$ Chebyshev extrema $x_k = \cos(k\pi/n)$ and their alternating signs in Lean.
- The "sign changes imply roots" intermediate-value + root-counting lemma over $\mathbb{R}$.

### What Would a Proof Need?

- Lemma: $\tilde T_n(x_k) = (-1)^k 2^{-(n-1)}$ at $x_k = \cos(k\pi/n)$, $k=0,\dots,n$.
- A root-counting lemma: a real polynomial with $m$ sign alternations on an interval has $\ge m$ roots there.
- Degree bookkeeping: $\deg(\tilde T_n - p) \le n-1$ for monic $p$ of degree $n$.

## Tractability Assessment

**Difficulty**: Medium–High

**Justification**:
- Classical, well-understood proof with a clear structure.
- Mathlib has Chebyshev polynomials and IVT; the root-counting step may need assembly.
- Real-analysis bookkeeping (extrema, sign changes) is the main cost.

**Estimated Effort**:
- Exploration: 1 day
- If tractable: 1–2 weeks
- If hard (root-counting infra missing): 2–4 weeks

## References

### Papers
- T. J. Rivlin, *Chebyshev Polynomials* — the minimax theorem and equioscillation.

### Online Resources
- Standard approximation-theory texts (Cheney, Powell) — best uniform approximation by polynomials.

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Polynomials` and `Polynomial.Chebyshev` — Chebyshev definitions and evaluations.
- `Polynomial.card_roots_le_degree`, IVT (`intermediate_value_Icc`) — root counting and sign changes.

## Metadata

```yaml
tags:
  - approximation-theory
  - chebyshev-polynomials
  - minimax
  - real-analysis
related_proofs:
  - de-moivre-oq-02
difficulty: high
source: proof-suggestion
created: 2026-06-18
```
