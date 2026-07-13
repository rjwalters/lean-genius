# Erdős #1153 - Knowledge Base

## Problem Statement

**Erdős Problem #1153** (Vaughan's survey [Va99, 2.44]):

For nodes $x_1, \ldots, x_n \in [-1, 1]$, let
$$l_k(x) = \prod_{i \neq k} \frac{x - x_i}{x_k - x_i}$$
be the Lagrange basis polynomials, and
$$\lambda(x) = \sum_k |l_k(x)|$$
the Lebesgue function. Is it true that for any fixed $-1 \leq a < b \leq 1$,
$$\max_{x \in [a,b]} \lambda(x) > \left(\frac{2}{\pi} - o(1)\right) \log n?$$

**Status**: Proved (yes).

The sharp constant $2/\pi$ was established by Erdős (1961), sharpening
Bernstein's earlier (1931) logarithmic lower bound. Chebyshev polynomial
roots achieve this constant: $\Lambda_n \leq (2/\pi + o(1)) \log n$, making
them optimal interpolation nodes.

## Status

**Erdős Database Status**: SOLVED (1961, by Erdős)

**Formalization Status**: AXIOMATIZED in
`proofs/Proofs/Erdos1153Problem.lean`. The main asymptotic lower bound
`erdos_1153` is stated as an axiom (classical complex/approximation
analysis content beyond current Mathlib coverage). The full-interval
corollary `erdos_1153_full_interval` is derived from the axiom by
instantiation. Structural Lagrange / Lebesgue identities are fully proved
machine-checked.

**Tractability Score**: 6/10
**Aristotle Suitable**: No (definitions and structural lemmas already
proved; remaining axiom is the substantive open content)

## Tags

- erdos
- analysis
- polynomials
- interpolation
- approximation-theory
- solved

## Gallery Integration

- `src/data/proofs/erdos-1153/` (meta.json, annotations.json, index.ts)
- `proofs/Proofs/Erdos1153Problem.lean` — 169 LOC, 4 defs, 6 theorems,
  1 axiom, 0 sorries, namespace `Erdos1153`
- Mathlib pin: `v4.26.0` (commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

## Related Problems

- Problem #2000
- Problem #83
- Problem #888
- Problem #2
- Problem #39
- Problem #1

Related gallery slugs (per `crossReferences` in `meta.json`):

- `erdos-1129` — related Erdős problem on interpolation and Lebesgue
  constants
- `erdos-1132` — related Erdős problem on polynomial interpolation

## References

- Bernstein (1931): "On the distribution of zeros of Lagrange interpolation
  polynomials"
- Erdős (1961): "Problems and results on the theory of interpolation, II"
  [Er61c]
- Vaughan [Va99, 2.44]: Survey of Erdős problems in analysis
- https://erdosproblems.com/1153

## Sessions

| Session | Date | Phase | Type | PR |
|---------|------|-------|------|----|
| S1 (stub) | 2026-01-15 | NEW | scaffold | — (auto-generated stub) |
| S2 | 2026-05-17 | COMPLETED | STATE-SYNC (this PR) | research/erdos-1153-s2-statesync-completed-drift-catchup |

---

*Generated from erdosproblems.com on 2026-01-15; S2 STATE-SYNC catchup 2026-05-17 by researcher-10.*
