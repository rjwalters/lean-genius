# Problem: Nonderogatory ⇒ cyclic vector — does the prime-power proof simplify for char 0 / algebraically closed fields?

**Slug**: cayley-hamilton-minpoly-oq-05-oq-01-oq-04-wip-03-oq-02
**Created**: 2026-07-04T12:34:40-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
M \in \mathrm{Mat}_n(K) \text{ nonderogatory with } \mu_M = p^e,\ p \text{ irreducible}
\;\Rightarrow\; \exists\,v,\ \{v, Mv, \dots, M^{n-1}v\} \text{ a basis (cyclic vector)}.
$$

Specialize the existing general-characteristic proof to $\operatorname{char}(K) = 0$ and to
$K$ algebraically closed, where every irreducible $p$ is linear.

### Plain Language

A matrix is *nonderogatory* when its minimal and characteristic polynomials coincide, which
is exactly the condition for having a cyclic (Krylov) vector generating the whole space. The
gallery WIP proves the prime-power minimal-polynomial case $\mu_M = p^e$ over any field. When
$K$ is algebraically closed (or $\operatorname{char} K = 0$ with $p$ linear), $p = X - \lambda$,
so $\mu_M = (X-\lambda)^e$ and the cyclic vector is a single Jordan-string generator. This
problem asks for the streamlined proof in that setting.

### Why This Matters

The general proof carries UFD/irreducible-factor machinery that is unnecessary when $p$ is
linear. A clean linear-case proof (a) documents the Jordan-block intuition behind the general
argument, (b) may be directly Mathlib-contributable, and (c) is a self-contained warm-up that
de-risks the general `wip-04` combination target (`...-oq-01`).

## Known Results

### What's Already Proven

- Prime-power case $\mu_M = p^e$ over arbitrary $K$ — the parent WIP entry (axiom-free).
- Nonderogatory $\Leftrightarrow$ cyclic vector exists — classical rational canonical form.
- Over algebraically closed $K$, nonderogatory $\Leftrightarrow$ one Jordan block per eigenvalue — classical.

### What's Still Open (for this formalization)

- A Lean proof of the $p = X - \lambda$ special case that avoids the general UFD argument.
- Whether the simplification meaningfully shortens the Lean development or just re-specializes.

### Our Goal

Formalize the cyclic-vector existence for $\mu_M = (X-\lambda)^e$ (single linear irreducible),
picking $v$ with $(M-\lambda)^{e-1} v \ne 0$, and confirm it discharges the algebraically
closed / char-0 nonderogatory case directly.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| cayley-hamilton-minpoly-oq-05-oq-01-oq-04-wip-03 | parent prime-power (all fields) proof | minimal polynomial, cyclic vectors |
| abel-ruffini-galois-extensions-oq-10 | field-theoretic structure of splitting fields | irreducibility, field extensions |

## Initial Thoughts

### Potential Approaches

1. **Direct Jordan-string vector**: with $\mu_M = (X-\lambda)^e$ and $n = e$ (nonderogatory),
   pick $v$ so that $(M-\lambda)^{e-1}v \ne 0$; then $v, Mv, \dots, M^{e-1}v$ are independent.
   - Why it might work: independence follows from a single nonvanishing of the top power.
   - Risk: relating $n$ and $e$ correctly (nonderogatory forces $\deg\mu_M = n$).

2. **Reduce to nilpotent by shifting**: replace $M$ by $N = M - \lambda I$ (nilpotent of index $e$),
   prove the cyclic vector for $N$, transfer back.
   - Why it might work: nilpotent single-block theory is the cleanest special case.
   - Risk: Mathlib's nilpotent-index API coverage may be thin.

### Key Difficulties

- Establishing $\deg \mu_M = n$ from the nonderogatory hypothesis in Lean.
- Independence of the Krylov sequence from a single top-power nonvanishing.

### What Would a Proof Need?

- Key lemma 1: nonderogatory $\Rightarrow \deg \mu_M = n$ (min poly = char poly degree).
- Key lemma 2: $(M-\lambda)^{e-1}v \ne 0 \Rightarrow \{M^i v\}_{i<e}$ linearly independent.
- Technical requirements: `Matrix`/`LinearMap` minimal-polynomial API and nilpotent-shift lemmas.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Specializing an existing axiom-free proof to the linear-irreducible case is bounded.
- The Jordan/nilpotent intuition is standard and finite-dimensional.
- Mathlib has minimal-polynomial and cyclic-vector groundwork from the parent entries.

**Estimated Effort**:
- Exploration: 1-2 days
- If tractable: 1 week
- If hard: 2 weeks

## References

### Papers
- Standard reference: Hoffman & Kunze, *Linear Algebra* — cyclic vectors and rational/Jordan canonical form.

### Online Resources
- https://en.wikipedia.org/wiki/Cyclic_vector — cyclic vectors and companion matrices.

### Mathlib
- `Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly` — minimal and characteristic polynomials.
- `Mathlib.RingTheory.Nilpotent.Basic` — nilpotent index for the shifted matrix.

## Metadata

```yaml
tags:
  - linear-algebra
  - minimal-polynomial
  - cyclic-vector
  - nonderogatory
  - prime-power
related_proofs:
  - cayley-hamilton-minpoly-oq-05-oq-01-oq-04-wip-03
  - abel-ruffini-galois-extensions-oq-10
difficulty: medium
source: proof-suggestion
created: 2026-07-04T12:34:40-07:00
```

**Significance**: 5/10
**Tractability**: 6/10
