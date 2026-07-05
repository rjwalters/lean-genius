# Problem: Muirhead's Inequality as a Generalization of Maclaurin

**Slug**: amgm-inequality-oq-02-oq-02-oq-03
**Created**: 2026-07-04
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For nonnegative reals $x_1,\dots,x_n$ and exponent vectors $\alpha \succ \beta$
(majorization, with equal sums), the symmetrized power sums satisfy

$$
\sum_{\sigma \in S_n} \prod_{i=1}^{n} x_{\sigma(i)}^{\alpha_i} \;\ge\; \sum_{\sigma \in S_n} \prod_{i=1}^{n} x_{\sigma(i)}^{\beta_i}.
$$

### Plain Language

Muirhead's inequality (Hardy–Littlewood–Pólya, *Inequalities* 1934, §2.18) says:
if one exponent vector *majorizes* another (same total, but more "spread out"), then
the corresponding symmetric power-sum function is larger for all nonnegative inputs.
The gallery's `amgm-inequality` chain (AM–GM, Newton, Maclaurin) is the special case
obtained by comparing exponent vectors like $(1,1,\dots,1,0,\dots,0)$ against
$(1,0,\dots,0)$. The task is to formalize Muirhead and recover Maclaurin/AM–GM as
instances.

### Why This Matters

Muirhead is the master symmetric-mean inequality: AM–GM, Maclaurin, and Newton's
inequalities all fall out of it via specific majorization comparisons. A Lean
formalization would unify the gallery's inequality entries under one theorem and
introduce the majorization order as a reusable tool.

## Known Results

### What's Already Proven

- `amgm-inequality` (gallery) — AM–GM and the Maclaurin/Newton chain.
- Mathlib has `MeanInequalities` (AM–GM, Young, Hölder) and some majorization
  material (`Mathlib.Order.Majorization` / `Finset` doubly-stochastic tools).

### What's Still Open

- A Lean statement and proof of Muirhead in terms of the majorization order on
  exponent vectors, plus the derivation of Maclaurin as a corollary.
- Whether Mathlib's convexity / doubly-stochastic-matrix (Birkhoff) API is enough to
  reach Muirhead via the standard "average over transfers" (Hardy–Littlewood–Pólya) proof.

### Our Goal

Formalize Muirhead's inequality (at least for the symmetrized-monomial form) and
show it implies the existing Maclaurin/AM–GM gallery results.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| amgm-inequality | Parent; the special cases Muirhead generalizes | AM–GM, Newton, Maclaurin, symmetric polynomials |

## Initial Thoughts

### Potential Approaches

1. **Approach A — majorization + Birkhoff/HLP transfers**: use the classical proof
   that $\alpha \succ \beta$ iff $\beta = D\alpha$ for a doubly stochastic $D$, then
   average the symmetrized monomials over the transfer.
   - Why it might work: it is the standard textbook proof; Mathlib has convexity and
     some doubly-stochastic infrastructure.
   - Risk: assembling the Birkhoff–von Neumann / transfer step in Lean may be heavy.

2. **Approach B — direct "SOS by transfers" induction on the majorization poset**:
   reduce a single Robin-Hood transfer $\alpha \to \alpha'$ and iterate.
   - Why it might work: each elementary transfer is an AM–GM-style two-variable step.
   - Risk: managing the symmetric-sum reindexing and the induction on majorization steps.

### Key Difficulties

- Encoding majorization on exponent vectors and the elementary "transfer" step in Lean.
- Symmetric-sum reindexing over `S_n` and keeping the bookkeeping tractable.

### What Would a Proof Need?

- Key lemma 1: single-transfer inequality (a two-exponent Robin-Hood step increases the symmetrized sum).
- Key lemma 2: any $\alpha \succ \beta$ decomposes into finitely many such transfers.
- Technical requirements: `Mathlib.Analysis.MeanInequalities`, majorization/convexity API.

## Tractability Assessment

**Difficulty**: Medium–High

**Justification**:
- The full Muirhead theorem is a genuine formalization effort; the transfer lemma is
  approachable but the majorization-decomposition step is nontrivial in Lean.
- Similar solved problems: AM–GM and Maclaurin are already in the gallery, giving a target
  and reusable sub-lemmas.

**Estimated Effort**:
- Exploration: 1–2 days
- If tractable: 1–2 weeks (full Muirhead); a restricted symmetric-monomial form sooner
- If hard: unknown

## References

### Papers
- Hardy, Littlewood, Pólya, *Inequalities* (1934), §2.18 — Muirhead's theorem.
- Marshall, Olkin, Arnold, *Inequalities: Theory of Majorization and Its Applications*.

### Online Resources
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/MeanInequalities.html — mean inequalities in Mathlib.

### Mathlib
- `Mathlib.Analysis.MeanInequalities` — AM–GM, Young, Hölder.
- `Mathlib.Order.Majorization` / doubly-stochastic tooling — majorization order.

## Metadata

```yaml
tags:
  - inequalities
  - symmetric-polynomials
  - majorization
  - muirhead
  - am-gm
related_proofs:
  - amgm-inequality
difficulty: high
source: gallery-gap
created: 2026-07-04
```

**Significance**: 6/10
**Tractability**: 5/10
