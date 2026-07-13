# Problem: Brouwer Fixed-Point Theorem via Sperner Coloring on [0,1]^n

**Slug**: sperner-simplicial-instance-oq-04
**Created**: 2026-07-02
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Build a Brouwer-fixed-point theorem on top of the 1-d Sperner lemma
(`interval_sperner`). Combine it with a barycentric-mesh refinement and a
continuous-coloring → Sperner-coloring reduction. The near-term, tractable target
is the **continuous 1-d intermediate value theorem** obtained from the *discrete*
sign-change theorem:

For continuous $f : [0,1] \to [-1,1]$ with $f(0) \le 0 \le f(1)$, there exists
$x_0 \in [0,1]$ with $f(x_0) = 0$, derived as the mesh limit $m \to \infty$ of the
discrete sign-change cells $\{i/m, (i+1)/m\}$ where $f(i/m) \le 0 < f((i+1)/m)$,
so that $|f(x_0)| \to 0$.

### Plain Language

The 1-d Sperner lemma already gives, for any coloring of a subdivided interval with
different colors at the two ends, a "panchromatic" cell where the color changes. If
we color grid points by the sign of $f$, that panchromatic cell is exactly a
sign-change interval. Refining the mesh and taking a convergent subsequence
(Bolzano–Weierstrass) pins down a genuine root — the continuous IVT — purely from the
discrete combinatorial lemma. Iterating the same idea in $n$ dimensions (via
barycentric subdivision and `sperner-ndim`) yields Brouwer's theorem.

### Why This Matters

This closes the loop from the gallery's Sperner infrastructure to a headline
consequence (IVT, then Brouwer) using only combinatorics + a compactness argument —
no analytic fixed-point machinery. It is a clean, self-contained demonstration that
the discrete Sperner lemma *implies* continuous existence theorems.

## Known Results

### What's Already Proven (prior sessions — see knowledge.md)

- **Part (a) DONE** — `proofs/Proofs/SpernerSimplicialInstanceOQ04.lean` (no `sorry`,
  no `axiom`): the continuous-coloring → Sperner-coloring reduction.
  - `signColoring f m j = if f (j/m) ≤ 0 then 0 else 1`, with endpoint lemmas
    `signColoring_zero` / `signColoring_self`.
  - `exists_sign_change_cell`: for every mesh $m > 0$ there is a cell $i : \mathrm{Fin}\,m$
    whose endpoints straddle a sign change of $f$ (via
    `OQ05Scarf1d.discrete_ivt_panchromatic_cell`).
  - `exists_sign_change_bracket`: product form $f(a)\cdot f(b) \le 0$.
- **Sibling `...-oq-05`** (`SpernerSimplicialInstanceOQ05Scarf1d.lean`): the discrete
  IVT `discrete_ivt_panchromatic_cell` itself. oq-04 is distinct — it adds the
  real-function reduction layer, not the combinatorics.
- Numerical certificate `verify_sperner_oq04_bridge.py`: sign-change cell brackets a
  true root for all meshes $m \in \{1,\dots,65536\}$ on 3 test functions.

### What's Still Open

- **Part (b) — OPEN, tractable (~150 lines)**: the continuous 1-d IVT via mesh
  refinement + Bolzano–Weierstrass, promoting `exists_sign_change_cell` to a genuine
  root $f(x_0) = 0$. **This is the target of this problem.**
- Part (c) — $n$-d Brouwer via barycentric subdivision + `sperner-ndim`: BLOCKED
  (>1000 lines), out of scope here.

### Our Goal

Complete **part (b)**: prove the continuous 1-d IVT from the already-proven discrete
sign-change cells. Leave part (c) ($n$-d Brouwer) for a follow-up.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| sperner-simplicial-instance | Parent; 1-d Sperner / `interval_sperner` | Simplicial combinatorics |
| sperner-simplicial-instance-oq-05 | Supplies `discrete_ivt_panchromatic_cell` | Discrete IVT |
| sperner-ndim | Needed only for part (c) ($n$-d) | Barycentric subdivision |

## Initial Thoughts

### Potential Approaches

1. **Mesh refinement + Bolzano–Weierstrass**: Take mesh $m = 2^k$, extract the
   sign-change cell $x_k = i_k/m$. The sequence $(x_k)$ lives in compact $[0,1]$; a
   convergent subsequence $x_{k_j} \to x_0$ has $f(x_{k_j}) \le 0 < f(x_{k_j} + 1/m)$,
   and continuity forces $f(x_0) = 0$.
   - Why it might work: `exists_sign_change_cell` already provides the cells; Mathlib
     has sequential compactness of `[0,1]` and continuity lemmas.
   - Risk: index bookkeeping for the subsequence and the two straddling endpoints.

### Key Difficulties

- Managing the two endpoint sequences ($x_k$ and $x_k + 1/m$) converging to the same
  limit and passing continuity through the inequality.

### What Would a Proof Need?

- Sequential compactness of `[0,1]` (`IsCompact.tendsto_subseq` / `Bolzano–Weierstrass`).
- Continuity of $f$ to pass to the limit in $f(x_k) \le 0 \le f(x_k')$.
- The existing `exists_sign_change_cell` as the discrete input.

## Tractability Assessment

**Difficulty**: Medium (part (b) only)

**Justification**:
- Part (a) is already complete and builds without `sorry`/`axiom`.
- Part (b) is a standard compactness/continuity argument (~150 lines) with all
  prerequisites in Mathlib.
- Part (c) is deliberately out of scope.

**Estimated Effort**:
- Exploration: hours (context already gathered)
- If tractable: days

## References

### Papers
- Sperner (1928); Scarf (1967) — combinatorial fixed-point methods.

### Mathlib
- `IsCompact`, `tendsto_subseq`, `Continuous` — compactness + limit passing.

## Metadata

```yaml
tags:
  - combinatorics
  - sperner-lemma
  - topology
  - brouwer
  - intermediate-value-theorem
related_proofs:
  - sperner-simplicial-instance
  - sperner-simplicial-instance-oq-05
difficulty: medium
source: proof-suggestion
created: 2026-07-02
```

**Significance**: 7/10
**Tractability**: 5/10
