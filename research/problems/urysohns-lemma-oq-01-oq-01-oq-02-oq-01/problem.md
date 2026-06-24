# Problem: Banach-Space-Valued Norm-Preserving Tietze via the Explicit Urysohn Series

**Slug**: urysohns-lemma-oq-01-oq-01-oq-02-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

For a normal space $X$, closed $s \subseteq X$, and a finite-dimensional (or interval-valued)
target — concretely $f \in C(s, \mathbb{R}^d)$ componentwise, or $f \in C(s, [a,b])$ —

$$
\exists\, G \in C(X, V)\ \text{with}\ G|_s = f \ \text{and}\ \|G\|_\infty = \|f\|_\infty ,
$$

obtained by running the explicit Urysohn correction series of the parent in each coordinate of
the value space $V$.

### Plain Language

The parent (`urysohns-lemma-oq-01-oq-01-oq-02`) gives a *norm-preserving* Tietze extension for
**real-valued** data, assembled as an explicit geometric series of Urysohn corrections. This
problem asks whether that exact construction carries through when the function takes values in
something richer than $\mathbb{R}$ — first the concrete finite-dimensional case $\mathbb{R}^d$
(extend each coordinate, control the joint norm), and the interval-constrained case $[a,b]$
(extend without leaving the interval). The geometric majorant and Banach-space completeness
argument should survive verbatim; the new content is a *vector-valued Urysohn correction step*
and the bookkeeping that keeps the sup-norm sharp, $\|G\| = \|f\|$.

### Why This Matters

Real-valued Tietze is the base case; the genuinely useful statements in analysis are
vector-valued (extending maps into $\mathbb{R}^d$, into Banach spaces, or into a fixed interval
without overshoot). Showing the *explicit-series* construction — not Mathlib's black-box
closed-embedding routine — generalizes cleanly demonstrates that the hand-built engine is
robust, not an artifact of the scalar case. It also produces reusable infrastructure (a
vector-valued one-step correction) that downstream extension and approximation results can
build on, and it keeps the norm-preservation that the scalar parent worked hard to establish.

## Known Results

### What's Already Proven

- `urysohns-lemma-oq-01-oq-01-oq-02` (parent) — the **scalar** norm-preserving Tietze extension
  built as an explicit `tsum` of corrections, with $\|G\| = \|f\|$.
- `urysohn_approx_step` / `urysohn_approx_iterate` (`Proofs/UrysohnsLemmaOQ01OQ01.lean`) — the
  scalar one-step correction and its geometric iterate.
- Mathlib: `BoundedContinuousFunction` into a complete normed space is complete; componentwise
  continuity for $\mathbb{R}^d$ (`continuous_pi` / `continuous_apply`), and the interval-valued
  Tietze data via `Set.Icc` membership are all available.

### What's Still Open

- A vector-valued Urysohn correction step: given $f$ valued in $\mathbb{R}^d$ (resp. $[a,b]$),
  produce a single global correction reducing the residual by the same $2/3$ factor while
  respecting the value constraint.
- Assembling the per-coordinate series into one $V$-valued extension and proving the joint
  sup-norm is preserved (not merely bounded coordinatewise).

### Our Goal

State and prove a Lean theorem extending the parent to $V \in \{\mathbb{R}^d, [a,b]\}$:
$G|_s = f$ with $\|G\| = \|f\|$, reusing the scalar engine in each coordinate and avoiding
`ContinuousMap.exists_restrict_eq`. The $\mathbb{R}^d$ case is the primary deliverable; the
interval case is a stretch goal.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| urysohns-lemma-oq-01-oq-01-oq-02 | Scalar parent; the construction this problem lifts to vector-valued data. | Explicit `tsum`, geometric bounds, norm preservation |
| urysohns-lemma-oq-01-oq-01-oq-01 | Sibling self-contained scalar extension (sup-norm form). | `tsum` in $X\to^b\mathbb{R}$, completeness |
| urysohns-lemma-oq-01-oq-01 | Engine providing the one-step correction to be vectorized. | One-step Urysohn approximation |

## Initial Thoughts

### Potential Approaches

1. **Approach A — coordinatewise reduction for $\mathbb{R}^d$**: Extend each component $f_j$ by
   the scalar parent, set $G = (G_1, \dots, G_d)$. Continuity is `continuous_pi`; the residual
   shrinks by $2/3$ in each coordinate.
   - Why it might work: $\mathbb{R}^d$ separates into scalars, reusing the whole engine.
   - Risk: the joint sup-norm $\|G\|=\max_j\|G_j\|$ may only give $\|G\|=\|f\|$ if the maximizing
     coordinate is handled carefully; coordinatewise norm preservation need not give joint
     preservation without an argument.

2. **Approach B — genuine vector-valued one-step lemma**: Replace `urysohn_approx_step` with a
   $V$-valued version using a single scalar Urysohn function as a multiplier toward the value.
   - Why it might work: keeps one series rather than $d$, easing the norm bookkeeping.
   - Risk: constructing the vector-valued step in Mathlib without a ready-made lemma.

### Key Difficulties

- Joint sup-norm preservation for $\mathbb{R}^d$ (vs. merely coordinatewise bounds).
- The interval case must keep values in $[a,b]$ throughout the iteration (clamping vs. sharpness).

### What Would a Proof Need?

- Key lemma 1: scalar parent extension, applied per coordinate.
- Key lemma 2: $\|(G_1,\dots,G_d)\|_\infty$ control in terms of the $\|G_j\|$ and $\|f_j\|$.
- Technical requirements: `continuous_pi`, `Pi.norm` / `pi_norm_le`, `Set.Icc` membership for the
  interval variant.

## Tractability Assessment

**Difficulty**: Medium-High

**Justification**:
- The $\mathbb{R}^d$ coordinatewise route is mostly engineering over the proven scalar parent.
- Sharp joint norm preservation and the interval-valued variant add genuine new content.
- Mathlib has the product-space continuity and norm APIs needed for the finite-dimensional case.

**Estimated Effort**:
- Exploration: about one day to scope the vector step and norm bookkeeping.
- Formalization: a few days for the $\mathbb{R}^d$ case with sharp norm preservation.
