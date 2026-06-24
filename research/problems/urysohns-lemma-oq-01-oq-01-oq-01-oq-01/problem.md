# Problem: Sharp Norm Equality ‖G‖ = ‖f‖ from the Sup-Norm Tietze Series

**Slug**: urysohns-lemma-oq-01-oq-01-oq-01-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Strengthen the sup-norm **bound** of the self-contained series extension to the sharp
**equality**: for $f \in C(s, \mathbb{R})$ on a closed $s \subseteq X$ ($X$ normal), with
$G = \sum_i g_i \in X \to^{b} \mathbb{R}$ the explicit Urysohn correction series of the parent,

$$
\|G\|_\infty \;=\; \|f\|_\infty .
$$

### Plain Language

The sibling proof `urysohns-lemma-oq-01-oq-01-oq-01` extends $f$ to $G$ as an explicit infinite
sum of Urysohn corrections and shows $\|G\| \le \|f\|$ up to the construction's geometric
constant. This problem asks to track the partial-sum norms carefully enough to land on the
**sharp** norm-preserving form $\|G\| = \|f\|$ — recovering the textbook statement of Tietze
("the extension can be chosen with the same sup-norm as the original") directly from the
hand-built series, rather than from Mathlib's `TietzeExtension` closure.

> **Note for the researcher (dedup):** the *companion* entry
> `urysohns-lemma-oq-01-oq-01-oq-02` already proves a norm-preserving Tietze extension, but via
> a **different** construction (a norm-preserving correction series). The point of *this*
> problem is to obtain $\|G\| = \|f\|$ from the **sup-norm construction of
> `...-oq-01-oq-01-oq-01`** by tracking its partial-sum norms — i.e. show that branch *also*
> yields equality, not just $\le$. If, on inspection, the sup-norm series cannot be made sharp
> without effectively rebuilding the companion's construction, record that and pivot to proving
> the precise constant it *does* achieve. Confirm the exact inequality the sibling currently
> states before claiming.

### Why This Matters

The sharp norm bound is the quantitatively strongest form of the Tietze extension and the one
used in applications (e.g. extending without amplifying magnitude, partitions of unity with
controlled size). Deriving it from the explicit series — tracking how the partial sums'
sup-norms behave — exposes *why* norm preservation holds at the level of the construction, which
is exactly the pedagogical content a hand-built proof is supposed to make visible. It also
completes the sup-norm branch of the Urysohn-series family so both branches reach the sharp form.

## Known Results

### What's Already Proven

- `urysohns-lemma-oq-01-oq-01-oq-01` (sibling/parent) — the self-contained sup-norm Tietze
  extension assembled as an explicit `tsum`, with a sup-norm **bound** on $G$.
- `urysohns-lemma-oq-01-oq-01-oq-02` (companion) — a norm-preserving Tietze extension
  $\|G\| = \|f\|$ via a *different*, norm-tracking correction series (reference construction).
- `urysohn_approx_step` / `urysohn_approx_iterate` (`Proofs/UrysohnsLemmaOQ01OQ01.lean`) — the
  one-step correction bounded by $M/3$ and its geometric iterate.
- Mathlib: `BoundedContinuousFunction` norm API (`norm_le`, `norm_coe_le_norm`), `tsum` norm
  bounds (`norm_tsum_le_tsum_norm`), and geometric series sums.

### What's Still Open

- Tracking the partial-sum sup-norms of the *sup-norm* construction so the limit norm equals
  $\|f\|$ exactly (matching lower bound $\|G\| \ge \|f\|$ from $G|_s = f$, and the sharp upper
  bound from the corrections).
- A clean Lean statement `tietze_sup_series_norm_eq` giving the equality.

### Our Goal

Prove `‖G‖ = ‖f‖` for the sup-norm series $G$ of `urysohns-lemma-oq-01-oq-01-oq-01`: the lower
bound from $G|_s = f$ (restriction can only shrink norm), the upper bound by tracking the
partial-sum norms / geometric corrections — without invoking `ContinuousMap.exists_restrict_eq`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| urysohns-lemma-oq-01-oq-01-oq-01 | Direct parent; supplies the sup-norm series $G$ whose norm we sharpen to equality. | Explicit `tsum` in $X\to^b\mathbb{R}$, geometric bounds |
| urysohns-lemma-oq-01-oq-01-oq-02 | Companion already achieving $\|G\|=\|f\|$ by a different construction; reference + dedup boundary. | Norm-tracking correction series |
| urysohns-lemma-oq-01-oq-01 | Engine: one-step Urysohn correction and iterate. | One-step approximation, geometric decay |

## Initial Thoughts

### Potential Approaches

1. **Approach A — two-sided squeeze**: Lower bound $\|G\| \ge \|G|_s\| = \|f\|$ from
   `norm_restrict_le` reasoning (restriction to $s$ cannot increase norm, and $G|_s = f$); upper
   bound $\|G\| \le \|f\|$ by summing the corrected partial-sum norm bounds.
   - Why it might work: the lower bound is immediate from $G|_s = f$; the upper bound reuses the
     geometric per-term estimates.
   - Risk: the sup-norm construction's corrections may only give $\|G\| \le c\,\|f\|$ with
     $c > 1$ unless the step is the norm-preserving variant — this is the crux to check first.

2. **Approach B — import the companion's norm bookkeeping**: Adapt the partial-sum norm
   tracking from `...-oq-01-oq-01-oq-02` into this branch.
   - Why it might work: reuses a proven technique.
   - Risk: may collapse into the companion (dedup concern) — only pursue if it genuinely
     sharpens *this* construction.

### Key Difficulties

- Establishing the upper bound $\|G\| \le \|f\|$ exactly (constant $1$) for the sup-norm series.
- Avoiding duplication of the companion entry's already-proven equality.

### What Would a Proof Need?

- Key lemma 1: $\|G\| \ge \|f\|$ from $G|_s = f$ and restriction-shrinks-norm.
- Key lemma 2: partial-sum sup-norm bound that sums to $\le \|f\|$ in the limit.
- Technical requirements: `BoundedContinuousFunction.norm_le`, `norm_tsum_le_tsum_norm`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Reuses an existing series and the companion as a template for the norm-preserving argument.
- The lower bound is immediate; the upper bound is a controlled geometric sum.
- Main risk is conceptual (dedup vs. companion), not technical.

**Estimated Effort**:
- Exploration: a few hours to confirm the sibling's exact current bound and the crux constant.
- Formalization: about one day if the sup-norm step is sharpenable to constant $1$.
