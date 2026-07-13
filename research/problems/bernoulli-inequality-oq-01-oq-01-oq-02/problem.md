# Problem: A General "Line Escapes a Bounded Power" Lemma

**Slug**: bernoulli-inequality-oq-01-oq-01-oq-02
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The parent established strict Bernoulli on Mathlib's weak domain `−2 ≤ a` and analyzed the
endpoint behaviour on `−2 ≤ a ≤ −1`. The reusable abstraction sought here is, informally:

$$
\text{If } f : \mathbb{N} \to \mathbb{R} \text{ is bounded on a window } |f(n)| \le M
\text{ but the affine quantity } 1 + n a \text{ is unbounded in } n,
$$
$$
\text{then } 1 + n a \le f(n) \text{ fails for all sufficiently large } n.
$$

Concretely: a linear-in-`n` lower bound `1 + n·a` (with `a ≠ 0`) eventually escapes any
quantity that stays bounded, so endpoint/sign arguments of the Bernoulli kind reduce to a
single "line beats a bounded power" lemma rather than ad hoc per-`n` size estimates.

### Plain Language

The parent's proof on `−2 ≤ a ≤ −1` used a size argument: the line `1 + n a` grows (in
absolute value) faster than something that is trapped in a bounded range, so the inequality
must break for large `n`. We want to extract that argument once, as a clean general lemma, so
that it can be reused for other truncated binomial / power-bound estimates instead of being
re-derived each time.

### Why This Matters

It turns a one-off estimate into a named, reusable tool. Several gallery entries
(Bernoulli endpoints, truncated binomial bounds, alternating tail bounds) repeat the same
"unbounded affine term overtakes a bounded term" pattern; a single lemma documents the idea
and shortens future proofs.

## Known Results

### What's Already Proven

- `bernoulli-inequality-oq-01-oq-01` — Strict Bernoulli on `−2 ≤ a`, with endpoint analysis on `−2 ≤ a ≤ −1` (verified, 0-axiom).
- `bernoulli-inequality-oq-01` and `bernoulli-inequality` — base Bernoulli results.
- Mathlib: `Filter.Tendsto.atTop`/`atBot` for affine maps, `exists_nat_gt`, `Archimedean` facts.

### What's Still Open

- A standalone lemma stating "an affine `n ↦ 1 + n a` with `a ≠ 0` eventually exceeds any uniformly bounded `f`" and its mirror for lower bounds.
- A demonstration that the parent's `−2 ≤ a ≤ −1` endpoint argument factors through it.

### Our Goal

State and prove the general escape lemma (both `atTop` and `atBot` directions), then refactor
or re-derive the parent's endpoint conclusion as a corollary, confirming the abstraction is
faithful.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| bernoulli-inequality-oq-01-oq-01 | Parent: source of the size argument | strict Bernoulli, endpoint analysis |
| bernoulli-inequality-oq-01 | Bernoulli on the weak domain | induction, real inequalities |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Archimedean escape**: For `a ≠ 0` and any bound `M`, use `exists_nat_gt`
   to pick `n` with `n·|a| > M + 1`, contradicting `1 + n a ≤ f(n)` with `|f(n)| ≤ M`.
   - Why it might work: elementary, no filters needed; matches the parent's flavour.
   - Risk: handling the sign of `a` (atTop vs atBot) in one statement.

2. **Approach B — filter formulation**: Phrase as `Tendsto (fun n => 1 + n*a) atTop atTop`
   (for `a > 0`) and conclude eventual strict inequality via `Filter.eventually`.
   - Why it might work: composes with Mathlib's order-filter API.
   - Risk: more machinery than the result needs; sign casework still required.

### Key Difficulties

- Choosing a statement general enough to be reusable but specific enough to discharge the
  parent's endpoint claim without contortion.
- Sign handling: the line escapes upward for `a > 0` and downward for `a < 0`.

### What Would a Proof Need?

- Key lemma 1: `∀ M, ∃ N, ∀ n ≥ N, M < n * |a|` for `a ≠ 0` (Archimedean).
- Key lemma 2: bridge from the abstract escape to the concrete `1 + n a ≤ (1+a)^n` failure.
- Technical requirements: `abs`, `exists_nat_gt`, basic ordered-field arithmetic.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The underlying estimate is already proven in the parent; this is a packaging/refactor task.
- Archimedean and filter tooling in Mathlib make the abstract lemma routine.
- The risk is design (statement shape), not mathematical depth.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–2 days
- If hard: a few days if the abstraction needs iteration

## References

### Mathlib
- `Mathlib.Algebra.Order.Archimedean` — `exists_nat_gt`, Archimedean lemmas.
- `Mathlib.Order.Filter.AtTopBot` — eventual inequality formulation (if Approach B).

## Metadata

```yaml
tags:
  - analysis
  - inequality
  - real-analysis
related_proofs:
  - bernoulli-inequality-oq-01-oq-01
  - bernoulli-inequality-oq-01
difficulty: medium
source: gallery-gap
created: 2026-06-24
```
