# Problem: Unconditional sublinearity of prime gaps from Baker–Harman–Pintz

**Slug**: erdos-1138-oq-03-oq-01
**Created**: 2026-07-02
**Status**: Surveyed (scoped, not yet formalized)
**Source**: gallery-open-question (child of erdos-1138-oq-03)

## Problem Statement

### Plain Language

The parent entry `erdos-1138-oq-03` (Erdős #1138, Prime Gap Bounds) proves a chain of
unconditional and conditional bounds on the maximal prime gap `maxPrimeGap x` below `x`,
and states the Baker–Harman–Pintz (2001) bound

```
maxPrimeGap x ≤ x ^ 0.525   (for x ≥ 25)
```

as an `axiom` (`baker_harman_pintz`) — a deep unconditional analytic-number-theory result
not available in Mathlib.

**This sub-problem asks for the clean downstream corollary that needs no new deep input:**
the Baker–Harman–Pintz bound implies prime gaps are *unconditionally sublinear*, i.e.

```
maxPrimeGap x / x → 0   as x → ∞.
```

Equivalently: for every `ε > 0` there is `N` with `maxPrimeGap x ≤ ε · x` for all `x ≥ N`.
This is the unconditional analogue of the parent's *conditional* Cramér result
`cramer_implies_gap_sublinear` (which derives sublinearity from `C·(log x)²`), obtained
instead from the exponent `0.525 < 1`.

### Formal Statement

```lean
-- Target (sketch), in namespace Erdos1138OQ03:
theorem bhp_implies_gap_littleo :
    Filter.Tendsto (fun x : ℕ => (maxPrimeGap x : ℝ) / x) Filter.atTop (nhds 0)

-- and/or the ε–N form:
theorem bhp_gap_eventually_le_eps (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in Filter.atTop, (maxPrimeGap x : ℝ) ≤ ε * x
```

## Classification

```yaml
tier: C
significance: 5
tractability: 8
tags:
  - seeker-selected
  - erdos
  - prime-gaps
  - analytic-number-theory
  - asymptotics
```

**Significance**: 5/10 — a corollary, not a new theorem, but it turns the parent's
axiom into a concrete asymptotic statement (the form applications actually use) and
mirrors the existing conditional Cramér lemma.
**Tractability**: 8/10 — no deep input required; it is `x^0.525 / x = x^{-0.475} → 0`, a
pure real-analysis / `Filter.Tendsto` argument over `rpow` monotonicity, entirely within
Mathlib's asymptotics API once the axiom is invoked.

## Why This Matters

1. Converts the parent's `baker_harman_pintz` axiom from a bare inequality into the
   asymptotic statement `maxPrimeGap = o(x)` that downstream results consume.
2. Completes the symmetry with `cramer_implies_gap_sublinear` (conditional) — both
   conditional and unconditional roads now reach sublinearity.
3. Self-contained and Mathlib-reachable: no new axioms, no `native_decide`.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| erdos-1138-oq-03 (parent) | Supplies `maxPrimeGap`, `baker_harman_pintz`, and the conditional `cramer_implies_gap_sublinear` template to mirror |
| erdos-1138 / erdos-1138-oq-02 | Prime-gap formalization lineage |

## Known Results / What's Already There

- `Erdos1138OQ03.maxPrimeGap : ℕ → ℕ` and `maxPrimeGap_le : maxPrimeGap x ≤ x`.
- `axiom baker_harman_pintz (x) (hx : 25 ≤ x) : (maxPrimeGap x : ℝ) ≤ (x:ℝ) ^ (0.525:ℝ)`.
- `cramer_implies_gap_sublinear` — the conditional sublinearity proof to mirror; it already
  demonstrates the `rpow` / `ε`-manipulation style needed here.
