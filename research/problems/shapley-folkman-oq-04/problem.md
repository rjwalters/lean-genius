# Problem: Shapley-Folkman Refined: Excess Bounded by the Number of Non-Convex Summands

**Slug**: shapley-folkman-oq-04
**Created**: 2026-06-30
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: shapley-folkman

## Problem Statement

### Formal Statement

$$
\mathrm{excessIndices}(D)\subseteq \{i\in t : \neg\,\mathrm{Convex}\,\mathbb{R}\,(S\,i)\};\quad |\mathrm{excessIndices}\,D| \le \min\big(\dim_\mathbb{R} E,\ |\{i\in t : \neg\mathrm{Convex}\,(S i)\}|\big)
$$

### Plain Language

The parent bounds the number of convexified summands by finrank ℝ E, independent of which sets are convex. But a convex S_i never needs convexification. Show the excess indices are contained in the non-convex indices, yielding the sharper bound excessIndices.card ≤ min(finrank ℝ E, #{i ∈ t : ¬Convex (S i)}). When only k of N ≫ k summands are non-convex, excess is bounded by k, not by dimension.

### Why This Matters

A standard, genuinely useful sharpening: the dimension bound is loose when few summands are non-convex, yet economically the truly non-convex agents are what matter. The core inclusion is a one-lemma consequence of Convex.convexHull_eq and reuses the parent's Decomposition/excessIndices directly.

## Known Results

### What's Already Proven

- Parent entry `shapley-folkman` is verified (0-axiom) in the gallery and supplies the base result this question extends.
- All Mathlib lemmas listed under References below were grep-confirmed to exist in the pinned Mathlib.

### What's Still Open

- The specific target theorems sketched below (currently `sorry`).

### Our Goal

Prove the target sketch below as a self-contained, verified (0-axiom) child of `shapley-folkman`. Category: **extension**.

## Target Lean Sketch

```lean
import Proofs.ShapleyFolkman
open ShapleyFolkman
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem excessIndices_subset_nonConvex {ι} {S : ι → Set E} {t : Finset ι} {x : E}
    (D : Decomposition S t x) :
    D.excessIndices ⊆ t.filter (fun i => ¬ Convex ℝ (S i)) := by sorry

theorem shapley_folkman_nonConvex_bound [FiniteDimensional ℝ E]
    {ι} {S : ι → Set E} {t : Finset ι} {x : E} (D : Decomposition S t x) :
    D.excessIndices.card
      ≤ min (Module.finrank ℝ E) (t.filter (fun i => ¬ Convex ℝ (S i))).card := by sorry
```

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `shapley-folkman` | Parent: Shapley-Folkman lemma, excess bounded by dimension | convex hull, Carathéodory, Minkowski sum |
| `shapley-folkman-oq-03` | Sibling | convexification bounds |

## Tractability Assessment

**Difficulty**: Low

**Significance**: 6/10  |  **Tractability**: 8/10  |  **Tier**: B

**Justification**: The required Mathlib primitives exist and the proof mirrors the parent's style; the sketch reduces to assembling named lemmas.

### Suggested First Steps

1. Prove excessIndices_subset_nonConvex: take i ∈ excessIndices (i ∈ t, point i ∉ S i); by contradiction if Convex ℝ (S i) then Convex.convexHull_eq rewrites mem_convexHull to point i ∈ S i — contradiction. Membership via Finset.mem_filter.
2. Get excessIndices.card ≤ (t.filter ¬Convex).card via Finset.card_le_card.
3. Combine with parent shapley_folkman (card ≤ finrank) using le_min; add a corollary example (k non-convex among N ⇒ excess ≤ k).

## References

### Mathlib

- `Convex.convexHull_eq` — Analysis/Convex/Hull.lean (Convex ℝ s → convexHull ℝ s = s)
- `subset_convexHull` — Analysis/Convex/Hull.lean
- parent `shapley_folkman` (Decomposition → excessIndices.card ≤ finrank) — proofs/Proofs/ShapleyFolkman.lean
- `Finset.filter`, `Finset.card_le_card`, `le_min` — core/Mathlib

## Metadata

```yaml
tags:
  - convex-analysis
  - combinatorics
  - minkowski-sum
  - economics
  - caratheodory
related_proofs:
  - shapley-folkman
  - shapley-folkman-oq-03
difficulty: low
source: proof-suggestion
created: 2026-06-30
```
