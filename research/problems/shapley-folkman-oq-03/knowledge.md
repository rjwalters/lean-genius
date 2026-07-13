# Knowledge Base: shapley-folkman-oq-03

Insights accumulated during research on this problem.

---

## Problem Understanding

**Goal**: Formalize the Starr (1969) quantitative bound on non-convexity in large
economies — extending the existing `ShapleyFolkman.lean` to the economic application.

**Status**: COMPLETE (2026-04-24) — Both ShapleyFolkman.lean (0 sorries) and
ShapleyFolkmanOQ03.lean (0 sorries) are fully proved. Gallery entry updated to `verified`.

---

## Session 2026-04-24 (Session 1) — Completion and Gallery Update

**Mode**: FRESH (claiming available problem)
**Outcome**: COMPLETED — problem was already solved, parent sorry resolved

### What I Did

1. Confirmed ShapleyFolkmanOQ03.lean (204 lines) is fully proved with 0 sorries.
2. Confirmed parent ShapleyFolkman.lean (1238 lines) now has 0 sorries (completed by
   researcher-11 in Session 10, 2026-04-24, via WF induction on total minCaraDepth).
3. Updated gallery meta.json for both proofs:
   - `shapley-folkman`: badge "wip" → "verified", sorries 1 → 0, status "formalized" → "verified"
   - `shapley-folkman-oq-03`: badge "wip" → "verified", status "formalized" → "verified",
     assumptions updated to remove transitive sorry note
4. Updated candidate pool: marked as "completed".

### Key Findings

The OQ-03 proof was written assuming the parent would resolve its 1 sorry. That resolution
happened in the same branch (`research/shapley-folkman-complete`), completing the full chain:
- `ShapleyFolkman.lean` → `sum_close_to_convexHull` (Shapley-Folkman decomposition)
- `ShapleyFolkmanOQ03.lean` → `shapley_folkman_starr` (Starr norm bound) + `large_economy_near_convex`

### Files Modified

- `src/data/proofs/shapley-folkman/meta.json`: status/badge/sorries updated
- `src/data/proofs/shapley-folkman-oq-03/meta.json`: status/badge updated, assumptions and cross-refs updated
- `research/problems/shapley-folkman-oq-03/state.md`: phase → COMPLETED

---

## Original Problem Understanding

### Current State of ShapleyFolkman.lean (1238 lines after Session 10)

The base proof has **0 sorries** — all proofs complete, including the WF descent
step in `reduce_excess_by_one` via WF induction on total `minCaraDepth`.

The file already contains economic application theorems that are **fully proved**:
- `sum_close_to_convexHull`: every point in conv(∑ Sᵢ) has a decomposition with
  at most `d = finrank ℝ E` components outside their original sets
- `repeated_sum_nearly_convex`: for n-fold Minkowski sum, excess ≤ d regardless of n

### What OQ-03 Adds: Starr Norm Bound

These existing theorems give a **counting bound** (≤ d non-convex components).
The Starr bound gives a **metric bound**: for an exchange economy with N agents in ℝ^d,

```
∥z - z*∥ ≤ √d · max_i diam(co(Aᵢ) \ Aᵢ)
```

where z* is the convexified optimum and z is the actual feasible allocation.

**The key missing theorem** (Starr 1969, Lemma 1):
```lean
theorem starr_norm_bound [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
    {ι : Type*} [DecidableEq ι] {S : ι → Set E} {t : Finset ι}
    (hne : ∀ i ∈ t, (S i).Nonempty)
    {x : E} (hx : x ∈ convexHull ℝ (∑ i in t, S i)) :
    ∃ y : E, y ∈ ∑ i in t, S i ∧
      ‖x - y‖ ≤ Real.sqrt (Module.finrank ℝ E) *
        (t.sup' ⟨_, ‹_›⟩ (fun i => Metric.diam (convexHull ℝ (S i)))) := by
  sorry
```

This requires: an InnerProductSpace structure (normed Euclidean space), a diameter
bound on each convexified set, and the Shapley-Folkman decomposition.

### Proof Strategy

1. Use `sum_close_to_convexHull` to get decomposition f with ≤ d excess components
2. For each excess component i, replace f i ∈ conv(Sᵢ) with any point in Sᵢ (using
   Carathéodory): cost ≤ diam(conv(Sᵢ))
3. Norm of the replacement: ‖f i - g i‖ ≤ diam(conv(Sᵢ)) for each swapped index
4. Total norm: ‖∑_excess (f i - g i)‖ ≤ √(|excess|) · max diam ≤ √d · max diam
   (Cauchy-Schwarz on the finite sum)

### Key Lean Requirements

- `InnerProductSpace ℝ E` for ‖·‖ norm
- `Real.sqrt` monotonicity and `Real.sqrt_le_sqrt`
- `Finset.inner_mul_le_norm_mul_iff` (Cauchy-Schwarz)
- `Metric.diam_le_iff` for diameter bounds
- Already proved: `repeated_sum_nearly_convex` gives ≤ d excess components

---

## Insights

### The 1 Remaining Sorry

The sorry at line 704 (Case B of `reduce_excess_by_one`) is about WF descent.
The comment describes the proof strategy clearly — it just needs implementation:

```lean
-- Full proof: WF induction on N = Σ_{j excess} (Carathéodory vertex count of D.point j),
-- using a DecoratedDecomp structure that carries explicit vertex/weight data per index.
-- Each perturbation step: Case A exits excess; Case B decreases N by 1. N ≥ 2*(d+1).
```

This sorry is **Aristotle-eligible** (theorem sorry, not def sorry). Try Aristotle
submission first.

### Economic Interpretation

- `repeated_sum_nearly_convex` formalizes the key insight: in a large economy (n agents),
  the "non-convexity" is bounded by d (dimension), not n (agent count). This is the
  mathematical foundation of Starr's theorem.
- The norm bound refines this to a metric statement useful for approximation guarantees
  in mechanism design and competitive equilibrium theory.

### Connection to Mathlib

No existing Mathlib theorem directly gives the Starr norm bound, but all components
are available:
- `inner_mul_le_norm_sq_mul_norm_sq` (Cauchy-Schwarz variant)
- `Finset.norm_sum_le` (triangle inequality for finite sums)
- `Metric.diam` API in `Mathlib.Topology.MetricSpace.Basic`

---

## Dead Ends

[Approaches known not to work will be documented here]
