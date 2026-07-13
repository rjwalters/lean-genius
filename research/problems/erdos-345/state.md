# Current State

**Phase**: REFINEMENT
**Since**: 2026-04-28T00:00:00Z
**Iteration**: 2

## Current Focus

Convention/consistency fix on the formalization. The conjecture itself
remains open and is not amenable to direct Lean attack — the relevant
threshold values are computed by exhaustive search and grow rapidly.

## Active Approach

Audit the existing formalization for internal consistency. Found and
fixed a convention mismatch:

- `IsCompleteSeq A := ∃ m, ∀ n ≥ m, n ∈ subsetSums A` defines
  `threshold` as the **least m** such that all n ≥ m are representable.
- Under this convention, `threshold (powerSeq 2) = 129` (largest
  non-representable is 128, so all n ≥ 129 are representable). The
  axiom correctly stated 129.
- But `threshold_cubes`/`threshold_fourth`/`threshold_fifth` axiomatized
  the OEIS A001661 values 12758, 5134240, 67898771 — these are largest
  non-representables, NOT the least-m thresholds.
- Fixed: cubes → 12759, fourth → 5134241, fifth → 67898772.
- Updated meta.json + annotations.json with corrected values and added
  explicit cross-reference to OEIS A001661 to disambiguate the
  conventions for future readers.

## Blockers

The substantive conjecture (existence of infinitely many threshold
reversals) is intractable. `T(n^k)` for `k ≥ 6` is computationally
infeasible — `T(n^5)` already required searching ~6.8 × 10⁷ integers
— and no known analytic technique distinguishes power sequences
`{n^k}` for which `{n^{k+1}}` has a smaller threshold.

## Next Action

Sub-claims that may be Lean-tractable:

1. Structural lemma: under our `IsCompleteSeq` convention,
   `threshold A = (sup of non-representable integers in A) + 1` — a
   characterization that could replace the five point-value axioms
   with one parameterized witness axiom.
2. Reduce `threshold_squares`/`cubes`/`fourth`/`fifth` to a single
   `threshold_powerSeq_known (k) (h : k ∈ {2,3,4,5}) : ...` axiom.
3. Replace `powerSeq_complete` (current Waring axiom) by importing
   Mathlib's Waring result if/when it lands.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (convention audit + fix)
