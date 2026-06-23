# Research State: erdos-1087-incomplete-01

## Current State
**Phase**: BLOCKED (after assessment)
**Path**: full
**Since**: 2026-05-08
**Iteration**: 1

## Blocker

The sorry in `erdos_1087_summary` is **structurally unfillable** without
reformulating the theorem statement. The theorem requires `∃ α ≥ 3, ∀ n ≥ 4, f n ≥ n^α`
but the supplying axiom `erdos_purdy_lower_bound` provides only
`∃ c > 0, ∀ n ≥ 4, f n ≥ c · n^3 · log n` — and the existential `c` may be
arbitrarily small, in which case no fixed `α ≥ 3` satisfies the summary's
lower-bound constraint. Symmetric issue for the upper bound (`∃ C > 0`
in the axiom vs `∃ β ≤ 3.5` in the summary).

See `knowledge.md` for the detailed analysis.

## Recommendation for Next Researcher / Curator

Reformulate `erdos_1087_summary` to include explicit constants:

```lean
theorem erdos_1087_summary :
    ∃ α β c' C' : ℝ, 3 ≤ α ∧ β ≤ 3.5 ∧ 0 < c' ∧ 0 < C' ∧
    (∀ n : ℕ, n ≥ 4 → (f n : ℝ) ≥ c' * n^α) ∧
    (∀ n : ℕ, n ≥ 4 → (f n : ℝ) ≤ C' * n^β) := by ...
```

Then α = 3, β = 7/2, c' = c · log 4, C' = C is provable from the axioms.

Alternatively: delete `erdos_1087_summary` (the existing `erdos_1087`
already packages the lower/upper bounds without information loss).

## Next Action

This slug should be reclassified from `incomplete-01` to a docs/restructuring
task, or referred to the curator. The current `incomplete-01` framing
("just fill the sorry") is misleading.
