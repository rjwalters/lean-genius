# Session 2026-07-24 — S3-A ACT: Lyapunov convexity in dimension one (researcher-2)

## Outcome

**S3-A COMPLETE.** New file `proofs/Proofs/ShapleyFolkmanOQ01Lyapunov.lean`
(246 lines, 0 sorries, 0 axioms — `#print axioms` on all five capstone
theorems shows only `propext`/`Classical.choice`/`Quot.sound`; host-verified
with `lake env lean` on v4.31.0).

This is the first rung of the S3 positive programme. The prior blocker read
"Lyapunov's convexity theorem is not in Mathlib" — this session discharges
the `d = 1` case in-repo and sharpens the blocker to "general-measurable-space
Sierpiński exhaustion (S3-B) + ℝᵈ induction (S3-C)".

## What was proved

| Declaration | Content |
|---|---|
| `monotone_measure_inter_Iic` | `t ↦ μ (s ∩ Iic t)` monotone |
| `continuous_measure_inter_Iic` | …and continuous for `[NoAtoms μ]`, `s` measurable, `μ s ≠ ∞` |
| `exists_subset_measure_eq` | **Sierpiński 1922 on ℝ**: `r ≤ μ s → ∃ t ⊆ s` measurable, `μ t = r` |
| `setOf_measure_subset_eq_Icc` | value range `= Icc 0 (μ s)` (ℝ≥0∞ form) |
| `lyapunov_range_eq_Icc` | real form: range of `(μ ·).toReal` `= Icc 0 (μ s).toReal` |
| `lyapunov_range_convex` / `lyapunov_range_isCompact` | **d = 1 Lyapunov**: range convex and compact |
| `exists_subset_unitInterval_volume_eq` | non-vacuity: Lebesgue on `[0,1]` attains every `r ≤ 1` |

## Mechanism (route label: cumulative-slice IVT)

Witnesses are initial slices `s ∩ Iic x`. Left-continuity of the cumulative
function IS atomlessness (`Iio_ae_eq_Iic`); right-continuity is continuity
from above (`tendsto_measure_iInter_atTop`, needs `μ s ≠ ∞`). Limits at ±∞
via `tendsto_measure_iInter_atBot` / `tendsto_measure_iUnion_atTop` with
`ι := ℝ`. Exact level attained by `mem_range_of_exists_le_of_exists_ge`
(IVT on the preconnected space ℝ, codomain ℝ≥0∞ — `OrderClosedTopology`
suffices). No exhaustion/Zorn argument needed on ℝ.

## Key API discoveries

- Mathlib has NO Sierpiński theorem (only `exists_subset_measure_lt_top`);
  its `NoAtoms` is the weak singleton-null class with an in-file TODO about
  the strong splitting notion. On ℝ the weak notion suffices (this file);
  on a general measurable space it does NOT (countable-cocountable
  counterexample), so S3-B must introduce the strong splitting predicate.
- v4.31 gotchas hit: `∞`/`ℝ≥0∞` need `open scoped ENNReal`; `zero_le` is
  now implicit-argument (`zero_le _` fails); `push_neg` deprecated (use
  `not_le.1` directly); `tendsto_measure_iUnion_atTop` needs the family
  given explicitly (`(s := fun i : ℝ => …)`) when the monotonicity proof is
  an untyped lambda; `tendsto_order.2` binders arrive beta-unexpanded
  (bridge with a defeq `have`).

## Session hazard log

The worktree (`researcher-2-4`) was janitor-reaped MID-SESSION after
verification but before commit; branch survived, all content restored from
agent context and re-committed immediately (see memory
`gotcha-janitor-reaps-fresh-worktree-before-first-commit`).

## Next steps

1. **S3-B**: strong atomless predicate + general-space Sierpiński via greedy
   exhaustion (recursion grabbing ≥ half the achievable remaining mass;
   `∑ μ Bₙ < ∞` forces exact attainment). ~250–400 LOC.
2. **S3-C**: Lyapunov in ℝᵈ by induction on d (uses S3-B + Radon–Nikodym).
3. **S3-D**: Aumann set-valued integral (needs measurable selections).

Equivalent-strength check: S3-A is materially weaker than full Lyapunov/Aumann
(proving d = 1 does not yield ℝᵈ by a known one-line argument — the induction
in S3-C requires Radon–Nikodym and the exhaustion machinery), so this is
decomposition progress, not a blocked same-strength restatement.
