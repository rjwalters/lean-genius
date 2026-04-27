# Current State

**Phase**: COMPLETED (axiomatized)
**Since**: 2026-01-23T08:04:56.539Z
**Last Updated**: 2026-04-27T22:30:00Z
**Iteration**: stable — no further work pending

## Current Focus

None — formalization is at a stable axiomatized end state matching the
meta.json's documented status.

## Active Approach

None.

## Blockers

None. The underlying mathematical conjecture (Erdős Problem #100, on
whether finite integer-distance sets in ℝ² must have diameter ≫ n)
remains OPEN, but the gallery formalization is complete:

- `proofs/Proofs/Erdos100Problem.lean`: 482 lines, **0 sorries**, **2 axioms**.
- The 2 axioms are:
  - `guthKatz_distinct_distances` — Guth & Katz (2015) distinct-distances
    bound (≥ cn/log n distinct distances for any n-point set in ℝ²).
  - `piepmeyer_construction` — existence of a 9-point integer-distance
    set with diameter < 5.
- Theorems proved (14 total): metric-space basics (`dist_symm`,
  `dist_nonneg`, `dist_self`, `dist_pos`, `dist_triangle`, `diam_nonneg`),
  the structural result `diam_is_integer` (diameter of an ≥ 2-point
  integer-distance set is a positive integer), the **bridge lemma**
  `distinctDistances_le_diam` (#distinct distances ≤ ⌊diam⌋ via Nat.floor
  injection into Finset.Icc 1 ⌊diam⌋), the lower bound `diam_ge_one`,
  the main lower bound `diam_ge_n_over_log_n` (chaining Guth–Katz with
  the bridge lemma), the upper-bound consequences
  `piepmeyer_ratio_bound` and `strong_conjecture_fails_at_9`, the
  implication `conjecture_implies_kanold`, and the asymptotic
  `n_over_log_sublinear` confirming n/log n = o(n).

The two axioms encode genuine external mathematical results that are
themselves nontrivial published theorems:

1. `guthKatz_distinct_distances` is the celebrated Guth–Katz 2015
   distinct-distances theorem. A formal Mathlib proof would be a major
   project on its own (polynomial-method + Elekes–Sharir reduction).
2. `piepmeyer_construction` asserts the existence of a 9-point
   integer-distance configuration with diameter < 5. Eliminating this
   axiom would require exhibiting an explicit configuration in Lean
   (constructive but tedious — coordinates for 9 points with all 36
   pairwise distances integer and overall diameter < 5).

The Erdős–Anning theorem (infinite integer-distance sets in ℝ² must be
collinear) is referenced as motivation for restricting to finite sets;
only the supporting `IsCollinear` predicate is defined formally — the
theorem itself is *not* declared as an axiom or theorem in this file
(meta.json has been corrected to reflect this on 2026-04-27).

Kanold's n^(3/4) bound is mentioned in commentary as historical
context but is *not* declared as an axiom or theorem in the file. The
`conjecture_implies_kanold` theorem proves only the implication: if
the linear conjecture holds then a c·n^(3/4) bound also holds (since
n^(3/4) ≤ n for n ≥ 1).

## Next Action

None for the research-agent loop. Possible follow-up work that would
strengthen this entry but is *not* required:

1. **Eliminate the Piepmeyer axiom.** Construct an explicit 9-point
   configuration in Lean (e.g., via lattice points on three concentric
   circles, or one of the known explicit constructions). This is a
   constructive but heavy formalization task.
2. **Add the Kanold n^(3/4) bound as a separate axiom** with a citation
   to its combinatorial counting proof, so that downstream work can
   reason about the chain n^(3/4) ≤ n/log n directly.
3. **Track Mathlib progress** on a formal Guth–Katz statement; once
   available, `guthKatz_distinct_distances` could be promoted from an
   axiom to a theorem reusing the Mathlib statement.

Otherwise, this entry should remain in its current state.

## Attempt Counts

- Total attempts: stable (single completed formalization, ≥ 3 prior
  enhancement sessions per pool notes)
- Current approach attempts: 0
- Approaches tried: axiomatized formalization with bridge lemma
  (successful)
