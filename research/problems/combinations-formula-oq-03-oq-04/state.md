# Research State: combinations-formula-oq-03-oq-04

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-09T16:03:14-07:00
**Iteration**: 2

## Status (S2, researcher-1, 2026-07-20) — unimodality API + base cases k ≤ 1

NOTE: the S1 template below was never filled in even though a substantial companion
file (`CombinationsFormulaOQ03OQ04.lean`, 16 thm, 0 ax/sorry — palindromy, degree,
monicity, coeff-nonneg, pinned extreme coeffs) already existed. This is the first
real ACT status.

New file `CombinationsFormulaOQ03OQ04Unimodal.lean` (1 def + 5 thm, 0 ax, 0 sorry,
docker-VERIFIED `[propext, Classical.choice, Quot.sound]`). Supplies the unimodality
layer the target theorem needs and the first two milestones:

- `IsCoeffUnimodal p` — coefficient-sequence unimodality of `p : ℤ[X]` (a peak index
  below which coeffs weakly rise, above which they weakly fall). Fills the Mathlib gap
  named in problem.md ("no Unimodal predicate for integer sequences").
- `isCoeffUnimodal_of_antitone` — a globally non-increasing coeff sequence is unimodal
  (peak at 0); the reusable reduction both base cases use.
- `qNumber_X_coeff` — coeff array of `qNumber X n = 1 + X + ⋯ + X^{n-1}` is `[j < n]`.
- `qBinom_X_coeff_one` — hence coeffs of `[n,1]_q` are `[j < n]`.
- `qBinom_X_unimodal_zero` / `qBinom_X_unimodal_one` — the coeff sequences of `[n,0]_q`
  and `[n,1]_q` are unimodal (base cases k = 0, 1 of Sylvester's theorem).

**Honesty**: `k ≤ 1` is the *easy* regime — both sequences are flat/monotone, so
unimodality collapses to `isCoeffUnimodal_of_antitone`. The hard cases `k ≥ 2`, where
the sequence genuinely rises then falls (e.g. `[6,2]_q = 1,1,2,2,3,2,2,1,1`), are the
open crux and need the sl₂-action / hard-Lefschetz argument (Proctor 1982) or O'Hara's
combinatorial decomposition (1990). Not attempted here.

## Next Action (item toward k = 2)
Derive the explicit coefficient formula for `[n,2]_q` (partitions into ≤ 2 parts each
≤ n−2; `a_i = ⌊i/2⌋+1` capped and mirrored), then prove `IsCoeffUnimodal (qBinom X n 2)`
by direct inequality on that formula — the named "tractable first milestone" in
problem.md. This is the first case where the peak is interior and `_of_antitone` no
longer applies, so it exercises the rising-then-falling reasoning.

## --- S1 template (never filled) below ---

## Current Focus
Initial problem understanding. Read problem.md and gather context.

## Active Approach
None yet.

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
None.

## Next Action
Read problem.md thoroughly and acquire full context.
Then move to ORIENT phase to explore literature and related proofs.
