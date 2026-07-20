# Research State: combinations-formula-oq-03-oq-04

## Current State
**Phase**: PROVE
**Path**: full
**Since**: 2026-07-09T16:03:14-07:00
**Iteration**: 1

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


## Progress Log (researcher-1, 2026-07-19)
- **Unimodality reduction** (VERIFIED 0-axiom, docker [8577/8577]). The symmetric half
  (palindromy `qBinom_X_coeff_symm'`, pinned extremes, nonnegativity) was already complete.
  Added `UnimodalCoeffs` predicate on `ℤ[X]` and the general reduction
  `unimodalCoeffs_of_palindromic_of_monotone_left`: a nonnegative palindromic polynomial that
  is weakly increasing up to `⌊d/2⌋` is fully two-sided unimodal (decreasing half is the mirror
  of the increasing half; odd-`d` middle plateau also from palindromy). Instantiated for the
  Gaussian polynomial as `qBinom_X_unimodalCoeffs_of_monotone_left` — so the ONLY remaining
  content of Sylvester's theorem for `[n,k]_q` is the single hypothesis that the coefficients
  increase up to `⌊k(n-k)/2⌋`. `qBinom_X_unimodalCoeffs_zero` (k=0) confirms non-vacuity.

## Progress Log (researcher-1, 2026-07-19 — session 2, builds on the reduction above)
- **k ≤ 1 columns fully unimodal** (VERIFIED 0-axiom, docker [8577/8577]). Discharged the
  reduction's `hmono` hypothesis for `k = 1` **unconditionally**: `[n,1]_q = [n]_q =
  1 + q + ⋯ + q^{n-1}` has a *flat* left half (all coefficients `= 1` on `[0, ⌊(n-1)/2⌋]`), so
  `hmono` is trivial. Added `qNumber_X_coeff` ((qNumber X n).coeff j = if j<n then 1 else 0),
  `qBinom_X_one_coeff`, and `qBinom_X_one_unimodal` — the first **nontrivial** column
  (degree `n-1`) proved unimodal, upgrading the vacuous `k=0` sanity instance.
- **Open-question target form.** Added `CoeffNoValley` (no `i` with `a_i > a_{i+1} < a_{i+2}` —
  the pinned statement) and the bridge `coeffNoValley_of_unimodalCoeffs`; discharged for
  `k ≤ 1` (`qBinom_X_zero_noValley`, `qBinom_X_one_noValley`).

## Next Action
Discharge `hmono` for `k = 2`: `[n,2]_q` coefficients are `⌊j/2⌋+1` rising to the midpoint —
the first genuinely *humped* (non-flat) left half. Then attack general `k` (Proctor `sl₂` /
O'Hara). Once `hmono` lands for a case, the reduction lemma closes unimodality immediately.
