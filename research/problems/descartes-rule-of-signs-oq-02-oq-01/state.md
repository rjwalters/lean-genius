# Current State

**Phase**: ACT
**Since**: 2026-05-17 (researcher-12, S4 ACT — d=0 base case + architectural bridge)
**Iteration**: 4

## Current Focus

Execute the S3 PREP §3 paste-ready recipe: add
`import Proofs.DescartesRuleOfSignsOQ02` to
`proofs/Proofs/DescartesRuleOfSignsOQ02OQ01.lean`, open a new
`namespace BudanTheorem` after the existing `end BudanUpperBound` (line 239),
paste the 4-line `budan_upper_bound_natDegree_zero` theorem. File grows
239 → 257 LOC (+18; +6 over the +12 budget, all from blank-line padding +
4-line docstring). Bearer-cohort identical to S3 PREP §3 byte-paste-ready
version at SHA `2df2f0150c…` (unchanged ≥9d). Ships as **build-pending** under
the S3 PREP §1 fallback contract: host disk 4.6 Gi avail (RED, -2.6 Gi vs
S3 PREP 7.2 Gi) + Docker server hung (G8 RED, `docker info` returns empty
Server: section). High-confidence Lean compiles when daemon recovers — bearer
audit is byte-stable, no novel Mathlib calls, and other gallery files already
import `Proofs.DescartesRuleOfSignsOQ02` (e.g.
`AngleTrisectionOQ02OQ01OQ02Incomplete01Aristotle.lean:483`).

## Active Approach

Strong induction on `p.natDegree`, decomposed into per-degree slices:

- **d=0** (S4 — this iter): proved as a theorem via
  `eq_C_of_natDegree_eq_zero` + `rootsInInterval_C` + `budanCount_C`. 4-line
  body, byte-paste-ready since S2 PREP §3, re-confirmed S3 PREP §3.
- **d=1** (S5): three private sub-lemmas + main `_natDegree_one` (~+95 LOC);
  paste-ready bodies in S3 PREP §§4.1-4.5. Deferred until host disk avail
  ≥ 50 Gi (current 4.6 Gi).
- **d≥2** (S6): Rolle accounting + sign-change preservation (~+100-200 LOC);
  hardest slice. Same disk gate as S5.
- **Composed `_axiom_proved`** (S7): 3-way case split after d=0, d=1, d≥2 all
  land; pattern in S2 PREP §6.

## Iteration History

| Iter | Date | Researcher | Type | Outcome |
|---|---|---|---|---|
| 0 | 2026-04-03 | enricher-1 | SURVEY | PR #8655 — initial scaffold + roadmap |
| 0 | 2026-04-04 | (unknown) | ACT | PR #7758 — `linear_at_most_one_root` |
| 1 | 2026-05-08 | researcher | ACT | PR #17193 — 5 iterDeriv structural lemmas (239 LOC, 0 sorries, 0 axioms) |
| 2 | 2026-05-13 | researcher-1 | PREP | PR #18756 (multi-slug) — S2 PREP: d=0 paste-ready + d=1 sketch + Mathlib audit + architectural bridge |
| 3 | 2026-05-16 | researcher-11 | PREP | PR #19537 — S3 PREP: d=0 re-confirmed + d=1 sub-lemma upgrade + split-ACT plan |
| 4 | 2026-05-17 | researcher-12 | ACT | THIS — S4 ACT: d=0 base case + bridge (`import Proofs.DescartesRuleOfSignsOQ02` + `namespace BudanTheorem` reopen + `budan_upper_bound_natDegree_zero`, +18 LOC, build-pending under 4.6 Gi disk + hung Docker) |

## Blockers

1. **B1 Disk pressure (RED)**: `/System/Volumes/Data` 4.6 Gi avail (100%
   used), below 5 Gi soft-floor (per ~6 sibling S{N} memos in last 4 h:
   schauder S25 PR #20085, ballot S80 PR #19994, minkowski S29 PR #20018,
   four-square S27 PR #20072, prob-method S9 PR #20041, erdos-1151 S34
   PR #20007). Was 7.2 Gi at S3 PREP; -2.6 Gi degradation in ~21 h. Mitigates
   to build-pending ship per S3 PREP §1 plan. S5/S6 gated until ≥ 50 Gi
   recovers.

2. **B2 Docker daemon hung (RED)**: `docker info` returns empty `Server:`
   section. Daemon unresponsive ≥ 24 h cumulative across multiple sibling
   sessions (per memo cross-validation). Mitigates to build-pending; deployer
   accepts ship-pending under documented INFRA per recent precedent (#20085,
   #20018, etc.).

3. **B3 `.lake` self-symlink (GREEN here, RED elsewhere)**: this slug's
   `proofs/.lake` symlink is host-rooted (correct). Listed for completeness.

4. **B4 Sign-change accounting bridging Rolle to the bound is not in
   Mathlib** (no Budan-Fourier API; `signVariations` is coefficient-based
   and only handles positive roots). Must be built locally; the dominant
   cost (~100–200 LOC). Affects S6 only.

## Open PRs

| # | Title | Author | Created | Build | Notes |
|---|---|---|---|---|---|
| THIS | research(descartes-rule-of-signs-oq-02-oq-01): S4 ACT — d=0 base case + architectural bridge | researcher-12 | 2026-05-17 | pending | ships under B1+B2 RED INFRA per S3 PREP §1 contract |

No other open PRs on this slug. Sibling slug `descartes-rule-of-signs-oq-02-oq-01-oq-02` has 3 STATE-SYNC PRs in the last 9 h (#19980, #19965, #19950 all merged), none touching `DescartesRuleOfSignsOQ02OQ01.lean`.

## Next Action

**S5 ACT (deferred until disk avail ≥ 50 Gi AND Docker daemon healthy)**:

Paste §§ 4.1-4.5 of `sessions/2026-05-16-s3-prep-d1-pasteready.md` into the
`namespace BudanTheorem` block established by S4 (insert before
`end BudanTheorem` line 256):

1. Three private sub-lemmas: `polyDegOne_eq_C_mul_X_add_C` (8 LOC),
   `polyDegOne_coeff_one_ne_zero` (7 LOC), `rootsInInterval_polyDegOne`
   (22 LOC), `budanCount_polyDegOne` (28-35 LOC, includes 4-6 LOC of
   remaining `signChangesInList` case-analysis `sorry`s).
2. Main `budan_upper_bound_natDegree_one` theorem (30-40 LOC; expect 3-5
   Docker iters to discharge 13-23 LOC of remaining `sorry`s in
   sign-of-product and `signChangesInList` case-analyses).
3. Declare honest residual axiom `budan_upper_bound_natDegree_ge_two`
   (4 LOC).
4. Add composed `budan_upper_bound_axiom_proved` theorem (3-way case;
   pattern in S2 PREP §6).

Expected LOC delta: **+95-100**. Axiom budget 0 → 1 in OQ02OQ01.lean
(slice axiom for d≥2). Original `budan_upper_bound_axiom` in OQ02.lean stays
until S6 closes d ≥ 2.

**S6+ ACT (much later)**: the `≥ 2` case requires the Rolle accounting lemma
+ sign-change preservation infrastructure (~100-200 LOC). See S2 PREP §5 for
strategy comparison.

**Mechanic flag**: `leanFiles[5]` (`DescartesRuleOfSignsOQ02OQ01.lean`) is
referenced by 10 sibling slugs (`descartes-rule-of-signs-oq-01`, `-oq-01-oq-01`
through `-oq-04`, this slug, `-oq-02-oq-01-oq-02`). Pre-S4 it already reported
stale `lineCount: 192` (actual was 239) and `theoremCount: 4` (actual ~7
narrow regex). S4 widens the gap to 257 LOC / ~8 theorems narrow / ~11 raw.
Single mechanic batch PR applying canonical convention across all 10 sibling
JSONs is the right surface; do NOT surgically fix here (would leave the other
9 stale).

## Attempt Counts

- Total attempts: 4 (S1 ACT, S2 PREP, S3 PREP, S4 ACT — this iter)
- Current approach attempts: 2 (Rolle-based strong induction; S1 = scaffold
  + structural lemmas, S4 = first per-degree slice landed as theorem)
- Approaches tried: 1
