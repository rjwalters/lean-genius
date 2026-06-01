# Research State: nth-root-irrational-oq-03

## Current State

**Phase**: PREP — S6 watch tick (PR #28013) + CF-of-e Mathlib master rescan (0 new content) + S5c infrastructure build re-verify (3072/3072 clean at HEAD `8bf8a7b3552`). Path C re-evaluation: **no actionable target** — empirical grep confirms no other `LiouvilleWith p (specific-irrational)` axiom anywhere in `proofs/Proofs/`. Strategic posture shifts to Path B (passive watch). PR #28013 staleness 69.8h (warm; 2026-05-29 merge from master reset the clock), well below 168h threshold.
**Path**: full
**Since**: 2026-05-12T13:07:57-07:00 (slug creation by seeker)
**Last Updated**: 2026-06-01T05:10:00Z (Iteration 7, researcher-1)
**Iteration**: 7

## Iteration 7 (researcher-1, 2026-06-01) — S6 PREP (PR #28013 watch tick + CF-of-e rescan + S5c build re-verify)

**Outcome**: doc-only — 16-day delta watch tick on PR #28013, Mathlib master rescan for CF-of-e additions (0 found; one CF determinant generalisation #37997 ships generic machinery only), and S5c-shipped infrastructure build re-verify (3072/3072 clean, 0 bearer drift). Also performed empirical re-check of S5d's Path C recommendation: **no sibling slug carries a `LiouvilleWith p (specific-irrational)` axiom** that could be discharged by the S5c-built `irrational_liouvilleWith_two` template. Path C is empirically exhausted; strategic posture shifts to Path B (passive PR #28013 watch) until upstream merge or staleness threshold crossed.

### What I did

- Verified lake-manifest at HEAD `8bf8a7b3552` pins Mathlib `v4.26.0` → SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged from S5d, 16 days ago).
- Ran `./proofs/scripts/docker-build.sh Proofs.ETranscendentalOQ03` at HEAD. Result: 3072/3072 jobs clean; `ETranscendentalOQ03` and `eTranscendental` both replayed/built; only 3 deprecation linter warnings (same 3 as recorded in S5c §3, unchanged).
- Re-pinned PR #28013 status via `gh api`: head SHA `5abb7c68488…` (changed from S5d-era `3bafffe27908…`), `updated_at = 2026-05-29T07:22:48Z`, `mergeable_state = blocked`, additions 1040 / deletions 64, 9 issue + 24 review comments. Recomputed staleness at 2026-06-01T05:10Z: **69.8h** (was 90.9h at S5d). The 2026-05-29 commit is a merge-from-master only — no new substantive content since 2026-05-08.
- Enumerated Mathlib master commits in `Mathlib/Algebra/ContinuedFractions/` and `Mathlib/NumberTheory/DiophantineApproximation/` since 2026-05-16: 1 substantive CF commit (PR #37997 `30f4950b`, det formula generalisation `SimpContFract` → `GenContFract`), plus 1 toolchain bump (`d568c8c0`, v4.31.0-rc1) and 1 doc PR (`fc937127`). **0 e-specific additions.**
- 3 independent code searches for CF-of-e content (`"exp 1" convergent`, `"convergents_exp"`, `"Euler continued fraction"`): 0 source hits in Mathlib repo (only docs/references.bib + docs/overview.yaml). S5d's 280–480 LOC re-estimate for direct S5d.A discharge remains valid.
- Empirical Path C check: `grep -rn "axiom.*[Ll]iouvilleWith" proofs/Proofs/` → exactly 1 match (`e_not_liouvilleWith_gt_two` in `ETranscendentalOQ03.lean:247`, same file as the just-shipped `irrational_liouvilleWith_two`). No sibling slug carries an analogous axiom; `PiTranscendental.lean` has only `lindemann_theorem`, no `Liouville*`-shaped axioms.
- Pre-push race check: 0 open PRs with `nth-root-irrational-oq-03 in:title`; `feature/researcher-1` branch carries 0 open prior PRs.

### Files Modified

- `research/problems/nth-root-irrational-oq-03/sessions/2026-06-01-s6-prep-pr28013-watch-tick-and-cf-of-e-rescan.md` (new — full watch-tick report, ~280 LOC)
- `research/problems/nth-root-irrational-oq-03/state.md` (this entry + Current State header refresh; historical tail preserved)
- `src/data/research/problems/nth-root-irrational-oq-03.json` (top-level `phase`/`iteration`/`lastUpdated` sync; new insight; nextSteps reorganised to flag Path C exhaustion and elevate S6 watch as primary active stance)

No Lean files modified. No meta.json modifications.

### Knowledge Added

- **Insights**: 3
  1. **Path C (S5d sibling-slug template re-use) is empirically exhausted at HEAD.** A repo-wide grep for `axiom.*[Ll]iouvilleWith` returns exactly one hit (`e_not_liouvilleWith_gt_two`, in the same file as the just-shipped lower-bound template). No other file carries the analogous-axiom shape. S5d's Path C never has anything to fire on.
  2. **PR #28013 reset its staleness clock on 2026-05-29 via merge-from-master.** As of 2026-06-01 the PR is 69.8h stale (well below the 168h "consider scoping local re-prove" threshold from S4c). The merge SHA change is mechanical only — no new substantive content since the 2026-05-08 `lint/cleanup/fix` cluster.
  3. **S5c-shipped infrastructure remains build-stable across the 16-day interval.** 3072/3072 jobs clean at HEAD `8bf8a7b3552`; 0 new Mathlib API regressions detected; same 3 deprecation linter warnings as S5c records. The S5a discovery pattern (silent parent regression on long doc-only chains) does not repeat here — the slug now has Lean-file changes in its history, providing a Docker checkpoint.

- **Built items**: 0 (doc-only)
- **Risks retired**: 1 — the post-S5d "Path C as active high-ROI continuation" framing. Empirical check shows no actionable target.
- **Next steps**:
  - **S6 watch (next, passive)**: re-check PR #28013 head SHA + `updated_at` at next claim. Current staleness 69.8h; threshold 168h; margin 98h.
  - **S5d.A (deferred, multi-session)**: if PR #28013 stalls past the 168h threshold (≈ next ~4 days from 2026-05-29), promote `e_continued_fraction_pattern` formalisation from "deferred" to "scope this session". Hermite-identity route may be shorter than direct-CF-via-series.
  - **Mechanic follow-up (out of scope)**: 3 deprecation linter warnings in `eTranscendental.lean` + `ETranscendentalOQ03.lean` — 2 import-aliases (`Mathlib.Data.Real.Irrational` → `Mathlib.NumberTheory.Real.Irrational`; `Mathlib.Data.Complex.ExponentialBounds` → `Mathlib.Analysis.Complex.ExponentialBounds`). 3 lines, 2 files, no semantic change.

## Current Focus (updated S6)

The slug's two remaining axioms are independently gated:

1. **`axiom hermite_lindemann`** in `HermiteLindemann.lean` — gated on Mathlib PR #28013 merge. Watch-loop cadence at 24h–weekly. Staleness margin large (98h before threshold). No scope-promotion signal.
2. **`axiom e_not_liouvilleWith_gt_two`** in `ETranscendentalOQ03.lean` — requires 280–480 LOC formalisation of Euler's CF expansion of e from scratch (3-sub-task arc S5d.A/B/C). 0 new CF-of-e content in Mathlib master since S5d. Multi-session work; not eligible for single-session ACT.

**Active stance**: Path B (passive PR #28013 watch). Path C empirically exhausted (this iteration). Path A.A deferred.

## Active Approach (updated S6)

Same axiom-reduction sequence as S5d, with Path C downgraded to "empirically empty":

- **S6 (passive, primary stance)**: PR #28013 watch-loop tick at next claim. Promote local re-prove if > 168h stale.
- **Path C (closed)**: no sibling slug has an analogous `LiouvilleWith p (specific-irrational)` axiom. Re-open only if a future enricher/researcher *adds* such an axiom to another file.
- **S5d.A/B/C (deferred)**: Direct discharge of `e_not_liouvilleWith_gt_two`; requires 3 sessions and Euler's CF expansion of e formalisation from scratch.

## Race Notes (S6)

Pre-action race check at 2026-06-01T05:10Z:
- 0 open PRs with `nth-root-irrational-oq-03 in:title`
- 0 open PRs on `feature/researcher-1` (clean shared branch)
- 0 open PRs touching `ETranscendentalOQ03`, `eTranscendental`, `HermiteLindemann`
- Most recent merge on slug: PR #19351 (S5c ACT, 2026-05-16T01:08:28Z, researcher-12)
- 16-day gap since last activity — within expected cadence for a "drained" slug awaiting external (Mathlib upstream) progress.

This PR is **doc-only**: 1 new session note + state.md update + JSON refresh. **STATE-SYNC**: counts against the 2-STATE-SYNC-PR-per-session cap.

## Iteration 6 (researcher-11, 2026-05-16) — S5d PREP (CF API enumeration + feasibility verdict)

**Outcome**: doc-only — enumerated Mathlib `Algebra.ContinuedFractions.*` + `NumberTheory.DiophantineApproximation.*` API at lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0). Confirmed full generic CF machinery is available (`succ_nth_fib_le_of_nth_den`, `abs_sub_convs_le`, `Real.exists_rat_eq_convergent`), but **CF expansion of e (Euler's [2;1,2k,1] pattern) is completely absent from Mathlib**. Re-estimated S5d scope from `~150–250 LOC` (post-S5c optimistic) to **280–480 LOC across 3 sub-tasks (S5d.A/B/C)**. Recommended hybrid Path B (PR #28013 watch) + Path C (sibling slug template re-use) rather than direct S5d ACT. Also performed 24h bearer drift recheck on S5c bearers — 0 drift.

### What I did

- Verified lake-manifest at origin/main pins Mathlib `v4.26.0` → SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged from S5c).
- Enumerated `Mathlib/Algebra/ContinuedFractions/` (12 files) + `Mathlib/NumberTheory/DiophantineApproximation/` (2 files) at pinned SHA via `gh api git/trees/<SHA>?recursive=1`.
- Re-pinned 5 S5c-era bearers at lake SHA (`Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`, `LiouvilleWith`, `Real.rpow_natCast`, `Rat.num_div_den`, `Irrational.ne_rat`) — all unchanged.
- Read full signatures of 5 CF-machinery bearers (`succ_nth_fib_le_of_nth_den` line 249, `abs_sub_convs_le` line 393, `of_partNum_eq_one` line 160, `of_one_le_get?_partDen` line 134 in `Approximations.lean`; `Real.exists_rat_eq_convergent` line 538 in `Basic.lean`).
- Performed 3 independent GitHub code searches for CF-of-e content (`"continued fraction of e"`, `"euler continued fraction"`, `"exp 1 ... convergent"`) — all 0 results in Mathlib source.
- Decomposed Davis's (1978) mathematical argument into 6 steps; mapped which are available (steps 3, 4, 5 — generic machinery) vs absent (steps 1, 2 — e-specific input).
- Re-estimated S5d scope: original `~150–250 LOC` was conditional on the CF expansion of e being available. With CF-of-e absent, the realistic scope is **S5d.A (e_continued_fraction_pattern, 150–250 LOC) + S5d.B (e_convergent_den_ratio_bounded, 50–80 LOC) + S5d.C (e_not_liouvilleWith_gt_two, 80–150 LOC)** = 280–480 LOC total.
- Performed S6 watch-loop tick on Mathlib PR #28013: head SHA `3bafffe279084269f91f91b0ea8bafc4ac666bbe` unchanged, `updated_at = 2026-05-12T09:28:36Z` unchanged → ~90.93h staleness vs 168h promotion threshold.

### Files Modified

- `research/problems/nth-root-irrational-oq-03/sessions/2026-05-16-s5d-prep-cf-api-enumeration-and-feasibility.md` (new — full enumeration, verdict, recommendation; ~650 LOC)
- `research/problems/nth-root-irrational-oq-03/state.md` (this entry + Current State header refresh; historical tail preserved)
- `src/data/research/problems/nth-root-irrational-oq-03.json` (top-level `phase`/`iteration`/`lastUpdated` sync; new insight; `nextSteps` reordered to put Path C ahead of Path A)

No Lean files modified. No meta.json modifications.

### Knowledge Added

- **Insights**: 3
  1. **Mathlib v4.26.0 has full generic CF machinery but no CF expansion of e.** Direct S5d discharge requires formalising Euler's [2;1,2k,1] pattern from scratch — 280–480 LOC across 3 sub-tasks, not the 150–250 LOC originally estimated by post-S5c state.md.
  2. **The generic CF bound stack at v4.26.0 is exactly the right shape for any concrete-irrational Liouville upper-bound argument.** `succ_nth_fib_le_of_nth_den` + `abs_sub_convs_le` + `Real.exists_rat_eq_convergent` is a complete tooling chain. The gap is purely the e-specific input (Euler's pattern), not the framework.
  3. **PR #28013 staleness has tripled since S5a record** (28h → 91h, threshold 168h). At current rate (~22h staleness/day elapsed), promotion trigger is ~3.5 days out.

- **Built items**: 0 (doc-only)
- **Risks retired**: 1 — the post-S5c "S5d as next single-session ACT" framing.
- **Next steps**:
  - **S5e or S7 next session**: identify the most tractable sibling slug with an
    analogous `LiouvilleWith 2 (specific-irrational)` axiom (candidates:
    `pi-transcendental-oq-*`, `ln-2-*`); apply S5c's reusable slice-finiteness +
    `irrational_liouvilleWith_two` template (~30–60 LOC ACT).
  - **S6 watch**: re-check PR #28013 head SHA + `updated_at` at next claim of this slug.
  - **S5d.A (if Path A elected later)**: PREP — design `e_continued_fraction_pattern`
    proof outline; decide Hermite-identity vs direct-CF-via-series.

## Current Focus (updated S5d)

S5d direct ACT is **NOT feasible as a single-session task** at v4.26.0. The CF expansion of e is absent from Mathlib; the realistic 3-sub-task arc requires 280–480 LOC of new content.

**Recommended hybrid posture**:

1. **Path B (passive)**: continue S6 watch on Mathlib PR #28013. Threshold 168h, current 91h, margin ~77h. Re-check at next slug claim.
2. **Path C (active, high ROI)**: apply S5c's `rat_approx_bounded_den_finite` + `irrational_liouvilleWith_two` reusable template to a sibling slug with an analogous `LiouvilleWith 2 (specific-irrational)` axiom. ~30–60 LOC ACT, builds on the just-shipped infrastructure, retires another axiom elsewhere.
3. **Path A (deferred)**: 3-sub-task arc S5d.A → S5d.B → S5d.C; only commit if Paths B+C exhaust their value.

## Active Approach (updated S5d)

Same axiom-reduction sequence as in S5c's "current focus", with realistic scoping:

- **S5e/S7 (next, active)**: Sibling-slug template re-use (Path C, ~30–60 LOC).
- **S6 (passive)**: PR #28013 watch-loop tick at 24h cadence.
- **S5d.A/B/C (deferred)**: Direct discharge of `e_not_liouvilleWith_gt_two`; requires 3 sessions and the formalisation of Euler's CF expansion of e from scratch.

## Race Notes (S5d)

Pre-action race check at 2026-05-16T03:20Z:
- 0 open PRs with `nth-root-irrational-oq-03 in:title`
- 0 open PRs touching `ETranscendentalOQ03`, `eTranscendental`, or `e-transcendental-oq-03`
- Most recent merge on slug: PR #19351 (S5c ACT, 2026-05-16T01:08:28Z, researcher-12, ~2.3h before claim).
- Open queue at write-time: **118 PRs**; deployer recently active.

This PR is **doc-only**: 1 new session note + state.md head update + JSON refresh. It **counts** as a STATE-SYNC / PREP-PR for this session's cap.

## Iteration 1 (researcher-10, 2026-05-12) — S1 OBSERVE

**Outcome**: doc-only — duplicate-detection survey identifying that this slug substantially overlaps existing Hermite-Lindemann / Lindemann-Weierstrass infrastructure.

### What I did

- Inventoried all existing project Lean files related to transcendence of $e$, $\pi$, and the Hermite-Lindemann statement: 6 files totalling 2,623 lines.
- Confirmed `HermiteLindemann.lean:147` axiomatizes the main statement (`axiom hermite_lindemann`); 1 axiom on this file.
- Confirmed sibling `ETranscendentalOQ03.lean` has 2 tractable axioms (`irrational_liouvilleWith_two`, `e_not_liouvilleWith_gt_two`) on the $\mu(e) = 2$ irrationality-measure result.
- Noted the slug's placement under `nth-root-irrational` parent is misleading: parent is *algebraic-irrationality*, this OQ is *transcendence*. The technical content effectively duplicates `e-transcendental-oq-{01,02,03}` plus `HermiteLindemann.lean`.
- Drafted a 4-iteration roadmap focused on **bridge work** (axiom reduction in `ETranscendentalOQ03.lean`) rather than re-formalising Lindemann-Weierstrass from scratch (an 800-1500 line task).
- Generated 0 new mathematical content (no Lean changes); deliverable is documentation only.

### Files Modified

- `research/problems/nth-root-irrational-oq-03/problem.md` (new — refined problem statement, parent mismatch documented)
- `research/problems/nth-root-irrational-oq-03/knowledge.md` (new — literature survey, axiom inventory, three tier-A/B/C target lists)
- `research/problems/nth-root-irrational-oq-03/state.md` (new — this file)
- `src/data/research/problems/nth-root-irrational-oq-03.json` (new — gallery entry with cross-references)

### Knowledge Added

- **Insights**: 4
  1. The "open question" is mostly already infrastructure (axiomatized in HermiteLindemann.lean)
  2. Two tractable adjacent axioms in OQ03 sibling
  3. The full HL axiom is ~900 lines of work — wait for Mathlib upstream PR
  4. Project status is "axiomatized", not "verified"

- **Built items**: 0 (S1 OBSERVE is doc-only)
- **Next steps**: 4 planned iterations (S2-S4 plus optional S5)

## Current Focus

S1 OBSERVE complete. Next session should advance to S2 ACT.

## Active Approach

**S2 plan**: Discharge `axiom irrational_liouvilleWith_two` in `proofs/Proofs/ETranscendentalOQ03.lean` using Mathlib Dirichlet-approximation API. This is the highest-value tractable next step: axiom count 2 → 1 on the relevant file, and the proof is canonical (~30-60 lines).

If Mathlib v4.26.0 API has the needed lemmas, attempt the proof. If not, **document the upstream API gap** as a contribution boundary (memo: file in `research/problems/nth-root-irrational-oq-03/literature/` or as a follow-up Mathlib PR target).

## Attempt Count

- Total attempts: 1 (this S1)
- Current approach attempts: 0 (S2 not yet attempted)
- Approaches tried: 0

## Blockers

None for S1 (doc-only). For S2:

- Mathlib v4.26.0 API compatibility with `LiouvilleWith 2` (low risk).
- Whether `Mathlib.NumberTheory.DiophantineApproximation.exists_q_lt_inv` (or equivalent) exists at the pin.

## Next Action

**Session 2 (S2 ACT)**: Open `proofs/Proofs/ETranscendentalOQ03.lean`. Locate `axiom irrational_liouvilleWith_two` on line 114. Replace with `theorem … := by …`. Prove using Mathlib's Dirichlet approximation API:

```lean
theorem irrational_liouvilleWith_two (x : ℝ) (hx : Irrational x) : LiouvilleWith 2 x := by
  -- LiouvilleWith p x ↔ ∃ C > 0, ∀ᶠ q in atTop, ∃ p, |x - p/q| < C/q^p
  -- Dirichlet: ∀ N ≥ 1, ∃ (p,q) with 1 ≤ q ≤ N, |x - p/q| < 1/(qN) ≤ 1/q^2
  -- Take C := 1, lift Dirichlet pairs to LiouvilleWith infinite family
  sorry
```

Run `./proofs/scripts/docker-build.sh Proofs.ETranscendentalOQ03` to verify. Update axiom count in `src/data/proofs/e-transcendental-oq-03/meta.json` (if such gallery entry exists) from 2 → 1.

**Race-readiness**: Before pushing S2, re-run:
```bash
gh pr list -R rjwalters/lean-genius --search "nth-root-irrational-oq-03" --state all
gh pr list -R rjwalters/lean-genius --search "e-transcendental-oq-03" --state all
git branch -r | grep -E "nth-root-irrational-oq-03|liouvilleWith"
```
to detect parallel work.

## Race Notes (S1)

S1 deliverable scope kept small (4 doc files, no Lean) to ship fast given Wiedijk-100 race-prone slug risk. Pre-write check: 0 open research PRs for this slug; only PR #18263 (seeker batch init) creates the same 3 markdown files — minor expected conflict if #18263 merges first (mine includes substantive content, theirs is a stub).

## Iteration 2 (researcher-11, 2026-05-13) — S4c PREP

**Outcome**: doc-only — verify S4b §4.3's deferred Mathlib API at pinned rev + correct a `rw` direction error in S4b §4.3's `log_transcendental_real` skeleton. Retires 2 of S4b §6 risks; reduces S5 ACT's API-layer blockers to "PR #28013 merge only".

### What I did

- Fetched `Mathlib/Analysis/SpecialFunctions/Complex/Log.lean` at pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Confirmed `Complex.ofReal_log` at line 62 with signature `{x : ℝ} (hx : 0 ≤ x) : (x.log : ℂ) = log x`.
- Fetched `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` at the same rev. Confirmed `Real.log_ne_zero_of_pos_of_ne_one` at line 254 with signature `{x : ℝ} (hx_pos : 0 < x) (hx : x ≠ 1) : log x ≠ 0`.
- Verified absence of `LindemannWeierstrass.transcendental_log` at v4.26.0: `gh api .../trees/2df2f0150c...?recursive=1` shows the Lindemann directory contains only `AnalyticalPart.lean` (no `Basic.lean`).
- Fetched PR #28013 head (`3bafffe279084269f91f91b0ea8bafc4ac666bbe`); confirmed `transcendental_log` signature at `Basic.lean:255` matches S4b §4.3's cited form verbatim. PR head SHA + `updated_at` (`2026-05-12T09:28:36Z`) unchanged from S4 PREP — > 28h stale.
- Caught direction error in S4b §4.3: both `rw [Complex.ofReal_log hu_pos.le]` calls need a `←` arrow (the lemma orients `Real.log → Complex.log` but the rewrite is needed `Complex.log → Real.log`). Provided corrected 7-LOC skeleton.
- Flagged S4b §4.1's `rw [Complex.ofReal_exp]` orientation question for S5 ACT verification (local file uses same pattern in compiling code, so direction is some-orientation-correct; not fetched in this PREP to keep scope tight).

### Files Modified

- `research/problems/nth-root-irrational-oq-03/sessions/2026-05-13-s4c-prep-mathlib-api-verify-at-pinned-rev.md` (new — this iteration's report)
- `research/problems/nth-root-irrational-oq-03/state.md` (this entry)

### Knowledge Added

- **Insights**: 3
  1. Both deferred §4.3 lemmas (`Complex.ofReal_log`, `Real.log_ne_zero_of_pos_of_ne_one`) are present at v4.26.0 — no upstream Mathlib gap.
  2. S4b §4.3 has a 2-arrow `rw` direction error that would have caused S5 ACT to fail at `lake build` time; corrected in §3.2.
  3. PR #28013 has been completely dormant since 2026-05-12 09:28 UTC (≥ 28h stale at S4c write-time) — S6 (local re-prove) becomes more likely if no movement in another 1–2 weeks.

- **Built items**: 0 (S4c PREP is doc-only)
- **Risks retired**: 2 of S4b §6 (`Complex.ofReal_log` existence; `Complex.ofRealHom.toAlgHom` instance for `ℤ`-algebra)
- **Next steps**: S5 ACT remains gated on PR #28013 merge; no further PREP work needed at the Mathlib-API layer.

## Current Focus (updated S4c)

S5 ACT remains gated on PR #28013 merge. At the Mathlib-API layer, all bridge dependencies are verified at the pinned rev (`Complex.ofReal_log`, `Real.log_ne_zero_of_pos_of_ne_one`, `IsAlgebraic.algHom`, `Complex.ofRealHom.toAlgHom`, `IsFractionRing.isAlgebraic_iff`). Only `LindemannWeierstrass.{transcendental_exp, transcendental_e, transcendental_pi, transcendental_log}` are PR-#28013-gated.

**Watch-loop cadence**: re-check PR #28013 head SHA + `updated_at` once per 24h. If unchanged for ≥ 1 week (i.e. > 7×24h from `2026-05-12T09:28:36Z`), promote S6 (local re-prove ~700–900 LOC) from "deferred" to "consider scoping". Current count: ~28h stale.

## Active Approach (updated S4c)

**S5 plan (post-merge)**: apply S4 PREP §3.4's 5-LOC bridge for `hermite_lindemann`. Optionally apply S4b §3.2/§3.3 refactors and add `log_transcendental_real` using **S4c §3.2's corrected skeleton** (with `← Complex.ofReal_log` in both rewrite sites).

If PR #28013 stalls past 2026-05-19 (1 week from current `updated_at`), pivot to S6 (Scenario C local re-prove).

## Attempt Count

- Total iterations: 2 (S1 OBSERVE + S4c PREP); intervening S2/S2c/S2d/S3/S3a/S4/S4b are listed in iteration-1 dependents but track separately as merged PRs not state-update iterations
- Current approach attempts: 0 (S5 ACT not yet attempted; gated externally)
- Approaches tried: 0 (no Lean refactor yet)

## Iteration 3 (researcher-12, 2026-05-13) — S5a PREP

**Outcome**: doc-only on filesystem; **substantive discovery** of two independent Mathlib v4.26.0 API regressions that block both `ETranscendentalOQ03.lean` (line 118) and `eTranscendental.lean` (9 errors at lines 151, 164, 183, 198, 212, 214, 224, 225, 228). These regressions explain why 9 consecutive doc-only PREP PRs (S1 through S4c, all merged 2026-05-12/13) failed to catch the build break — none of them Docker-built. The slug had drifted into the (doc-only chain) variant of the `(build pending) silent parent regression` anti-pattern from memory. This iteration also drafts a complete ~85-LOC S2 ACT proof body, ready for paste-in after parent-file repair.

### What I did

- Attempted **S2 ACT** (discharge `axiom irrational_liouvilleWith_two`) following the S2 PREP / S2c REFINE / S2d PREP recipe. Wrote ~85 LOC of Lean: a `rat_approx_bounded_den_finite` helper lemma + the main theorem.
- Discovered on first Docker build that `ETranscendentalOQ03.lean` line 118 (`e_liouvilleWith_two`, existing code) fails at v4.26.0 with `Unknown identifier irrational_exp_iff.mpr`. Verified by `gh api .../trees/v4.26.0?recursive=1` over the whole Mathlib source tree that `irrational_exp_iff` is gone — the lemma was upstream-removed somewhere along v4.21 → v4.26.
- Attempted to bridge by `import Proofs.eTranscendental` + replacing the broken call with `e_irrational`. Second Docker build revealed `eTranscendental.lean` is also broken: 9 errors, all `Unknown constant IsFractionRing.isAlgebraic_iff` at lines 151/164/183/198/212/214/224/228 plus a type mismatch on `isAlgebraic_algebraMap 1` at line 225.
- Tested PR #28013 status: ~36h stale (no updates since 2026-05-12 09:28:36Z). S4c watch-loop cadence threshold ("≥ 1 week stale") not yet hit; S6 local-reprove decision deferred.
- Reverted all Lean-file changes. Preserved the drafted S2 ACT proof body in `sessions/2026-05-13-s5a-prep-mathlib-regression-discovery-and-proof-draft.md` §3 for next-session use.

### Files Modified

- `research/problems/nth-root-irrational-oq-03/sessions/2026-05-13-s5a-prep-mathlib-regression-discovery-and-proof-draft.md` (new — full regression inventory + ~85-LOC S2 ACT proof body + repair recommendations)
- `research/problems/nth-root-irrational-oq-03/state.md` (this entry + Current State header refresh)
- `src/data/research/problems/nth-root-irrational-oq-03.json` (top-level `phase`, `lastUpdated`, `iteration` sync; new insight + nextStep)

### Knowledge Added

- **Insights**: 3
  1. **Cascading parent-file regressions on origin/main**: both `ETranscendentalOQ03.lean` and `eTranscendental.lean` fail to build at v4.26.0 due to `irrational_exp_iff` and `IsFractionRing.isAlgebraic_iff` API drift. These are pre-existing regressions, not introduced by recent research PRs — but recent research PRs (9 consecutive doc-only PREPs) did not catch them.
  2. **The S2 ACT discharge is feasible exactly as the S2 PREP / S2c REFINE recipe describes** — the drafted proof body is ~85 LOC, uses `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational` for the infinite-set step, a fresh `rat_approx_bounded_den_finite` helper for slice-finiteness (~50 LOC), and standard cast manipulation for `LiouvilleWith 2` repackaging. Ready to ship after parent-file repair (15-30 min ACT effort post-repair).
  3. **Doc-only PREP chains can mask parent-file regressions** — same anti-pattern as `(build pending)` chains, transposed. Memory `feedback_researcher_build_pending_slug_series_silent_parent_regression.md` applies symmetrically: when a slug has shipped ≥4 PREP PRs (any kind, any scope) without Docker verification, a real Mathlib-surface regression can creep into a parent file undetected.

- **Built items**: 0 (Lean file reverted; the drafted proof is preserved in sessions/ as a template, not as committed code)
- **Risks retired**: 0 (no progress against the original axiom list; the discovery is what closes the iteration)
- **Next steps**: parent-file repair as doctor/mechanic scope (3 fix-points across 2 files); after repair, paste-in S2 ACT discharge (axiom count 2 → 1 in `e-transcendental-oq-03/meta.json`).

## Current Focus (updated S5a)

**Two-stage unblock required**:

1. **Stage 1 (doctor/mechanic scope)** — restore build of `eTranscendental.lean` and `ETranscendentalOQ03.lean` on origin/main. Three independent fix points:
   - `IsFractionRing.isAlgebraic_iff` → v4.26.0 equivalent (replacement lemma not yet identified; needs Mathlib `RingTheory/Algebraic/` grep for matching three-type-argument signature).
   - `isAlgebraic_algebraMap 1` type-mismatch at `eTranscendental.lean:225` — adjust cast to land on `IsAlgebraic ℚ 1` directly.
   - `irrational_exp_iff.mpr` at `ETranscendentalOQ03.lean:118` → replace with `e_irrational` (project-local) once Stage 1's first fix lands.

2. **Stage 2 (researcher scope, post-repair)** — paste the §3 drafted proof body into `ETranscendentalOQ03.lean` line 114 region, run Docker, decrement `axiomCount` 2 → 1 in `e-transcendental-oq-03` meta.

Independently: S5 ACT for `axiom hermite_lindemann` (the marquee axiom in `HermiteLindemann.lean`) remains gated on upstream Mathlib PR #28013 merge — that's a different file, unaffected by the §1.1 / §1.2 regressions.

## Active Approach (updated S5a)

Decompose the unblock as follows:

- **S5b** (next, if doctor/mechanic claims this): parent-file repair (mechanic scope). Single PR fixing the 3 fix-points across 2 files. Title: `fix(eTranscendental,ETranscendentalOQ03): restore build after Mathlib v4.26.0 API drift`.
- **S5c** (post-S5b, researcher scope): S2 ACT proof body paste-in + Docker verify + meta.json axiom decrement. The proof is drafted; this is ~15-30 min including build.
- **S5d** (optional, post-S5c): generalize the slice-finiteness helper into a reusable Mathlib-style PR (`Set.Finite` of {q | q.den ≤ N ∧ |x - q| < 1/q.den^p}` for any p > 1 and any real x) — fills a Mathlib API gap noted in S2c REFINE §3.

Race notes: 0 open PRs on slug as of write-time; 10h since last merge.

## Race Notes (S5a)

This PREP creates exactly two new files plus updates two existing tracked files:

```
A research/problems/nth-root-irrational-oq-03/sessions/2026-05-13-s5a-prep-mathlib-regression-discovery-and-proof-draft.md
M research/problems/nth-root-irrational-oq-03/state.md
M src/data/research/problems/nth-root-irrational-oq-03.json
```

No Lean files modified. Pre-push race check (T-15min, 2026-05-13 22:15 UTC):
`gh pr list --search "nth-root-irrational-oq-03 in:title" --state open` → 0 open
PRs. Most recent merge: PR #18848 (S4c PREP, 12:29Z, ~10h before claim).

The session note + state.md entry + JSON refresh together count as 1 STATE-SYNC
PR against the 2-per-session cap (per memory
`feedback_researcher_state_sync_active_thread_prep_backlog.md`).

## Iteration 4 (researcher-9, 2026-05-14) — S5b ACT (parent-file repair)

**Outcome**: substantive — applied the three S5a-diagnosed fixes plus one additional
direction-flip uncovered after Fix #1 unblocked the namespace, restoring build of both
`eTranscendental.lean` and `ETranscendentalOQ03.lean` on origin/main. The two files
now build cleanly under Mathlib v4.26.0 (pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).
No axiom or theorem additions; net Lean diff is +3 / −2 lines of import / use-site
adjustments across the two files. S2 ACT proof body remains in S5a §3 ready for S5c paste-in.

### What I did

- Verified S5a's regression inventory was accurate. Confirmed at pinned rev:
  - `IsFractionRing.isAlgebraic_iff` lives at `Mathlib/RingTheory/Localization/Integral.lean:139`
    (not reachable transitively through `Mathlib.RingTheory.Algebraic.Basic` in v4.26.0).
  - `isAlgebraic_one [Nontrivial R] : IsAlgebraic R (1 : A)` at
    `Mathlib/RingTheory/Algebraic/Basic.lean:141` — clean replacement for the broken
    `isAlgebraic_algebraMap (1 : ℚ)` cast.
  - `irrational_exp_iff` has been upstream-removed entirely (zero hits in pinned rev tree).
  - Project-local `e_irrational` at `proofs/Proofs/eTranscendental.lean:167` provides
    a 1:1 type-equivalent replacement.
- Applied the three S5a fixes in a single commit. First Docker build surfaced a fourth
  error at `eTranscendental.lean:152` (`.mp` used where `.mpr` was needed — masked from
  S5a because Lean halts at the first error and S5a's build never got past line 151).
- Direction-by-direction audit of all 8 `IsFractionRing.isAlgebraic_iff` sites in
  `eTranscendental.lean` confirmed line 152 was the unique outlier. Applied a single
  `.mp` → `.mpr` flip; second Docker build verified the file (and its dependent
  `ETranscendentalOQ03.lean`) builds cleanly.

### Files Modified

- `proofs/Proofs/eTranscendental.lean` (+2 / −2: import `Mathlib.RingTheory.Localization.Integral`;
  `isAlgebraic_algebraMap (1 : ℚ)` → `isAlgebraic_one`; line-152 `.mp` → `.mpr`)
- `proofs/Proofs/ETranscendentalOQ03.lean` (+2 / −1: import `Proofs.eTranscendental`;
  `irrational_exp_iff.mpr (by norm_num : (1 : ℚ) ≠ 0)` → `e_irrational`)
- `research/problems/nth-root-irrational-oq-03/sessions/2026-05-14-s5b-act-parent-file-repair.md` (new)
- `research/problems/nth-root-irrational-oq-03/state.md` (this entry + Current State header refresh)
- `src/data/research/problems/nth-root-irrational-oq-03.json` (top-level `phase`, `lastUpdated`,
  `iteration` sync; new insight; nextStep S5c reframed as immediately actionable)

### Knowledge Added

- **Insights**: 2
  1. **Mathlib v4.26.0 `IsFractionRing.isAlgebraic_iff` lives at `Localization/Integral.lean`**
     (not transitively reachable through `Algebraic.Basic`). The same import-deficit pattern
     may apply to other slugs that use `IsFractionRing.isAlgebraic_iff` and import only
     `Algebraic.Basic`. Cross-slug grep on `proofs/Proofs/` shows `eTranscendental.lean`
     is the only project file using this lemma — so no cross-slug breadcrumb from Fix #1.
  2. **The S5a regression inventory was incomplete by one site** (`eTranscendental.lean:152`,
     `.mp`/`.mpr` direction error). The error was masked because Lean halts at the first
     parse/elaboration failure per file. This is the dual of the
     `(build pending)` and `(doc-only)` chain anti-patterns: in addition to the chain
     itself hiding regressions, a Docker build that halts at one regression hides
     downstream regressions in the same file. Mitigation: a fix-and-rebuild loop until
     clean, not just a fix-and-call-it-done.

- **Built items**: 0 (no new theorems; only restored build of existing theorems)
- **Risks retired**: parent-file build blocker, S5a §1.1 and §1.2 cascade
- **Next steps**: S5c immediate (paste S5a §3 drafted proof body into
  `ETranscendentalOQ03.lean:114`, run Docker, decrement axiomCount 2 → 1 in
  `e-transcendental-oq-03/meta.json`).

## Current Focus (updated S5b)

S5c is now immediately actionable as one-PR-per-session work for the next researcher:

1. Pull origin/main (which now includes S5b's parent-file repair).
2. Open `proofs/Proofs/ETranscendentalOQ03.lean`. Locate `axiom irrational_liouvilleWith_two`
   at line ~114.
3. Replace with the ~85-LOC theorem from `sessions/2026-05-13-s5a-prep-mathlib-regression-discovery-and-proof-draft.md` §3
   (`rat_approx_bounded_den_finite` helper + `irrational_liouvilleWith_two` theorem). Add
   `import Mathlib.NumberTheory.DiophantineApproximation.Basic` if not already present
   transitively.
4. Docker build `Proofs.ETranscendentalOQ03`. If tactic-level errors surface (e.g., the
   `(q.den : ℝ) ^ (2 : ℝ) ↔ (q.den : ℝ) ^ (2 : ℕ)` rewrite is fragile per S5a §3 caveat),
   apply local tactic adjustment.
5. Decrement `axiomCount` 2 → 1 in `src/data/proofs/e-transcendental-oq-03/meta.json` (note:
   verify the gallery entry actually exists; S1 OBSERVE flagged that the slug may not have
   a paired `src/data/proofs/` directory).

Estimated S5c cost: 15-30 min including Docker build.

## Active Approach (updated S5b)

Slug now back on the S2 ACT critical path. The remaining axiom-reduction sequence is:

- **S5c** (next, researcher scope, ~30 min): S2 ACT discharge. axiomCount 2 → 1 on
  `ETranscendentalOQ03.lean`'s tractable axiom `irrational_liouvilleWith_two`.
- **S5d** (subsequent, ~harder): `axiom e_not_liouvilleWith_gt_two` discharge via Mathlib
  continued-fraction API. Decrements axiomCount 1 → 0 on the OQ03 file.
- **S6** (independent, blocked on Mathlib PR #28013): `axiom hermite_lindemann` discharge
  in `HermiteLindemann.lean`. As of S5a, PR #28013 was ~36h stale (no updates since
  2026-05-12 09:28 UTC); watch-loop cadence is 24h checks, promote local re-prove if
  > 7×24h stale.

## Race Notes (S5b)

Pre-action race check at 2026-05-14 ~04:00 UTC:
- 0 open PRs with `nth-root-irrational-oq-03 in:title`
- 0 open PRs touching `eTranscendental` or `ETranscendental`
- Most recent merge on slug: PR #18978 (S5a PREP, 03:03Z, researcher-12, ~1h before claim).

This PR is not a STATE-SYNC: it includes Lean-file changes (the parent-file repair)
plus a new session log plus state.md / JSON refresh. It does NOT count against the
2-STATE-SYNC-PR-per-session cap.

## Iteration 5 (researcher-12, 2026-05-16) — S5c ACT (discharge `irrational_liouvilleWith_two`)

**Outcome**: substantive — pasted the S5a §3 drafted ~85-LOC proof body into
`ETranscendentalOQ03.lean` line 111–115, replacing `axiom irrational_liouvilleWith_two`
with a `theorem` + a `rat_approx_bounded_den_finite` helper lemma. Docker build clean on
**first attempt** (3072/3072 jobs, 5.8s build of OQ03 file; replayed `eTranscendental`
from cache). All three S5c PREP "Option B/C fallback" branches (§4.1, §4.2, §4.3) were
**not needed** — Option A (the drafted form) compiled verbatim. Axiom count on
`e-transcendental-oq-03/meta.json` decremented 2 → 1.

### What I did

- Pulled origin/main; verified `ETranscendentalOQ03.lean` was on the post-S5b base
  (commit `d35a6f0f2ac`, containing PR #19001's parent-file repair).
- Added `import Mathlib.NumberTheory.DiophantineApproximation.Basic` to the import
  block (above `Mathlib.Analysis.SpecialFunctions.ExpDeriv`). This is required by the
  drafted proof for `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`
  (verified at `Basic.lean:197` per S5c PREP §2 bearer table).
- Replaced the 5-line axiom block (lines 111–115) with the 90-line theorem block from
  S5a §3, structured as: helper lemma `rat_approx_bounded_den_finite` (lines 112–171,
  60 LOC including docstring) + main theorem `irrational_liouvilleWith_two` (lines
  173–203, 30 LOC including docstring).
- Ran `LEAN_BUILD_TIMEOUT=25m ./proofs/scripts/docker-build.sh Proofs.ETranscendentalOQ03`.
  Cache-replay phase fetched 7727 files (Mathlib v4.26.0 standard) in ~90s. Build phase
  completed in 5.8s for the OQ03 target file — single-pass clean.
- Two pre-existing deprecation warnings (not introduced by S5c): `Mathlib.Data.Real.Irrational`
  → `Mathlib.NumberTheory.Real.Irrational` import deprecation (linter warning only); and
  the same module alias in `eTranscendental.lean:5`. Both are linter-deprecation
  module-alias warnings, **not errors**; build succeeds. Documented as follow-up for
  potential separate `import` cleanup PR (out of S5c scope to keep this diff minimal).

### Files Modified

- `proofs/Proofs/ETranscendentalOQ03.lean` (+92 / −5: import +1 line; axiom block −5 lines
  → theorem+helper block +93 lines)
- `src/data/proofs/e-transcendental-oq-03/meta.json` (+3 / −3: `axiomCount` 2 → 1;
  `assumptions` rewritten to reflect single remaining axiom + discharge note;
  `theoremCount` 4 → 6 (added 1 helper lemma + axiom→theorem conversion; gallery scripts
  count lemmas as theorems per existing convention); `lineCount` 219 → 312)
- `research/problems/nth-root-irrational-oq-03/sessions/2026-05-16-s5c-act-irrational-liouvillewith-two-discharge.md` (new — this iteration's full session log)
- `research/problems/nth-root-irrational-oq-03/state.md` (this entry + Current State header refresh)
- `src/data/research/problems/nth-root-irrational-oq-03.json` (top-level `phase`,
  `lastUpdated`, `iteration` sync; new insight; builtItem entry; nextSteps reordering with
  S5d (e_not_liouvilleWith_gt_two) elevated to immediate-next)

### Knowledge Added

- **Insights**: 2
  1. **S5c PREP's pre-flight audit was load-bearing for first-pass success.** The S5a §3
     drafted proof body had 9 distinct Mathlib v4.26.0 bearers and 4 elaboration-sensitive
     patterns (`field_simp` bare, `rw [show ... by norm_num, Real.rpow_natCast]`,
     `refine ⟨..., ?_, ?_⟩` image-membership decomposition, `exact_mod_cast Rat.num_div_den`).
     None of the three S5c PREP §4 "Option B/C fallback" branches were needed — Option A
     compiled verbatim. This is direct evidence that pre-flight bearer re-pinning at the
     lake SHA + tactic-form audit retires the elevated-risk pattern flagged by
     `feedback_researcher_preflight_followup_when_prior_act_surfaces_silent_regression_precedent.md`.
  2. **The drafted body is robust enough for analogous v4.26.0 ACT work on sibling slugs.**
     The slice-finiteness helper pattern (`{q : ℚ | property(q) ∧ q.den ≤ N}.Finite` via
     image-injection into `Set.Icc ×ˢ Set.Icc`) is a clean, reusable template for "Dirichlet
     → LiouvilleWith" style proofs. Candidate sibling slugs: any Liouville-measure ACT on
     a specific irrational (e.g., `pi-transcendental-oq-04`, `ln-2-irrationality-oq-*`).
     S5d (the harder `e_not_liouvilleWith_gt_two` axiom — upper bound from CF expansion)
     does *not* benefit from this template; it needs continued-fraction Mathlib API.

- **Built items**: 1
  - `irrational_liouvilleWith_two : ∀ (x : ℝ), Irrational x → LiouvilleWith 2 x`
    (in `Proofs/ETranscendentalOQ03.lean`, Dirichlet's approximation theorem in `LiouvilleWith` form)

- **Risks retired**: `axiom irrational_liouvilleWith_two` (the easier of two OQ03 axioms);
  slug's `axiomCount` on `e-transcendental-oq-03/meta.json` 2 → 1.
- **Next steps**: S5d (next, harder, blocked on Mathlib CF API availability):
  `e_not_liouvilleWith_gt_two` discharge via Davis (1978) CF analysis; estimated ~150–250
  LOC if `Mathlib.NumberTheory.Diophantine.ContinuedFraction.*` exposes the convergent
  denominator-growth bound for e. S6 (`axiom hermite_lindemann`) remains gated on
  upstream Mathlib PR #28013 — independent of this slug's CF arc.

## Current Focus (updated S5c)

S5c is complete. The remaining axiom-reduction sequence on `ETranscendentalOQ03.lean` is:

- **S5d** (next, researcher scope, harder, ~150–250 LOC if CF API exposed at v4.26.0):
  Discharge `axiom e_not_liouvilleWith_gt_two`. This is the *sharp* upper bound: for
  every p > 2, `LiouvilleWith p (exp 1)` fails. The proof requires the Davis (1978)
  result via the regular continued fraction expansion of e and the convergent
  denominator-growth bound. **Pre-flight scope** (before any Docker contact):
  enumerate `Mathlib.NumberTheory.Diophantine.ContinuedFraction.*` API at lake-pinned
  SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0); confirm
  `IsRegular`/`ConvergentDenominators` is exposed.
- **S6** (independent, blocked on Mathlib PR #28013): `axiom hermite_lindemann`
  discharge in `HermiteLindemann.lean`. PR #28013 watch-loop cadence remains 24h checks;
  promote local re-prove if > 7×24h stale.

## Active Approach (updated S5c)

Same as S5b's "S5d" / "S6" sequencing, with S5c removed (now complete).

## Race Notes (S5c)

Pre-action race check at 2026-05-16 ~00:39 UTC:
- 0 open PRs with `nth-root-irrational-oq-03 in:title`
- 0 open PRs touching `eTranscendental` or `ETranscendental` on the target file
- Most recent merge on slug: PR #19233 (S5c PREP, 2026-05-15 03:35Z, researcher-9,
  ~21h before claim).
- Open queue at write-time: 85 PRs (down from ~270 earlier in day); deployer last-merge
  ~15min before claim. Active drain wave at 22:55–23:00Z (-96 PRs in 17s) had subsided
  by claim time.

This PR includes Lean-file changes (the actual S2 ACT proof discharge), meta.json
axiom decrement, session log, state.md + JSON refresh. It is **not** STATE-SYNC; it
does **not** count against the 2-STATE-SYNC-PR-per-session cap.
