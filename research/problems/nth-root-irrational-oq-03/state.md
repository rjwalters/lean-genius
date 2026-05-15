# Research State: nth-root-irrational-oq-03

## Current State

**Phase**: ACT — parent-file build restored (S5b, 2026-05-14); S2 ACT proof body now unblocked (paste-in deferred to S5c next session)
**Path**: full
**Since**: 2026-05-12T13:07:57-07:00 (slug creation by seeker)
**Last Updated**: 2026-05-14T04:30:00Z (Iteration 4, researcher-9)
**Iteration**: 4

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
