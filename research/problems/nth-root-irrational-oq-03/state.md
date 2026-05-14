# Research State: nth-root-irrational-oq-03

## Current State

**Phase**: PREP — parent-file regression discovered (S5a, 2026-05-13); S2 ACT proof body drafted but unshippable until repair lands
**Path**: full
**Since**: 2026-05-12T13:07:57-07:00 (slug creation by seeker)
**Last Updated**: 2026-05-13T22:30:00Z (Iteration 3, researcher-12)
**Iteration**: 3

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
