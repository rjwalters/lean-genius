# Current State

**Phase**: ACT (S6 ACT FINDING-E APPLIED — extended `IbragimovHypotheses` with the two `past_le` / `future_le` fields per the S5d STATE-SYNC checklist Step 2; 14 → 16 fields, +14 LOC including docstrings; Docker-verified 3131 jobs clean; the structural gap blocking S5c's level-set decomposition is now closed and Step 2 of the 7-step S5c+1 plan is shipped. Steps 3-7 (level-set decomp, bilinear expansion, pointwise indicator_covariance_le_alpha application, Hölder + Markov, sorry-count 2 → 1) remain for a follow-up S7 ACT.)
**Since**: 2026-06-01T00:00:00Z
**Iteration**: 10 (S5d STATE-SYNC iter 9 → this S6 ACT iter 10)
**Last Updated**: 2026-06-01 (researcher-1)

## S6 ACT FINDING-E APPLIED (researcher-1, 2026-06-01, this PR — `IbragimovHypotheses` +2 fields, build verified)

Closes Step 2 of the S5c+1 ACT 7-step checklist (per S5d STATE-SYNC §5):
extend `IbragimovHypotheses` (currently 14 fields at lines 157–189 of
`CentralLimitTheoremOQ02OQ04.lean`) with the two sub-σ ≤ ambient
relations required by `indicator_covariance_le_alpha`'s call site in
the level-set decomposition.

### Files changed

* `proofs/Proofs/CentralLimitTheoremOQ02OQ04.lean`:
  * Lines 73–74: docstring update for the structure summary
    ("14 fields" → "16 fields — S6 ACT adds `past_le` and `future_le`
    per Finding E from PR #19289").
  * Lines 181–192: two new fields inserted after `future_measurable`
    (was line 180), before `alpha_bound` (was line 182):

    ```lean
    /-- The past σ-algebra at time `k` is a sub-σ-algebra of the
        ambient measurable structure on `Ω`. (...) -/
    past_le : ∀ k, pastSigma k ≤ (inferInstance : MeasurableSpace Ω)
    /-- The future σ-algebra at time `k` is a sub-σ-algebra of the
        ambient measurable structure on `Ω`. Companion to `past_le`. -/
    future_le : ∀ k, futureSigma k ≤ (inferInstance : MeasurableSpace Ω)
    ```

    Note: `(inferInstance : MeasurableSpace Ω)` rather than bare
    `inferInstance` — the structure's elaboration context can't unify
    `≤`'s implicit `MeasurableSpace Ω` argument without the explicit
    type ascription (build #1 failed with "type class instance
    expected `?m.42`"; build #2 with the ascription passed clean).

### Diff stats

* `lineCount`: 719 → 733 (+14 net: 2 new fields × 1 statement-line +
  ~6 lines of docstrings each).
* `theoremCount`: 13 (unchanged — structure field count grew, no
  theorems added or removed).
* `definitionCount`: 4 (unchanged).
* `sorries`: 2 (unchanged — `davydov_covariance_inequality` line 475
  and `mixing_clt_ibragimov` line 671; both deferred to S7+).
* `axiomCount`: 0 (unchanged — but note: per the project's Axiom
  Integrity Policy, structure-encoded hypotheses are
  assumption-carrying. The existing 14 fields of `IbragimovHypotheses`
  already constituted such assumptions and were not previously
  counted; this PR adds 2 more in the same spirit. Whether to
  retroactively count the structure fields is an audit decision left
  out of scope for this ACT; `meta.json` axiomCount is preserved at 0
  to match the pre-existing convention.)

### Build verification

```
./proofs/scripts/docker-build.sh Proofs.CentralLimitTheoremOQ02OQ04
⚠ [3130/3131] Replayed Proofs.CentralLimitTheoremOQ02
⚠ [3131/3131] Built Proofs.CentralLimitTheoremOQ02OQ04 (4.4s)
Build completed successfully (3131 jobs).
```

Sorries surfaced: the expected 2 in this file (lines 522 and 718 after
shift) + 3 in parent `CentralLimitTheoremOQ02.lean` (480, 519, 538;
reused-by-reference, not in scope).

Mathlib SHA: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0;
unchanged since pre-S5b era).

### Strategic positioning

* **Leaf-only PR**: no parent-file changes. Per S5d STATE-SYNC §5
  Step 1's "ship IbragimovHypotheses-only sub-ACT under build-pending
  qualifier ONLY if structure extension is leaf-only" — this PR
  satisfies that condition (and goes further: it is build-verified,
  not build-pending).
* **No callers of `IbragimovHypotheses` constructed it**: a grep
  shows the structure is referenced only as a theorem parameter
  `(H : IbragimovHypotheses μ X δ C r)` at lines 536, 549, 615, 708 —
  never instantiated via `⟨...⟩`. Adding fields therefore breaks no
  downstream code.
* **Parent file co-extension queued**: `AlphaMixingSequence` in
  `CentralLimitTheoremOQ02.lean:427-442` has the same gap. This PR
  does NOT touch the parent; the parent fix is queued for S7+ or a
  sibling mechanic PR (non-leaf, multiple importers → cascade risk
  requires its own Docker run).

### S7 ACT picker (when Docker stays healthy, ~60-90 min)

Now that Step 2 is shipped, the remaining 5 steps from the S5d
checklist are tractable in a single follow-up session:

3. Apply level-set decomposition `X = ∫₀^∞ (𝟙_{X>t} − 𝟙_{X<-t}) dt`
   for both `X` and `Y` (~15 LOC).
4. Bilinear expansion of `Cov(X, Y)` into double integral (~10 LOC).
5. Pointwise application of `indicator_covariance_le_alpha` at each
   `(t, s)` threading `H.past_le 0 _ h_sub` + `H.future_le 0 _ h_sub`
   for the ambient measurability arguments (~20 LOC); `h_sub` from
   `@measurableSet_lt Ω ℝ _ _ (H.pastSigma 0) X (fun _ => t)
   (H.past_measurable 0) measurable_const`.
6. Hölder amplification with exponents `(p, p/(p-1))` (~25 LOC) +
   Markov tail bound for truncated piece (~15 LOC).
7. Docker-verify. Target sorry count: 2 → 1 (close
   `davydov_covariance_inequality`; preserve `mixing_clt_ibragimov`
   as S8+ target).

Session memo: `sessions/2026-06-01-s6-act-finding-e-applied.md`.

---



## S5d STATE-SYNC (researcher-6, 2026-05-16, doc-only — post-double-PREP catchup + Finding E surface)

Doc-only STATE-SYNC iteration catching state.md up to the two merged PRs that landed
since the 2026-05-14 S5b build-verify section was authored:

1. **PR #19050** (S5c-prep ACT, researcher-12, merged 2026-05-15T16:27:31Z) shipped
   one fully-proven theorem `indicator_covariance_le_alpha` at lines 443-485 of
   `CentralLimitTheoremOQ02OQ04.lean` (35 LOC incl. docstring), bridging the S4
   algebraic identity `indicator_pair_covariance_eq` and the S5b indicator α-bound
   `davydov_indicator_bound` into the covariance-form indicator α-bound. Build
   verified 3131 jobs. theoremCount 12 → 13. JSON iter 7 → 8 + focus + nextAction
   refresh. **state.md NOT updated by #19050** (recurring researcher-12 pattern
   of JSON-without-state.md sync).
2. **PR #19289** (S5c-prep sibling audit, researcher-12, merged
   2026-05-15T11:01:22Z) shipped doc-only sibling-audit memo (~406 LOC) reviewing
   PR #19050 with 4 findings (A-F). The headline is **Finding E** — a structural
   gap in `IbragimovHypotheses` blocking S5c proper.

### Finding E summary (condensed; full re-cite in S5d memo §4)

`indicator_covariance_le_alpha` requires BOTH sub-σ measurability AND ambient
`MeasurableSet` at every call site. The natural S5c call site (level-set
decomposition `X = ∫₀^∞ (𝟙_{X>t} − 𝟙_{X<-t}) dt`) produces sub-σ measurable
level sets via `@measurableSet_lt Ω ℝ _ _ (H.pastSigma 0) X (fun _ => t)
(H.past_measurable 0) measurable_const`, but cannot produce ambient
`MeasurableSet {ω | X ω > t}` without a `pastSigma k ≤ inferInstance` field
on the structure.

**Fix (Path B per Finding E, recommended)** — +2 fields to `IbragimovHypotheses`
(currently 14 fields at lines 157-189):

```lean
  /-- The past σ-algebra is a sub-σ-algebra of the ambient measurable structure. -/
  past_le : ∀ k, pastSigma k ≤ inferInstance
  /-- The future σ-algebra is a sub-σ-algebra of the ambient measurable structure. -/
  future_le : ∀ k, futureSigma k ≤ inferInstance
```

(Insertion point: after line 180 `future_measurable`, before line 182
`alpha_bound`. Result: structure 14 → 16 fields, +5 LOC including docstrings
and blank-line padding.)

**Parent file co-extension** (out of scope for S5c+1 ACT; queued for S5c+2 or
sibling mechanic): `AlphaMixingSequence` in `CentralLimitTheoremOQ02.lean:427-442`
has the same gap; cascade risk on non-leaf parent requires Docker verification.

### Files changed this S5d STATE-SYNC cycle

1. NEW `sessions/2026-05-16-s5d-state-sync-postdoubleprep-finding-e.md`
   (~370 LOC, 8 sections: drift inventory + S5c-prep ACT absorption + sibling
   audit absorption + Finding E condensed + refreshed S5c+1 ACT plan +
   leanFiles[] drift handoff + not-done/out-of-scope + race-safety/refs).
2. EDIT this state.md (head replace preserving Sessions 1-S5b BV verbatim +
   this Session-S5d entry).
3. EDIT `src/data/research/problems/central-limit-theorem-oq-02-oq-04.json`
   (`currentState.{iteration 8→9, since, focus rewrite absorbing Finding E,
   nextAction rewrite 6→7 steps, lastUpdate, attemptCounts.total 5→6}` +
   `knowledge.{progressSummary prepend S5d paragraph, insights += 1 Finding E
   insight, builtItems += 1 memo entry, nextSteps[0] rewrite}`).

0 Lean edits. 0 meta.json edits. 0 problem.md / 0 knowledge.md edits.
0 axiom change (0 / 0). 0 sorry change (2 preserved: line 475
`davydov_covariance_inequality`, line 671 `mixing_clt_ibragimov`).

### LeanFiles[] drift (informational only — NOT touched; mechanic territory)

JSON `leanFiles[i]` for slug Lean file shows `lineCount: 553, theoremCount: 9`
but actual at `origin/main` is **719 lines, 13 theorems** (sorryCount 2,
defCount 4 with structure-as-def convention — these two confirmed correct).
Ready-to-paste mechanic diff in S5d memo §6. **DO NOT** self-edit `leanFiles[]`
per MEMORY pattern (auto-populated by `enrich-research.ts`).

### Host infra this S5d STATE-SYNC cycle

- **Docker daemon still hung** (~7.5+ h cumulative, same B1 condition as
  cramers-rule S15 PREP cycle ~30 min before this; same researcher-6 session).
- **Disk**: 5.4 Gi avail (degrading; AMBER but above ~5 Gi floor).
- **Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0,
  unchanged since pre-S5b era; bearer surface stable per S5c-prep ACT
  3131-job build on 2026-05-15).
- **0 open PRs** for this slug at cycle start.
- **0 sibling `iter-<TS>` branches** on origin.

### Refreshed S5c+1 ACT picker checklist (7 steps; supersedes 6-step from prior JSON)

1. Confirm Docker daemon healthy.
2. Apply Finding E +5 LOC: extend `IbragimovHypotheses` with `past_le` and
   `future_le` fields (insert after line 180, before line 182).
3. Apply level-set decomposition for X and Y (~15 LOC).
4. Bilinear expansion of `Cov(X, Y)` into double integral (~10 LOC).
5. Pointwise application of `indicator_covariance_le_alpha` at each (t, s)
   threading `H.past_le 0 _ h_sub` + `H.future_le 0 _ h_sub` (~20 LOC).
6. Hölder amplification + Markov tail bound (~40 LOC).
7. Docker-verify. Target sorry-count: 2 → 1.

Estimated S5c+1 ACT wall time (when Docker is healthy): 60-90 min.

Session note: `sessions/2026-05-16-s5d-state-sync-postdoubleprep-finding-e.md`.

## S5c-prep sibling audit (researcher-12, 2026-05-15, PR #19289 — Finding E structural gap; doc-only)

Session memo at `sessions/2026-05-15-s5c-prep-sibling-audit.md` (~406 LOC).
Reviewed PR #19050 with 4 findings (A-F); headline is **Finding E** — structural
gap in `IbragimovHypotheses` requiring +2 fields `past_le` and `future_le` (sub-σ
≤ ambient measurable structure) for S5c proper to land cleanly. See S5d STATE-SYNC
§3-4 (above) for full condensation.

## S5c-prep ACT (researcher-12, 2026-05-15, PR #19050 — indicator_covariance_le_alpha bridge; build verified)

Session memo at `sessions/2026-05-14-s5c-prep-indicator-covariance-le-alpha.md`
(~153 LOC). Shipped one fully-proven theorem `indicator_covariance_le_alpha`
at lines 443-485 (35 LOC incl. docstring), bridging the S4 `indicator_pair_covariance_eq`
and S5b `davydov_indicator_bound` into the covariance-form indicator α-bound.
Build verified Docker 3131 jobs. theoremCount 12 → 13. Lean file 553 → 684 LOC
(+131; includes some docstring polish + line-419 unused-simp-arg cleanup).
See S5d STATE-SYNC §2 (above) for full absorption notes.

## S5b build-verify (researcher-9, 2026-05-14, this PR — retire `(build pending)` qualifier)

PR #18728 (S5b ACT, merged 2026-05-13T10:17:09Z) shipped under the `(build pending)` qualifier with the stated reason being the worktree `proofs/.lake` self-referential symlink. That symlink does **not** affect `./proofs/scripts/docker-build.sh`, which mounts its own `/lean/.lake` inside the Docker container — the host worktree's `.lake` is irrelevant. Build re-run from a fresh worktree off `origin/main` (sha `2afb1b79c0a`):

```
./proofs/scripts/docker-build.sh Proofs.CentralLimitTheoremOQ02OQ04
⚠ [3130/3131] Replayed Proofs.CentralLimitTheoremOQ02
⚠ [3131/3131] Built Proofs.CentralLimitTheoremOQ02OQ04 (3.3s)
Build completed successfully (3131 jobs).
```

Sorries surfaced (the expected 2; same as `meta.json`):

* `Proofs/CentralLimitTheoremOQ02OQ04.lean:475:8` — `davydov_covariance_inequality` (S5c target, L^p density step).
* `Proofs/CentralLimitTheoremOQ02OQ04.lean:671:8` — `mixing_clt_ibragimov` (S6+ target).

Parent file `Proofs/CentralLimitTheoremOQ02.lean` carries its own 3 sorries (lines 480, 519, 538), all reused-by-reference and not in scope for this slug.

Doc-only changes:
* `state.md` — flip `[BUILD PENDING]` to `[BUILD VERIFIED]` in the S5b section header below; refresh top-of-file Phase/Since/Iteration/Last Updated.
* `src/data/research/problems/central-limit-theorem-oq-02-oq-04.json` — top-level `phase: ORIENT → ACT` (drift fix; gallery listings derived from this), `lastUpdate` advanced; `currentState.{phase,since,iteration,focus,nextAction}` refreshed to post-S5b state; `knowledge.progressSummary` and `knowledge.nextSteps[0]` updated. No Lean changes.

**No Lean changes.** PR #18728 shipped a sound proof; this STATE-SYNC just retires the stale `(build pending)` qualifier and resyncs trackers.

### Linter note (out of scope)

The Docker build surfaced one cosmetic linter warning at line 419 in the pre-existing `indicator_pair_covariance_eq` (S4 contribution, shipped via #17939 — **not** part of S5b's contribution):

```
Proofs/CentralLimitTheoremOQ02OQ04.lean:419:12: This simp argument is unused: Set.indicator_apply
```

The `by_cases hωA <;> by_cases hωB <;> simp [Set.indicator_apply, Set.mem_inter_iff, hωA, hωB]` proof closes via `simp [Set.mem_inter_iff, hωA, hωB]` alone (under Mathlib v4.26.0, the four explicit cases unfold the indicator without needing the `indicator_apply` lemma in the simp set). Flagged for a future cleanup pass; **not bundled with this build-verify STATE-SYNC** to keep scope minimal per "(build pending)" retirement template (cf. #19025 cayley-hamilton-minpoly-oq-03-oq-02 S2 build-verify).

## S5b (researcher-3, 2026-05-13, PR #18728 — ingredient (3) `davydov_indicator_bound`)

**Davydov structural decomposition — all 3 named order-theory ingredients now proven.**

Closes the third and final order-theory ingredient in the structural
decomposition of `davydov_covariance_inequality` documented since S4:

```lean
theorem davydov_indicator_bound
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (σPair : Fin 2 → MeasurableSpace Ω)
    {A B : Set Ω}
    (hA_meas : @MeasurableSet Ω (σPair 0) A)
    (hB_meas : @MeasurableSet Ω (σPair 1) B) :
    |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal| ≤
      CentralLimitTheoremOQ02.alphaMixingCoeff μ (σPair 0) (σPair 1)
```

### Proof strategy

The 4-fold nested supremum defining `alphaMixingCoeff` is peeled one layer at
a time:

* **Set Ω layers** (outer over `A'`, middle over `B'`): apply `le_ciSup_of_le`
  with `BddAbove` witnesses derived uniformly from `indicator_cov_le_one`
  (the [0, 1] envelope proven in S4). Each `BddAbove` is established by
  chaining three `Real.iSup_le _ (by norm_num)` discharges through the inner
  ⨆ layers, bottoming out at `indicator_cov_le_one`.

* **Prop layers** (`_hA : @MeasurableSet Ω (σPair 0) A` and `_hB : ...`):
  apply `ciSup_pos`
  (`Mathlib.Order.ConditionallyCompletePartialOrder.Indexed` line 95). Since
  the body is constant in the propositional binder, `ciSup_pos` reduces
  `⨆ (h : p), f h` to `f hp` whenever `p` holds — exactly our situation
  with `hA_meas`, `hB_meas`.

### Key technical tricks

The two `BddAbove` witnesses for the `Set Ω` layers are constructed
identically to the proof of `alphaMixingCoeff_le_one`: `refine ⟨1, ?_⟩`, then
peel inner ⨆ layers with `Real.iSup_le _ (by norm_num)`, bottoming out at
`indicator_cov_le_one`. The S4 [0, 1] envelope thus does double duty as both
the *upper bound* witness (S5 `alphaMixingCoeff_le_one`) and the *BddAbove*
witness (S5b, this PR).

The `ciSup_pos` for Prop layers sidesteps the `BddAbove` discharge for
`Sort*`-indexed iSup that would have been required had we tried to peel all
4 layers uniformly via `le_ciSup_of_le`. `ciSup_pos` is stated for arbitrary
`ConditionallyCompletePartialOrder` (so applies to ℝ) and only requires that
the proposition hold — exactly the hypothesis we have at the call site.

### Strategic positioning

* **Non-overlapping with all 5 open same-slug PRs** (#17810, #17826, #17943,
  #17947 are S3/S4 stale build-pending; #18439 is an obsolete auditor meta
  drift bump already superseded by #18440 merged at 2026-05-13T02:06:50Z).
  This PR adds a single theorem strictly downstream of S5 in Part III, just
  before Part IV. No conflict with any open work.
* **Closes ingredient (3)** of the Davydov decomposition. With (1)
  `alphaMixingCoeff_le_one`, (2) `alphaMixingCoeff_nonneg` (both S5) and (3)
  `davydov_indicator_bound` (S5b, this PR) all proven, the only remaining
  step to discharge `davydov_covariance_inequality` is the L^p density step
  (S5c target, ~100 lines: truncation + Hölder).
* **Closes parent file's deferred order-theory plumbing**: the parent file
  `CentralLimitTheoremOQ02.lean` line 444 omitted `alphaMixingCoeff_nonneg`
  due to nested-ciSup elaboration complexity. S5/S5b show that the
  combination of `Real.iSup_nonneg` / `Real.iSup_le` (reflectively in
  `Sort*`) for Type+Prop layers and `ciSup_pos` for Prop-only layers fully
  resolves the elaboration concern.

### Counts

* `lineCount`: 610 → **684** (+74 net: ~36 lines of one new proven theorem
  with full docstring explaining the layer-peeling structure; the Part IV
  docstring of `davydov_covariance_inequality` updated +6 lines to mark
  ingredient (3) as proven and shift the L^p density step to S5c; file
  header docstring updated to record S5b session).
* `theoremCount`: 11 → **12** (+1 fully proven, no new sorries).
* `definitionCount`: 4 (unchanged).
* `sorries`: **2** (unchanged — this PR does not touch any existing sorry;
  `davydov_covariance_inequality` and `mixing_clt_ibragimov` remain as
  S5c / S6+ targets).
* `axiomCount`: 0 (unchanged).

### Build status

**[BUILD VERIFIED]** — researcher-9, 2026-05-14. The S5b qualifier was a
false alarm: `./proofs/scripts/docker-build.sh` mounts `/lean/.lake` inside
the Docker container and ignores the host worktree's self-referential
`proofs/.lake` symlink. Verified from a fresh worktree off
`origin/main 2afb1b79c0a`:

```
./proofs/scripts/docker-build.sh Proofs.CentralLimitTheoremOQ02OQ04
⚠ [3130/3131] Replayed Proofs.CentralLimitTheoremOQ02
⚠ [3131/3131] Built Proofs.CentralLimitTheoremOQ02OQ04 (3.3s)
Build completed successfully (3131 jobs).
```

The proof uses only Mathlib API surfaced in the build:

* `le_ciSup_of_le` (`Mathlib.Order.ConditionallyCompleteLattice.Indexed`
  line 146): `BddAbove (range f) → ∀ i, a ≤ f i → a ≤ ⨆ j, f j`.
* `ciSup_pos`
  (`Mathlib.Order.ConditionallyCompletePartialOrder.Indexed` line 95):
  `(hp : p) → ⨆ h : p, f h = f hp` (works for ℝ as a
  ConditionallyCompletePartialOrder).
* `Real.iSup_le` (`Mathlib.Data.Real.Archimedean` line 236),
  `indicator_cov_le_one` (S4, line 229), `Set.range` — in scope.

Only the expected 2 sorries (`davydov_covariance_inequality` line 475 and
`mixing_clt_ibragimov` line 671) remain, matching `meta.json`.

### Next iteration (S5c / S6)

Two productive paths now open:

1. **S5c ACT** (~100 lines): L^p density step — truncate `X` and `Y` to
   bounded random variables `X^N := X · 1_{|X| ≤ N}` and `Y^M`, apply
   indicator decomposition `X^N = ∫_0^N 1_{X > t} − 1_{X < -t} dt`, expand
   the covariance bilinearly into a double integral over indicator pairs,
   apply `davydov_indicator_bound` pointwise, then Hölder to recover the
   `‖X‖_p · ‖Y‖_p` factor and bound the tail via Markov + Chebyshev.
2. **Joint tuple stationarity** (S6 prerequisite for Bernstein blocks),
   ~100 lines.

---

## S5 (researcher-3, 2026-05-12, PR #18227 — order-theory ingredients (1) & (2))

**Davydov structural decomposition — 2 of 3 named ingredients now proven.**

This narrow PR closes two of the three named order-theory ingredients in the
structural decomposition of `davydov_covariance_inequality` (documented inline
since S4):

```lean
theorem alphaMixingCoeff_nonneg {μ : Measure Ω}
    (σPair : Fin 2 → MeasurableSpace Ω) :
    0 ≤ CentralLimitTheoremOQ02.alphaMixingCoeff μ (σPair 0) (σPair 1) := by
  unfold CentralLimitTheoremOQ02.alphaMixingCoeff
  apply Real.iSup_nonneg; intro _A
  apply Real.iSup_nonneg; intro _hA
  apply Real.iSup_nonneg; intro _B
  apply Real.iSup_nonneg; intro _hB
  exact abs_nonneg _

theorem alphaMixingCoeff_le_one {μ : Measure Ω} [IsProbabilityMeasure μ]
    (σPair : Fin 2 → MeasurableSpace Ω) :
    CentralLimitTheoremOQ02.alphaMixingCoeff μ (σPair 0) (σPair 1) ≤ 1 := by
  unfold CentralLimitTheoremOQ02.alphaMixingCoeff
  apply Real.iSup_le _ (by norm_num); intro A
  apply Real.iSup_le _ (by norm_num); intro _hA
  apply Real.iSup_le _ (by norm_num); intro B
  apply Real.iSup_le _ (by norm_num); intro _hB
  exact indicator_cov_le_one A B
```

### Key technical tricks

The parent file `CentralLimitTheoremOQ02.lean` line 444 deferred
`alphaMixingCoeff_nonneg` "due to nested ciSup elaboration complexity
(MeasurableSpace instances conflict in nested suprema)" — two intertwined
obstacles.

**Obstacle 1: typeclass-synthesis conflict.** Direct `(ℱ 𝒢 : MeasurableSpace
Ω)` explicit arguments compete with the ambient `[MeasurableSpace Ω]`
instance for synthesis inside the nested `⨆`. **Resolution.** Bundle the
σ-algebra pair as `σPair : Fin 2 → MeasurableSpace Ω`; the projections
`σPair 0` and `σPair 1` are function applications, not instance candidates.
This is the file convention already used by `davydov_covariance_inequality`
(S4) and the parent file's `independent_implies_zero_mixing`.

**Obstacle 2: nested `BddAbove` discharge.** A naive `le_ciSup_of_le`
approach would require a `BddAbove` witness at each of the 4 nested `⨆`
layers, mixing `Type` (`Set Ω`) and `Prop` (`MeasurableSet …`) indices.
**Resolution.** `Real.iSup_nonneg` and `Real.iSup_le` from
`Mathlib.Data.Real.Archimedean` are stated reflectively in `ι : Sort*` —
they apply uniformly to **any** index sort, including the propositional
`MeasurableSet …` layers. The unbounded/empty-range edge cases collapse to
`sSup ∅ = 0 ∈ ℝ` automatically (Mathlib's convention for ℝ as a
`ConditionallyCompleteLinearOrder`). No per-level `BddAbove` machinery is
needed — the proof is 5 lines each, fully discharged via `apply ... ;
intro`.

### Strategic positioning

* **Non-overlapping with PR #18202** (researcher-5 — S5a `polynomial_summable_of_exponent_gt_one`
  drift fix). #18202 touches Part II only; this PR adds to Part III only. Both
  can merge independently.
* **Closes named ingredients (1) and (2)** of the Davydov decomposition. The
  remaining order-theory sorry is `davydov_indicator_bound` (ingredient (3)),
  which now has `alphaMixingCoeff_le_one` available as the `BddAbove` witness
  for the inverse direction (`le_ciSup_of_le`). Becomes tractable in the next
  iteration.
* **Resolves the parent file's deferred TODO** noted at
  `CentralLimitTheoremOQ02.lean` line 444. The reflective `Real.iSup_nonneg`
  approach is upstream-portable.

### Counts

* `lineCount`: 544 → **601** (+57 net: ~30 lines of two new proven theorems
  with full docstrings explaining the dual typeclass / BddAbove obstacles;
  Part III header docstring rewritten ~+10 lines to reflect the new
  structure; `davydov_covariance_inequality` docstring re-marked +12 lines
  to flag the now-proven ingredients (1) and (2)).
* `theoremCount`: 9 → **11** (+2 fully proven).
* `definitionCount`: 4 (unchanged).
* `sorries`: **3** (unchanged — this PR does not touch any existing sorry;
  PR #18202 in flight closes `polynomial_summable_of_exponent_gt_one` to
  bring this to 2 once it merges).
* `axiomCount`: 0 (unchanged).

### Build status

**[BUILD VERIFIED]** — Docker build of `Proofs.CentralLimitTheoremOQ02OQ04`
on Mathlib v4.26.0 completes successfully on the worktree. The two new
proofs use only:

* `Real.iSup_nonneg` (`Mathlib.Data.Real.Archimedean` line 301)
* `Real.iSup_le` (`Mathlib.Data.Real.Archimedean` line 236)
* `abs_nonneg`, `norm_num`, `indicator_cov_le_one` (already in scope).

No new imports required.

### Next iteration (S5b / S6)

Three productive paths now open:

1. **`davydov_indicator_bound`** (the third order-theory ingredient): use
   `le_ciSup_of_le` repeatedly with `alphaMixingCoeff_le_one`'s implicit
   `BddAbove` discharge. ~30 lines. Closes the indicator base case.
2. **L^p density step** (S5b ACT, ~100 lines): truncate + Hölder
   amplification.
3. **Joint tuple stationarity** (S6 prerequisite for Bernstein blocks),
   ~100 lines.

---

## S4 partial (researcher-6, 2026-05-12, this PR)

**Indicator-pair covariance identity** — one new fully-proven private theorem,
positioned in Part III immediately before `davydov_covariance_inequality`:

```lean
theorem indicator_pair_covariance_eq
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫ ω, A.indicator (1 : Ω → ℝ) ω * B.indicator (1 : Ω → ℝ) ω ∂μ
      - (∫ ω, A.indicator (1 : Ω → ℝ) ω ∂μ)
        * (∫ ω, B.indicator (1 : Ω → ℝ) ω ∂μ)
    = μ.real (A ∩ B) - μ.real A * μ.real B
```

This is the **algebraic identity** that the indicator base case of Davydov's
covariance inequality reduces to. The RHS `μ(A ∩ B) − μ(A) · μ(B)` is precisely
the expression appearing inside the supremum that defines `alphaMixingCoeff`
in the parent file `CentralLimitTheoremOQ02.lean` (line 416–424). Combined
with a `le_ciSup`-flavored bound (the next sub-step in the S4 path; deferred
since the parent file flagged the nested-`ciSup` elaboration complexity in
`alphaMixingCoeff_nonneg`), this yields the constant-1 Davydov bound on
indicator pairs `|Cov(1_A, 1_B)| ≤ α(ℱ, 𝒢)`. The truncation + Hölder
amplification step then promotes this base case to the sharp-constant
general L^p inequality with constant 12 (the full S4 deliverable).

**No supremum machinery is invoked at this layer.** The proof uses only:

* `Set.indicator_apply` and `Set.mem_inter_iff` for pointwise identification
  `1_A · 1_B = 1_{A ∩ B}`.
* `MeasureTheory.integral_indicator_one` to evaluate each indicator integral
  as `μ.real`.

### Why this is a productive narrow step

The full S4 Davydov proof is ~150 lines and decomposes as:

1. **Indicator-pair algebraic identity** — *this PR*. ~20 lines of measure-theoretic
   bookkeeping, fully proven, no Mathlib gaps.
2. **Indicator-pair α-mixing bound** — `|Cov(1_A, 1_B)| ≤ α(ℱ, 𝒢)` via
   `le_ciSup` on the nested-`ciSup` definition of `alphaMixingCoeff`. ~30 lines,
   deferred pending the parent's nested-`ciSup` complexity workaround.
3. **Simple-function extension** — linear combination of indicators by linearity
   of integrals. ~30 lines.
4. **Truncation step** — for L^p X, Y, bound the truncation tail via Markov's
   inequality + Hölder. ~50 lines.
5. **Hölder amplification** — Hölder on the bounded part yields the
   `(p-2)/p` exponent. ~30 lines.

This PR closes step 1 without touching the open S3 PRs (#17810, #17826), which
target the already-merged stationarity / Davydov-reduction work. The open PRs
are conflict-frozen against the post-S3 main; this S4 PR sits cleanly downstream
without overlap.

### Counts

* `lineCount`: 402 → 443 (+41, including ~25 lines of docstring + 16 lines
  of proof body + import line)
* `theoremCount`: 7 → 8 (+1 fully-proven theorem)
* `definitionCount`: 4 (unchanged)
* `sorries`: 2 (unchanged — `davydov_covariance_inequality` and
  `mixing_clt_ibragimov` remain the deferred targets; this PR adds a proven
  helper but does not close either sorry)
* `axiomCount`: 0 (unchanged)

### Strategic positioning

**Non-overlap with open PRs**:
* #17810 (researcher-1, conflicting): 5 stationarity/moment-bound bridge
  lemmas (Stationary.integrable_of_zero, etc.) — predates the merged S3 ACT
  (#17820) and its content is now superseded by `stationary_eLpNorm_eq`
  proven in S3. Conflict-frozen.
* #17826 (researcher-1, mergeable): duplicate of merged S3 ACT (#17820);
  same Davydov reduction + bridge lemmas. Content already in main.

This PR is **strictly downstream** of S3: it adds a new helper proven against
the post-S3 file, building on the now-merged `IbragimovHypotheses` /
`davydov_covariance_inequality` API surface. No overlap with the two open S3
PRs at the file-level (this PR adds a new theorem, doesn't touch existing
ones). No overlap at the API level (this helper is positioned to be consumed
by future S4 sub-steps, not by the S3 deliverables).

### Build status

**[BUILD UNVERIFIED]** — Same caveat as S2/S3/S22: worktree's
`proofs/.lake` is a recursive self-symlink, so local Docker builds
re-fresh-clone Mathlib (~30–45 min cold). The new helper uses only Mathlib
API verified against `/Users/rwalters/GitHub/mathlib4`:

* `MeasureTheory.integral_indicator_one`
  (`Mathlib.MeasureTheory.Integral.Bochner.Set` line 519):
  `∫ x, s.indicator 1 x ∂μ = μ.real s` for measurable `s`. Added as an
  explicit import to ensure transitive availability.
* `Set.indicator_apply`, `Pi.one_apply`, `Set.mem_inter_iff` — core Set/Pi
  API, transitively available via `MeasureTheory.Function.LpSpace.Basic`.
* `IsProbabilityMeasure` and `Measure.real` — transitively available.

No new axioms.

### Next iteration (S4 cont'd)

After this PR lands, the remaining steps for closing
`davydov_covariance_inequality`:

1. **Indicator-pair α-mixing bound** (next ~30 lines): apply `le_ciSup` to
   the nested `ciSup` definition of `alphaMixingCoeff` to derive
   `|μ(A ∩ B) − μ(A)·μ(B)| ≤ alphaMixingCoeff μ ℱ 𝒢` for any measurable
   `A ∈ ℱ`, `B ∈ 𝒢`. The proof composes with this PR's
   `indicator_pair_covariance_eq` to give the constant-1 indicator-pair
   Davydov bound on covariance. The parent's `alphaMixingCoeff_nonneg`
   nested-`ciSup` complexity note (line 444) applies; the workaround is
   to apply `le_ciSup` iteratively at each ⨆ layer.
2. **Simple-function extension** (~30 lines).
3. **Truncation + Hölder amplification** (~80 lines).

Total ~140 lines once the nested-`ciSup` bound is settled.

---

## S3 (researcher-1, 2026-05-12, merged via #17820)

S4 ACT — **Build-fix** for S3 PR #17820 (which was merged
"(build pending)" and never actually compiled on `origin/main`), plus
proven `indicator_cov_le_one` ([0, 1] envelope helper) and documented
structural decomposition of `davydov_covariance_inequality`.

Three build blockers fixed:
1. **Stale import** `Mathlib.Probability.Variance` (file removed in Mathlib
   drift) — removed (unused in code).
2. **MS Ω typeclass-synthesis collision** — when `(ℱ 𝒢 : MeasurableSpace Ω)`
   are direct explicit args of a theorem, Lean 4's typeclass synthesis
   picks them as the `[MeasurableSpace Ω]` instance of
   `alphaMixingCoeff`, instead of the ambient `inst✝¹`. Fix: use the parent
   file's pattern `(σPair : Fin 2 → MeasurableSpace Ω)` (function-form),
   then `σPair 0` and `σPair 1` are projections — not instance candidates.
   This is the same trick the parent file uses at
   `independent_implies_zero_mixing` and `AlphaMixingSequence.mixing_bound`.
3. **Invalid Lean identifier `σ²`** in `mixing_clt_ibragimov` (superscript
   `²` not in Lean's identifier alphabet) — renamed to `σsq`.

Deliverables (this session):
- **Build-fix**: 3 blockers above; file now builds cleanly.
- **`indicator_cov_le_one` (PROVEN)**: `[0, 1]` envelope for the
  indicator-covariance term, the `BddAbove` witness for the nested suprema
  inside `alphaMixingCoeff`.
- **Documented structural decomposition** in `davydov_covariance_inequality`'s
  docstring: the L^p Davydov inequality decomposes into 3 named
  order-theory ingredients (`alphaMixingCoeff_le_one`,
  `alphaMixingCoeff_nonneg`, `davydov_indicator_bound`) + 1 L^p density
  step. Each ingredient has a clear strategy.

Sorries: 2 (unchanged from S3 raw count; the file now actually compiles).

## Active Approach

**Sharp-threshold polynomial-mixing CLT** under (2+δ)-th moments. Bernstein
blocks proof template:

1. **Davydov's covariance inequality (S4–S5)** ⇒ covariances are summable.
   - S3 status: stated, never built.
   - S4 status: builds cleanly; decomposed into 3 order-theory sorries
     (yet to formalize) + 1 L^p density step. `indicator_cov_le_one`
     proven as the `[0, 1]` envelope.
   - S5a target: formalize the 3 order-theory ingredients.
   - S5b target: L^p density / truncation step.
2. **Long-run variance σ² = Var(X₁) + 2∑_{k≥1} Cov(X₁, X_{k+1}) absolute
   convergence** — S3 proven modulo Davydov (call site refactored in S4 to
   use the `σPair : Fin 2 → MS Ω` wrap).
3. Joint tuple stationarity strengthening (S6).
4. Bernstein blocks p_n, q_n (S7).
5. Lindeberg condition on large blocks (S8).
6. Invoke parent's Lindeberg-Feller CLT (S9).

## Blockers

- **L^p density step** (S5c target): ~100 lines of measure-theoretic
  reduction (level-set decomposition + Hölder + Markov tail). All three
  order-theory ingredients are now proven (S5+S5b), so this is the sole
  remaining step inside `davydov_covariance_inequality`.

## Next Action

**Session S5c+ candidates** (in priority order):

1. **S5c ACT** (~100 lines): L^p density step using level-set
   decomposition + Hölder, reducing to `davydov_indicator_bound` (now
   available, S5b). Concretely: bound `|Cov(X, Y)|` by expressing
   `X = ∫_ℝ (𝟙_{X>t} − 𝟙_{X<-t}) dt` plus a Markov tail, expanding
   bilinearly into a double integral of indicator-pair covariances, and
   applying `davydov_indicator_bound` pointwise; Hölder on the truncated
   piece + Markov on the tail recovers the `α^{(p-2)/p} · ‖X‖_p · ‖Y‖_p`
   bound.
2. **Parallel path**: Refine `Stationary` to joint tuple stationarity
   (S6 prerequisite for Bernstein blocks). ~100 lines.

## Decomposition Plan

| Session | Phase | Deliverable | Lines | Status |
|---|---|---|---|---|
| S1 | OBSERVE | Scaffold (md + json) | 0 Lean | merged #17778 |
| S2 | ORIENT | 4 def stubs + 2 thm stmts + 2 proven helpers | 231 | merged #17792 |
| S3 | ACT | Davydov stmt + 3 new helpers + longrun_variance proof (never built) | 402 | merged #17820 (build broken) |
| S4 | ACT | Build-fix + indicator_cov_le_one + structural decomposition | 502 | merged #18173/etc |
| S5 | ACT | alphaMixingCoeff_nonneg + alphaMixingCoeff_le_one (ingredients 1, 2) | 544 → 601 | merged #18227 |
| S5a | mechanic | polynomial_summable_of_exponent_gt_one drift fix | 601 → 610 | merged #18202 |
| S5b | ACT | davydov_indicator_bound (ingredient 3) | 610 → 684 | **this session** |
| S5c | ACT | L^p density / truncation → full Davydov | ~100 | next |
| S6 | ACT | Refine Stationary to tuple-joint stationarity | ~100 | |
| S7 | ACT | Bernstein blocks p_n, q_n + arithmetic | ~150 | |
| S8 | ACT | Large-block independence approximation | ~120 | |
| S9 | ACT | Lindeberg condition on blocks | ~100 | |
| S10 | ACT | Invoke parent Lindeberg-Feller CLT | ~50 | |

## Attempt Counts

- Total attempts: 6
- Current approach attempts: 1 (S5b — peel 4-fold ⨆ via le_ciSup_of_le
  + ciSup_pos)
- Approaches tried:
  - S1: OBSERVE scaffolding.
  - S2: ORIENT — predicates + structure + main theorem statements + 2
    helpers.
  - S3: ACT — Davydov-modulo proof of long-run variance absolute
    convergence + extension of IbragimovHypotheses + 3 new proven theorems
    (PR #17820 merged "(build pending)" without actually building).
  - S4: ACT — discovered S3 was broken, fixed 3 build-blockers, added
    proven `indicator_cov_le_one` helper, documented the structural
    decomposition into 3 named order-theory ingredients + L^p density.
  - S5: ACT — proved ingredients (1) `alphaMixingCoeff_le_one` and (2)
    `alphaMixingCoeff_nonneg` via reflective use of `Real.iSup_le` and
    `Real.iSup_nonneg` (build-verified, PR #18227).
  - S5a: mechanic — closed `polynomial_summable_of_exponent_gt_one`
    Mathlib-drift sorry via `Real.summable_nat_rpow` (PR #18202).
  - S5b: ACT — proved ingredient (3) `davydov_indicator_bound` by peeling
    4-fold ⨆ via `le_ciSup_of_le` (Set Ω layers, BddAbove from
    `indicator_cov_le_one`) and `ciSup_pos` (Prop layers).

## Key Files

- `proofs/Proofs/CentralLimitTheoremOQ02OQ04.lean` — **S5b: 684 lines,
  build-pending (worktree .lake symlink loop)**. 12 theorems + 2 sorries,
  4 definitions, 1 structure with 14 fields. S5b additions: one new proven
  theorem `davydov_indicator_bound` (~36 LOC + ~30 LOC docstring) +
  docstring updates to Part IV `davydov_covariance_inequality` (mark
  ingredient (3) proven; relabel L^p density as S5c). The remaining 2
  sorries are `davydov_covariance_inequality` (L^p version, S5c target,
  now reduced to step (d) alone) and `mixing_clt_ibragimov` (S6+ target).
- `src/data/proofs/central-limit-theorem-oq-02-oq-04/meta.json` —
  updated with sorries 2, lineCount 684, theoremCount 12.
- `proofs/Proofs/CentralLimitTheoremOQ02.lean` — parent file, unchanged.
  The 3 named order-theory ingredients (now all proven) in S4's Davydov
  docstring are good candidates for upstream contribution.
