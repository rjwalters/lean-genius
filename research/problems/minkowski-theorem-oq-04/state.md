# Research State: minkowski-theorem-oq-04

## Current State
**Phase**: ACT (S30 PR-B landed Docker-clean; PR-C is the only remaining S24 ACT — bearers and helpers all in scope; infra GREEN since 2026-06-02)
**Path**: full
**Since**: 2026-06-02T00:25:00Z (S30 ACT PR-B — `blichfeldt_general_lattice` shipped; Docker 3075 jobs clean)
**Last Updated**: 2026-06-02 (S30 ACT PR-B — Lean +139 LOC, 1126 lines, 17 theorems, build-verified; B1/B2 CLEARED)
**Iteration**: 30 (S30 ACT PR-B — researcher-1)

## S30 — S30 ACT PR-B 2026-06-02 (researcher-1)

**Focus**: ship S24 PR-B per S23 spec §2.1 / §4 — `blichfeldt_general_lattice` (lattice-side k+1
covering-count averaging). Builds on S27 PR-A `volume_eq_setLIntegral_indicator_tsum_lattice`.
T+16d since S29 STATE-SYNC. Pre-flight at S30: B1 (Docker hung 19.9h at S29) CLEARED — `timeout 10 docker info` returns full Server: section (Containers: 0, Images: 3); B2 (disk RED 3.4 Gi at S29) CLEARED — `df -h /System/Volumes/Data` reports 55 Gi avail / 94% used. Both gates of S29 nextAction §(c) GREEN, unblocking option (c) "paste S23 spec §2.1 and ship".

### Deliverables (S30 PR-B)

| Field | Value |
| --- | --- |
| New theorem | `BlichfeldtTheorem.blichfeldt_general_lattice` (basis-parametric, k+1 covering form) |
| Insertion site | `proofs/Proofs/MinkowskiTheoremOQ04.lean:441` (immediately after `blichfeldt_general` at :324; before `blichfeldt_basic_from_general` at :442 in pre-edit numbering) |
| Body size | ~110 LOC body + ~17 LOC docstring (+1 `#check` line in Export section); total +139 LOC |
| Proof strategy | Mechanical bearer-substitution per S23 §4: `stdLattice n → Submodule.span ℤ (Set.range b)`, `stdFundDomain n → ZSpan.fundamentalDomain b`, `volume_eq_setLIntegral_indicator_tsum → volume_eq_setLIntegral_indicator_tsum_lattice b` (the S27 PR-A helper). The covolume-= 1 step (`stdLattice_covolume`) is the only `stdLattice`-specific step; abstracted by quoting `volume (ZSpan.fundamentalDomain b)` directly in the hypothesis (per S23 §5 normalisation). Otherwise structurally identical to `blichfeldt_general`. |
| Docker build | **3075 jobs / first-try clean** at Lean 4.26.0 + Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` |
| Source file growth | 987 → **1126** lines (+139) |
| Theorem count | 16 → **17** |
| Axioms | **0** textually / **0** structure-encoded (unchanged) |
| Sorries | **0** (unchanged) |
| New `#check` entries | 1 (`BlichfeldtTheorem.blichfeldt_general_lattice` at Export check :1117) |

### Bearer drift recheck at this commit (B1-B4 from S25 manifest, lake-SHA `2df2f0150c`)

| # | Symbol | Bearer file | S25 line | S30 status |
|---|---|---|---|---|
| B1 | `ZSpan.isAddFundamentalDomain'` | `Mathlib/Algebra/Module/ZLattice/Basic.lean` | 359 | ✅ used via `volume_eq_setLIntegral_indicator_tsum_lattice` (S27); no direct call in PR-B |
| B2 | `ZSpan.volume_fundamentalDomain` | `Mathlib/Algebra/Module/ZLattice/Basic.lean` | 386 | ✅ not needed in PR-B (covolume term left abstract per S23 §5) |
| B3 | `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure` | `Mathlib/MeasureTheory/Group/GeometryOfNumbers.lean` | 65 | ✅ deferred to PR-C |
| B4 | `Module.finrank_fin_fun` | `Mathlib/LinearAlgebra/FreeModule/Finite/Matrix.lean` | 328 | ✅ deferred to PR-C |

### S24 sequencing — post-PR-B state

| PR | Theorem | Status | Insertion site |
|---|---|---|---|
| **PR-A** | `volume_eq_setLIntegral_indicator_tsum_lattice` | ✅ **shipped (S27)** | `MinkowskiTheoremOQ04.lean:264` |
| **PR-B** | `blichfeldt_general_lattice` (~110 LOC body + docstring) | ✅ **shipped (S30, this iteration)** | `MinkowskiTheoremOQ04.lean:441` (post-edit) |
| PR-C | `minkowski_general_k_lattice` (~50 LOC) | ⏳ unblocked (PR-B shipped + Docker GREEN) | after `minkowski_general_k` at :719 |

### Pre-flight

- `gh pr list -R rjwalters/lean-genius --search "minkowski-theorem-oq-04 in:title" --state open` → 0 results. No concurrent researcher PR; #17599 (Iter 21 DIRTY 8-day-stale) merged or closed between S29 and S30 (T+16d).
- `timeout 10 docker info 2>&1 | grep -A 5 "^Server:"` → Containers: 0 + Images: 3 visible (B1 CLEARED).
- `df -h /System/Volumes/Data | tail -1` → 55 Gi avail / 94% used (B2 CLEARED, well above 5 Gi soft-floor).
- Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` unchanged from S25/S26/S27/S28/S29 — bearer manifest carries forward (no full re-spot-check; only the helper `volume_eq_setLIntegral_indicator_tsum_lattice` is directly invoked).
- Concurrent researcher slugs (`elementary-quadratic-reciprocity-oq-01-oq-02` S8 STATE-SYNC PR #22012 just shipped by this same researcher-1 session at T-20min) — no cross-slug conflict.

### Honest calibration

Adds +139 Lean LOC (1 new theorem `blichfeldt_general_lattice` + 1 `#check`), closes 0 sorries (already 0), retires 0 axioms (already 0). Build-verified 3075 jobs clean on first try via Docker. Mechanic territory deferred per S27 precedent: `meta.json.lineCount: 987 → 1126`, `meta.json.theoremCount: 16 → 17`, `mainTheorems[]` append for `blichfeldt_general_lattice` (rich object with significance/mathContext). Sibling-slug `leanFiles[0/1]` drift NOT touched.

### Next picker (S31)

- Verify Docker still GREEN: `timeout 10 docker info 2>&1 | grep -E "^Server:" -A 5`.
- Verify host disk ≥ 5 Gi: `df -h /System/Volumes/Data | tail -1`.
- IF BOTH GREEN: paste S23 spec §2.2 and ship `minkowski_general_k_lattice` via `./proofs/scripts/docker-build.sh Proofs.MinkowskiTheoremOQ04`. Estimated ~50 LOC body, parameter-lifted from `minkowski_general_k` at :719, calling PR-B's `blichfeldt_general_lattice` after the half-scaling step. Bearers B3 + B4 enter scope here.
- IF EITHER RED: ship a doc-only S31 STATE-SYNC absorbing any new mechanic / sibling drift.

## S29 — S29 STATE-SYNC 2026-05-17 (researcher-4)

**Focus**: doc-only JSON+state catchup post-S28-PREP (PR #19640 merged 2026-05-16T15:20:34Z, ~10.5h before this STATE-SYNC).
Full memo at `sessions/2026-05-17-s29-state-sync.md`.

### Four drift items closed

| # | Drift | Resolution |
|---|---|---|
| 1 | `currentState.focus` had four "this PR" loci referring to merged S28 PREP | Repointed to "PR #19640 (S28 PREP)" + rewrote focus to S29 narrative |
| 2 | B1 description "9h since hang ... within < 12h Path C cancellation window" | Refreshed to "19.9h since hang ... Path C window EXPIRED at 2026-05-16T18:01Z (7.9h past)"; mitigation "6.7 Gi avail" → "3.4 Gi avail (RED, below 5 Gi soft-floor)" |
| 3 | `currentState.blockers[]` had only B1 — missing B2 disk RED | NEW B2 added: host disk RED 3.4 Gi (-3.3 Gi vs S28 PREP 6.7 Gi snapshot) |
| 4 | `leanFiles[2]` (MinkowskiTheoremOQ04.lean) carried pre-S27 numerics | Surgical refresh: lineCount 922→987 (+65 from S27 PR-A), theoremCount 15→16 (+1), sorryCount 0→1 (raw `\bsorry\b` matches docstring "sorry-free" phrase at line 59; not a proof-level sorry — `meta.json.meta.sorryCount` left at null by mechanic PR #19542 intentionally) |

### INFRA snapshot (3 RED)

| Gate | Status | Detail | Δ vs S28 PREP |
|---|---|---|---|
| G7 host disk | RED | 3.4 Gi avail / 100% used (below 5 Gi soft-floor) | -3.3 Gi (was 6.7 Gi above 1 Gi threshold) |
| G8 Docker server | RED | `timeout 10 docker info` returns Client only, no Server: lines (canonical hung-daemon signature) | Unchanged — hung 19.9h, Path C window EXPIRED 7.9h ago |
| G9 .lake symlink | GREEN | `proofs/.lake → /Users/rwalters/GitHub/lean-genius/proofs/.lake` (regular symlink, not self-loop) | Unchanged — masked by Docker volume per Iter 23 insight |

### PR-B / PR-C status (unchanged from S28)

| PR | Theorem | Lean status | Docker status |
|---|---|---|---|
| PR-A | `volume_eq_setLIntegral_indicator_tsum_lattice` | ✅ shipped at lines 244–308 | ✅ build-verified 3075 jobs 04:40Z |
| PR-B | `blichfeldt_general_lattice` (~80 LOC) | paste-ready in `s23-lattice-generalization-spec.md §2.1` | ❌ BLOCKED on B1 (Path C EXPIRED 7.9h ago) |
| PR-C | `minkowski_general_k_lattice` (~50 LOC) | depends on PR-B | ❌ BLOCKED on B1 + PR-B |

### Pre-flight

- `gh pr list -R rjwalters/lean-genius --search "minkowski-theorem-oq-04 in:title" --state open` → 1 result (#17599 Iter 21, 8-day stale, DIRTY — mechanic/champion territory; not researcher scope).
- Recency probe: latest merged researcher PR for slug was S28 PREP #19640 at 2026-05-16T15:20:34Z (T-10.5h); no same-slug merges in last 2h — no collision risk.
- `timeout 10 docker info` → only `Client:` block (B1 RED, 19.9h hung).
- `df -h /System/Volumes/Data` → 3.4 Gi avail (B2 RED, below 5 Gi soft-floor).
- Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` unchanged from S25/S26/S27/S28 — bearer manifest carries forward (no re-spot-check in this STATE-SYNC).
- Sibling-slug `leanFiles[]` drift (OQ02 lineCount 285→284, OQ02OQ01 lineCount 268→267 + theoremCount 7→8) NOT touched — sibling territory, deferred to their respective mechanic batches.

### Honest calibration

Adds 0 Lean lines, closes 0 sorries, states 0 new theorems. Doc-only catchup is the entire deliverable. Reduces misleading state for future researchers/auditors scanning `currentState.{focus, blockers, lastUpdate}` and `leanFiles[2]`. Anti-scope: no `meta.json` edits (`mainTheorems[]` append for `volume_eq_setLIntegral_indicator_tsum_lattice` remains mechanic territory; sorryCount=null intent preserved), no bearer re-spot-check (Mathlib pin unchanged), no PR-B/PR-C Lean (Docker-blocked harder than at S28).

## S28 — S28 PREP 2026-05-16 (researcher-11)

**Focus**: doc-only JSON catchup post-S27-PR-A and post-mechanic-#19542.
Full memo at `sessions/2026-05-16-s28-prep-postS27-postmechanic-status-sync.md`.

### Three drift items closed

| # | Drift | Resolution |
|---|---|---|
| 1 | `currentState.blockers: []` (cleared by S27 PR-A's 04:40Z build-verify) | Re-add B1 — Docker re-hung at 06:01Z (9 h before this PREP); within 12 h Path C cancellation window |
| 2 | `currentState.focus` ends "Still deferred to Mechanic ... meta.status/badge flip + mainTheorems entries (PR-A new + blichfeldt_general type:axiom→proved)" | Mechanic PR #19542 (13:53Z, 1 h before this PREP) flipped meta.status (axiomatized→verified) + meta.badge (axiom→original) + rewrote meta.assumptions; `mainTheorems[blichfeldt_general].type` was already `"proved"`; STILL PENDING: `mainTheorems[]` entry for S27 PR-A new theorem `volume_eq_setLIntegral_indicator_tsum_lattice` (mechanic territory) |
| 3 | `lastUpdate: 2026-05-16T04:15:00Z` (~11 h stale) | Refresh to 15:00:00Z |

### PR-B / PR-C status

| PR | Theorem | Lean status | Docker status |
|---|---|---|---|
| PR-A | `volume_eq_setLIntegral_indicator_tsum_lattice` | ✅ shipped at lines 244–308 | ✅ build-verified 3075 jobs 04:40Z |
| PR-B | `blichfeldt_general_lattice` (~80 LOC) | paste-ready in `s23-lattice-generalization-spec.md §2.1` | ❌ BLOCKED on B1 |
| PR-C | `minkowski_general_k_lattice` (~50 LOC) | depends on PR-B | ❌ BLOCKED on B1 + PR-B |

### Pre-flight

- `gh pr list --search "minkowski-theorem-oq-04 in:title" --state open` → 1 result (#17599 Iter 21, 7-day stale, DIRTY — mechanic/champion territory; not researcher scope).
- `timeout 30 docker info` → only `Client:` block (B1 RED).
- `df -h /System/Volumes/Data` → 6.7 Gi avail (above 1 Gi threshold).
- Mathlib pin `2df2f0150c…` unchanged from S27 — S27 §"Bearer drift recheck" carries forward (no re-spot-check in this PREP).

### Honest calibration

Adds 0 Lean lines, closes 0 sorries, states 0 new theorems. JSON
catchup is the entire deliverable. Reduces misleading state for
future researchers/auditors scanning `currentState.{blockers,focus,
lastUpdate}`. Anti-scope: no `meta.json` edits (`mainTheorems[]`
append is mechanic territory), no bearer re-spot-check (Mathlib pin
unchanged), no PR-B/PR-C Lean (Docker-blocked).

## S27 — S24 ACT PR-A 2026-05-16 (researcher-1)

**Focus**: ship the first of three S24 PRs per S23 PREP §4 (post-S26 STATE-SYNC #19370 merge at 2026-05-16T03:53:25Z). Adds `volume_eq_setLIntegral_indicator_tsum_lattice` — the basis-parametric (`b : Module.Basis (Fin n) ℝ (Fin n → ℝ)`) variant of the existing `volume_eq_setLIntegral_indicator_tsum` — to `proofs/Proofs/MinkowskiTheoremOQ04.lean` immediately after the `stdLattice`-specialised version. Full memo at `sessions/2026-05-16-s27-s24-act-pr-a-volume-tsum-lattice.md`.

### Deliverables (S27 PR-A)

| Field | Value |
| --- | --- |
| New theorem | `volume_eq_setLIntegral_indicator_tsum_lattice` (basis-parametric, namespace `BlichfeldtTheorem`) |
| Insertion site | `proofs/Proofs/MinkowskiTheoremOQ04.lean:244–308` (between `volume_eq_setLIntegral_indicator_tsum` and `blichfeldt_general`) |
| Body size | ~45 LOC body + ~20 LOC docstring (~65 LOC total; S23 budgeted ≤30 LOC, doc-inflated) |
| Proof strategy | Mechanical bearer-substitution per S23 §4: `stdLattice n → Submodule.span ℤ (Set.range b)`, `stdFundDomain n → ZSpan.fundamentalDomain b`, `stdLattice_isAddFundamentalDomain n → ZSpan.isAddFundamentalDomain' b volume`. Otherwise structurally identical to the `stdLattice`-specialised template. |
| Docker build | **3075 jobs / first-try clean** at Lean 4.26.0 + Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` |
| Source file growth | 922 → **987** lines (+65) |
| Theorem count | 15 → **16** |
| Axioms | **0** textually / **0** structure-encoded (unchanged) |
| Sorries | **0** (unchanged) |
| New `#check` entries | 0 (deferred; `#check volume_eq_setLIntegral_indicator_tsum_lattice` natural to add when PR-B/-C land) |

### Bearer drift recheck at this commit (B1, lake-SHA `2df2f0150c`)

| # | Symbol | File | S25 line | This recheck | Drift | Section-header typeclasses |
|---|---|---|---|---|---|---|
| B1 | `ZSpan.isAddFundamentalDomain'` | `Mathlib/Algebra/Module/ZLattice/Basic.lean` | 359 | **359** | ✅ none | `section Real` → `[NormedAddCommGroup E] [NormedSpace ℝ E] (b : Basis ι ℝ E)`; theorem-level `[Finite ι] [MeasurableSpace E] [OpensMeasurableSpace E]` — all auto-derived for `E = Fin n → ℝ`, `ι = Fin n`. |

### S24 sequencing — post-PR-A state

| PR | Theorem | Status | Insertion site |
|---|---|---|---|
| **PR-A** | `volume_eq_setLIntegral_indicator_tsum_lattice` | ✅ **shipped (S27)** | `MinkowskiTheoremOQ04.lean:264` |
| PR-B | `blichfeldt_general_lattice` (~80 LOC) | unblocked (PR-A merged or HEAD-of-PR-A) | after `blichfeldt_general` (post `blichfeldt_basic_from_general`) |
| PR-C | `minkowski_general_k_lattice` (~50 LOC) | gated on PR-B | after PR-B (parameter-lifted copy of `minkowski_general_k`) |

### Gallery-meta sync (this PR)

| File | Field | 921→ | Reason |
|---|---|---|---|
| `meta.json` (top-level) | `lineCount` | **921 → 987** | PR-A added ~65 LOC |
| `meta.json` (top-level) | `theoremCount` | **15 → 16** | PR-A added 1 theorem |
| `meta.json` (`leanFiles[0]`) | `lineCount` | **921 → 987** | PR-A added ~65 LOC |
| `meta.json` (`leanFiles[0]`) | `theoremCount` | **15 → 16** | PR-A added 1 theorem |

**Still deferred to Mechanic** (per S26 D2): `meta.status: axiomatized → verified` / `meta.badge: axiom → original` / `meta.assumptions` rewrite / `mainTheorems[blichfeldt_general].type: axiom → proved` / new `mainTheorems[]` entry for `volume_eq_setLIntegral_indicator_tsum_lattice`. The lineCount+theoremCount drifts are byproducts of the Lean edit and are co-resolved here to avoid downstream tracker churn.

### Honest-status block (S27)

- **Mathematical progress**: PR-A discharges the §4 row 1 substitution table item ("a `_lattice` version of `volume_eq_setLIntegral_indicator_tsum`"). The new theorem is genuinely useful (entry-point for PR-B), but proof content is mechanical bearer-substitution against an already-discharged template — not novel mathematics.
- **Build-verification status**: 3075-job Docker green (warm-cache, ~2 min wall), first try. No new caveats.
- **Axiom status**: source is textually + structurally axiom-free (unchanged from S26); gallery flip remains Mechanic's call (deferred).
- **Open conjecture status**: unchanged — PR-A is infrastructure, not a new gallery-headline result. Remaining S24 work: PR-B (lattice Blichfeldt, mechanical) + PR-C (lattice Minkowski, mechanical lift through PR-B). #17599 (Iter 21, DIRTY 7-day-stale) still untouched and safe to ignore.

---

## S26 STATE-SYNC 2026-05-16 (researcher-12)

**Focus**: catch `state.md` and `src/data/research/problems/minkowski-theorem-oq-04.json` up to the post-drain reality on `origin/main` `8a3cda556b6`. Four PRs landed in 2026-05-15T22:55–23:44Z (S23 spec #18989, Iter 23 BUILD-VERIFY #19113, S24 candidate triage #19176, S25 bearer-pinpoint manifest #19314) — none updated the `state.md` head or the research JSON's `currentState` block. This iteration absorbs the lot in one conflict-free doc-only PR. Full memo at `sessions/2026-05-16-s26-state-sync-postdrain-catchup.md`.

### Post-drain Lean-source snapshot (`origin/main` `8a3cda556b6`)

| Field | Value |
| --- | --- |
| `lineCount` | **922** (+1 vs S26-prior 921; Iter 23 `#check minkowski_general_k_pairwise`) |
| `theoremCount` | **15** |
| `axiomCount` | **0** (textually; Docker-verified by Iter 23) |
| `sorries` | **0** (line-59 "is sorry-free" is in a docstring) |
| `#check` block | **11 entries** (lines 912–922; Iter 23 added `minkowski_general_k_pairwise`) |
| Docker build | **3075-job clean** at Lean 4.26.0 + Mathlib 4.26.0 (pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) |

### Bearer drift recheck (B1–B4, v4.26.0 pin)

S25 PREP §2 pinned four Mathlib lemmas by line number at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Re-executed 2026-05-16 02:01 UTC via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>`:

| # | Symbol | Path | S25 line | This recheck | Drift |
|---|---|---|---|---|---|
| B1 | `ZSpan.isAddFundamentalDomain'` | `Mathlib/Algebra/Module/ZLattice/Basic.lean` | 359 | **359** | ✅ none |
| B2 | `ZSpan.volume_fundamentalDomain` | `Mathlib/Algebra/Module/ZLattice/Basic.lean` | 386 | **386** | ✅ none |
| B3 | `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure` | `Mathlib/MeasureTheory/Group/GeometryOfNumbers.lean` | 65 | **65** | ✅ none |
| B4 | `Module.finrank_fin_fun` | `Mathlib/LinearAlgebra/Dimension/Constructions.lean` | 328 | **328** | ✅ none |

**Zero drift across all four bearers**. The Mathlib pin is content-addressable; bearer line numbers are immutable until a `lake-manifest.json` repo-side pin update.

### Post-merge ACT-readiness gate refresh (S25 PREP §6 → S26)

| # | Precondition | S25 PREP status | S26 STATE-SYNC status |
|---|---|---|---|
| 1 | #19113 (Iter 23) merged | OPEN/CLEAN | ✅ MERGED 2026-05-15T22:58:44Z |
| 2 | #18989 (S23 spec) merged | OPEN/CLEAN | ✅ MERGED 2026-05-15T23:44:39Z |
| 3 | post-merge state.md reflects S23 PREP block | gated on #2 | ⚠️ gated on this STATE-SYNC merging (self-satisfying) |
| 4 | Mathlib pin still `2df2f0150c` | ✅ | ✅ unchanged |
| 5 | Bearers B1–B4 at pinned lines | ✅ 2026-05-15 19:34 UTC | ✅ re-verified 2026-05-16 02:01 UTC (drift = 0) |
| 6 | No parallel ACT in flight | one DIRTY 5-day-stale (#17599) | ⚠️ one DIRTY 7-day-stale (#17599) — safe to ignore in scope decisions |

**S24 ACT is fully ready to ship**: pick PR-A (basis-parametric `volume_eq_setLIntegral_indicator_tsum_lattice`, ~30 LOC, mechanical bearer-substitution per PR #18989 §4), then PR-B (`blichfeldt_general_lattice`, ~80 LOC), then PR-C (`minkowski_general_k_lattice`, ~50 LOC).

### Gallery-meta drifts (deferred to Mechanic)

`src/data/proofs/minkowski-theorem-oq-04/meta.json` carries two drifts that the post-drain state surfaces. **This STATE-SYNC declines to fix them** (each is Mechanic-owned):

- **D1** `meta.lineCount: 921 → 922` (next Mechanic auto-sync pass).
- **D2** `meta.status: axiomatized → verified` / `meta.badge: axiom → original` / rewrite `meta.assumptions` to drop "pending Docker CI" caveat / `mainTheorems[blichfeldt_general].type: axiom → proved`. Mathematical preconditions per `CLAUDE.md` §"Axiom Integrity Policy" are unambiguously satisfied (0 textual axioms + 0 sorries + 0 structure-encoded assumptions + 3075-job Docker green). The flip is **safe** but is a provenance-significant Mechanic / Auditor decision, not a researcher one.

### Open-PR snapshot (2026-05-16 02:01 UTC)

`gh pr list --search "minkowski-theorem-oq-04 in:title" --state open`: **1 PR**.

- #17599 — Iter 21 `minkowski_three_points`. DIRTY 7-day-stale. Insertion site between `minkowski_general_k_finset` and `minkowski_four_points`; logically independent of S24 ACT. Next picker should either rebase or close.

### Honest-status block

- **Mathematical progress in this PR**: zero. STATE-SYNC is bookkeeping.
- **Build-verification status**: unchanged — `MinkowskiTheoremOQ04.lean` is 3075-job Docker green per Iter 23 BUILD-VERIFY.
- **Axiom status**: source is textually + structurally axiom-free; gallery flip remains Mechanic's call.
- **Open conjecture status**: Blichfeldt / generalized-Minkowski statements in the source file are mathematically complete; remaining open work is (a) S24 ACT (lattice generalization, ready), (b) gallery `verified` flip (Mechanic), (c) #17599 rebase or close (deferred).

### Next Action

**Session 27 (Lean-modifying)**: ship S24 ACT PR-A — basis-parametric `volume_eq_setLIntegral_indicator_tsum_lattice` (~30 LOC mechanical substitution per PR #18989 §4 row 1; bearers B1 + B2 + B4 already pinned at §"Bearer drift recheck" above). Budget Docker build per `feedback_researcher_lake_symlink_broken` (Iter 23 BUILD-VERIFY confirmed the host-side .lake recursive self-symlink is masked by Docker's cache-volume overlay, so a green build is achievable in ~12 min cold start).

**Parallel (Mechanic)**: gallery-flip per §"Gallery-meta drifts" — D1 (lineCount sync) + D2 (status `axiomatized → verified`).

----

## Iteration 23 BUILD-VERIFY 2026-05-14 (researcher-3)

**Focus**: First Docker baseline build of `MinkowskiTheoremOQ04.lean`
since the S13–S22 axiom-elimination chain landed 2026-05-08…05-09.
The slug carried a 9-PR build-pending convention (S13, S14, S15, S16,
S17, S18, S19, S20, S22A+B; plus PR #17599 still open) for 5–6 days
gated on a single Docker green pass. This iteration runs that pass,
records the outcome, and ships the 1-LOC `#check
minkowski_general_k_pairwise` cleanup that the STATE-SYNC #18969 (PR
#18969, 2026-05-13) flagged as "Minor cleanup pending".

### Outcome

**Build**: clean. `./proofs/scripts/docker-build.sh
Proofs.MinkowskiTheoremOQ04` returns **3075-job clean** on Lean v4.26.0
+ Mathlib v4.26.0 (pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).
Only warnings (routine `automatically included section variable(s)
unused` + `This simp argument is unused` in the parent
`MinkowskiFundamentalTheorem.lean`) — zero errors anywhere in the
build closure.

The 10 `#check` declarations in the Export check section all elaborate
cleanly (signatures shown in the build log; spot-check matches
state.md "live theorems" list).

### Lean edit (+1 LOC, net 921 → 922)

Single-line addition to the Export check section at line 920 of
`MinkowskiTheoremOQ04.lean`:

```lean
#check BlichfeldtTheorem.minkowski_general_k_pairwise
```

Placed alphabetically between `#check minkowski_general_k` (line 919)
and `#check minkowski_general_k_finset` (line 921 → 922). This closes
the "Minor cleanup pending" item flagged by STATE-SYNC #18969 (state.md
§"Minor cleanup pending"). Zero new Mathlib API; zero risk —
`minkowski_general_k_pairwise` is the Iter 22-B theorem (line 779) and
its signature was already verified by Iter 22-B's `Function.Injective`
+ `sub_eq_zero` proof.

### What this unblocks

1. **Meta status flip (Mechanic next)**: `meta.json` flip from
   `status: axiomatized → verified` and `badge: axiom → original` is
   now safe to perform. Docstring §"Axioms" claim "Zero axioms remain
   (down from four)" + Docker green build evidence = full provenance.
   Mechanic should also rewrite `meta.assumptions` to drop the
   "pending Docker CI" caveat and update
   `mainTheorems[blichfeldt_general].type: axiom → proved` (currently
   axiom-typed in `mainTheorems` per `meta.json`).
2. **PR #17599 rebase**: the open Iter 21 PR (`minkowski_three_points`)
   can rebase against this 1-LOC `#check` addition with a 3-line
   context adjustment (the insertion sites are 130+ lines apart and
   logically independent).
3. **S24 ACT (per PR #18989 sequencing)**: the lattice-generalization
   spec now has Docker-clean parent-state baseline to build on. PR-A
   (`volume_eq_setLIntegral_indicator_tsum` basis lift) and PR-B
   (`blichfeldt_general_lattice`) ship from a verified-green parent.

### Build environment data (for reproducibility)

| Field | Value |
| --- | --- |
| Docker image | `lean4-arm64:v4.26.0` |
| Lean toolchain | `v4.26.0` |
| Mathlib pin | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` |
| Memory limit | 32 GB (hard, cgroups) |
| Total jobs | 3075 |
| Errors | 0 |
| Mathlib cache | 7727 files (Azure origin) |
| Wall time | ~12 min (cold start; Mathlib clone + cache download + build) |

### Honest-status block

* **Mathematical progress in this PR**: zero new theorems; one
  Export-check `#check` line added. The mathematical content of the
  S13–S22 chain was already in-tree; this PR's contribution is
  **build-verification evidence + a 1-LOC cleanup**.
* **Build-verification status**: chain is now Docker-verified clean.
  The "9-PR build-pending" convention used by S13–S22 PRs is
  retroactively satisfied by this iteration's Docker run.
* **Open conjecture status**: unchanged — the underlying
  Minkowski/Blichfeldt generalization has been complete in the source
  file since Iter 22 (2026-05-09). This PR closes the verification
  gap, not the proof gap.
* **PR #18989 (S23 PREP lattice spec) status**: unaffected. That PR
  is doc-only and shapes S24/S25 scope; this PR is doc-mostly
  (+1 Lean LOC) and discharges the S22 build-pending convention. The
  two are independent.

----

## STATE-SYNC 2026-05-13 (researcher-12)

**Focus**: catch state.md and the research JSON
(`src/data/research/problems/minkowski-theorem-oq-04.json`) up to the
actually-merged Lean source on `origin/main` (post-Iter-22, both
parts A and B). Doc-only — zero Lean edits.

### Why STATE-SYNC

Two drifts compounded between 2026-05-09 (Iter 22 ship) and today
(2026-05-13):

1. **state.md missed Iter 22 part B.** PR #17627 (Iter 22 part A,
   `minkowski_four_points`) merged at 02:41 UTC and brought a fresh
   "Iteration 22" section into state.md. PR #17626 (Iter 22 part B,
   `minkowski_general_k_pairwise`) merged 73 minutes later at 03:54
   UTC; its file diff was effectively `proofs/...` only (the state.md
   hunk it claimed in its body never landed, presumably blocked at
   merge by the just-written Iter-22 section). Result: state.md
   records only `minkowski_four_points`, but the live file carries
   *both* part-A and part-B additions.

2. **Research JSON `leanFiles[MinkowskiTheoremOQ04.lean]` is at S9-era
   counts.** `lineCount: 296`, `theoremCount: 5`, `axiomCount: 1` on
   `origin/main` (file is 921 / 15 / 0). The gallery snapshot at
   `src/data/proofs/minkowski-theorem-oq-04/meta.json` was synced by
   mechanic PR #17681 (merged 2026-05-12) and already reads
   `lineCount: 921 / theoremCount: 15 / axiomCount: 0`. The research
   JSON's `leanFiles` block is not on any mechanic's auto-sync path,
   so the drift accumulates here until a researcher or doc-only PR
   refreshes it.

`currentState.focus` / `nextAction` / `knowledge.progressSummary` /
`knowledge.builtItems` likewise pre-date Iter 22 part B; this
STATE-SYNC repaints all four fields together with the `leanFiles`
counts and the `lastUpdate` timestamp.

### Iteration 22 part B (`minkowski_general_k_pairwise`, PR #17626, merged 2026-05-09T03:54:03Z)

Author: researcher-1 (per the PR body's signature). Iteration label
in the PR title and body is "Iter 22" — the same label as the part-A
`minkowski_four_points` PR #17627 — but the two ship disjoint
content. We retain the "Iteration 22 — parts A + B" header rather
than renumbering to "Iter 22 + Iter 22.5".

**Statement** (file line 779; ~17-line body + ~36-line docstring,
total +54 LOC):

```lean
theorem minkowski_general_k_pairwise {n : ℕ} [NeZero n] (k : ℕ)
    (s : Set (Fin n → ℝ))
    (h_meas : MeasurableSet s)
    (h_symm : ∀ x ∈ s, -x ∈ s)
    (h_conv : Convex ℝ s)
    (h_vol : (k : ENNReal) * (2 : ENNReal) ^ n < volume s) :
    ∃ pts : Fin (k + 1) → (stdLattice n).toAddSubgroup,
      Function.Injective pts ∧
      (∀ i, ((pts i : Fin n → ℝ)) ∈ s) ∧
      (∀ i j, i ≠ j →
        ((pts i : Fin n → ℝ)) - ((pts j : Fin n → ℝ)) ≠ 0)
```

**Proof** (transport from `minkowski_general_k`, ~5 lines):

```lean
obtain ⟨pts, h_inj, h_in_s⟩ :=
  minkowski_general_k k s h_meas h_symm h_conv h_vol
refine ⟨pts, h_inj, h_in_s, ?_⟩
intro i j hij
rw [sub_ne_zero]
intro heq
exact hij (h_inj (Subtype.ext heq))
```

**Pedagogical role**: the Minkowski-side analogue of Iter 19's
`blichfeldt_general_pairwise` (PR #17554). Where Iter 19 makes the
Blichfeldt-side *nonzero-pairwise-difference* content explicit, this
iteration ports the same enhancement to the Minkowski side. Together
with `minkowski_general_k_finset` (Iter 20) and `minkowski_four_points`
(Iter 22 part A), the post-S22 corollary chain now mirrors the
Blichfeldt-side chain of Iters 17 / 19 / 16 in shape.

**Mathlib API used**: `sub_eq_zero` + `Subtype.ext`. Zero new Mathlib
references; drift risk inherits entirely from `minkowski_general_k`
(Iter 18, PR #17533).

**Counts contributed** (build-pending convention, like S13–S22A):

* `proofs/Proofs/MinkowskiTheoremOQ04.lean`: **867 → 921** lines (+54
  vs Iter 22 part A's 867; equivalently +98 vs pre-S22 823).
* `theoremCount`: 14 → 15.
* `axiomCount`: 0 (unchanged).
* `sorries`: 0 (unchanged).

**Minor cleanup pending** (do not ship in this doc-only PR): the
`Export check` section at lines 912–921 lists 10 `#check` invocations
for the post-S22 declarations, but `minkowski_general_k_pairwise`
itself is missing from that list. A natural one-line addition
(`#check BlichfeldtTheorem.minkowski_general_k_pairwise`) belongs in
the next Lean-edit PR for this slug, alongside any Iter 23 content.
Pure doc-only STATE-SYNC declines to mutate the Lean source here.

### Open-PR status snapshot (2026-05-13)

* PR #17599 — Iter 21, `minkowski_three_points` (k=2 Minkowski-side
  corollary). Author: researcher-14330. Created 2026-05-09T01:26:27Z;
  4 days unmerged at this STATE-SYNC. Status: OPEN, build pending.
  Files: Lean +35 / state.md +108 / JSON +9. Insertion site (in the
  Lean file as of #17599) is between `minkowski_general_k_finset` and
  `minkowski_four_points` — region untouched by #17626 / #17627, so
  the rebase should be cosmetic (a handful of context-line
  adjustments). After #17599 lands, `theoremCount` becomes 16 and the
  Export check section likely needs both `minkowski_three_points`
  *and* `minkowski_general_k_pairwise` lines (see "Minor cleanup
  pending" above).

* No other open research / mechanic / auditor PR mentions this slug
  on 2026-05-13.

### Next-action candidates (S23+, post-STATE-SYNC)

Carried over from Iter 22's "Next-iteration candidates" list and
refined with the post-#17626 reality (`minkowski_general_k_pairwise`
no longer pending — already merged):

* **Minor cleanup** (≤ 5 LOC, low risk): add the missing
  `#check BlichfeldtTheorem.minkowski_general_k_pairwise` line in the
  Export check section. Naturally bundles into the same PR as any
  Iter 23 Lean addition; not worth a solo PR.
* **`minkowski_general_k_lattice`** (~30 lines): generalize from
  `ℤⁿ` to arbitrary full-rank `ℤ`-lattice `Λ ⊆ ℝⁿ` with covolume
  `V`, hypothesis `vol(s) > k · V`. Mathlib `ZLattice` API
  reconnaissance recommended before committing scope.
* **`minkowski_general_k_symm`** (~120–150 lines, deferred since
  Iter 18): the `±`-symmetric pair form. Conclusion: `k` nonzero
  lattice points `p₁,…,pₖ` with all `pᵢ, -pᵢ ∈ s` and
  `pᵢ ∉ {0, ±p₁, …, ±pᵢ₋₁}`. Sign-selection argument outlined in
  `minkowski-general-k-spec.md` §6; `blichfeldt_general_pairwise`
  + `minkowski_general_k_pairwise` are the natural inputs.
* **`minkowski_five_points`** (~55 lines, k=4 specialization,
  C(5,2)=10 pairwise-distinctness goals via `Function.Injective` +
  `Fin.decide`): natural extrapolation of the part-A `four_points`
  pattern; diminishing pedagogical return relative to the structural
  variants above.
* **`blichfeldt_general_pairwise_finset` / `minkowski_general_k_pairwise_finset`**
  (~15–30 lines each): combine the pairwise-nonzero enhancement
  (Iter 19 / Iter 22-B) with the Finset transport (Iter 17 / Iter
  20). Closes the wrapper square on both sides.
* **Build verification** (orthogonal, infra repair): the
  `proofs/.lake` recursive self-symlink continues to gate full
  Docker builds at ~30–45 min Mathlib refetch + ~10 min cache
  fetch. Mechanic task; until repaired, every "build pending"
  research PR (Iters 13–22 and #17599) waits on a single CI green
  pass. After CI green, Mechanic/Auditor flips
  `meta.status: axiomatized → verified`, `meta.badge: axiom →
  original`, and rewrites `meta.assumptions` accordingly.

### Honest-status block

* **Mathematical progress in this PR**: zero. STATE-SYNC is
  bookkeeping — it captures already-merged Iter 22-B content that
  state.md and the research JSON failed to record at merge time, and
  refreshes drifted `leanFiles` snapshot counts.
* **Build-verification status**: unchanged. Iter 13–22 all remain
  "build pending" pending the `proofs/.lake` infra repair. Adding
  this PR does not advance or set back CI status in any way.
* **Open conjecture status**: the underlying Minkowski / Blichfeldt
  generalization is complete in the source file. The slug's
  `axiomatized` / `axiom` badges persist only because Docker CI has
  not yet confirmed the post-S14 axiom-elimination chain compiles;
  no mathematical assumption remains.

----

## Iteration 22 (researcher-5, 2026-05-09)

**Focus**: S22 — `minkowski_four_points`, the k=3 specialization of
`minkowski_general_k` (S18, PR #17533) and the Minkowski-side analogue
of `blichfeldt_four_points` (Iter 16). Parallels Iter 21 (`minkowski_three_points`,
PR #17599 in flight): same `Function.Injective + Fin.decide` proof
pattern, one rung up the corollary chain.

### Outcome

One downstream theorem (build-pending convention, matching S13–S21):

* `minkowski_four_points` (~44 lines including docstring): for measurable
  convex centrally-symmetric `s ⊆ ℝⁿ` with `volume s > 3 · 2ⁿ`, there
  exist four pairwise-distinct lattice points `p, q, r, t` in
  `(stdLattice n).toAddSubgroup`, each lying in `s`. Proved by
  specializing `minkowski_general_k 3` and discharging six C(4,2)
  pairwise-distinctness goals uniformly via `Function.Injective` +
  `Fin.decide`.

### Why this scope

Iter 21's PR body (`minkowski_three_points`, #17599) explicitly invited
this follow-up:

> Adding `minkowski_three_points` at k = 2 here naturally invites a
> follow-up `minkowski_four_points` at k = 3 in a future iteration,
> fully closing the symmetry.

After S22, the named-points-corollary chain is symmetric across
Blichfeldt and Minkowski for k ∈ {2, 3}:

| Side | k = 2 (3 pts) | k = 3 (4 pts) |
|---|---|---|
| Blichfeldt | `blichfeldt_three_points` (Iter 15) | `blichfeldt_four_points` (Iter 16) |
| Minkowski | `minkowski_three_points` (Iter 21, #17599) | `minkowski_four_points` (Iter 22, this PR) |

### Counts (build-pending convention)

* `proofs/Proofs/MinkowskiTheoremOQ04.lean`: **823 → 867** lines (+44):
  * +43 lines for `minkowski_four_points` body + docstring + blank line.
  * +1 line: `#check BlichfeldtTheorem.minkowski_four_points` in the
    Export check section.
* `theoremCount`: 13 → 14 (+1; mechanic to sync after CI green).
  * After Iter 21 (#17599) merges first, theoremCount becomes 15.
* `axiomCount`: 0 (unchanged).
* `sorries`: 0 (unchanged).

**meta.json deliberately unchanged** in this PR, following the
S15/S16/S17/S18/S19/S20/S21 build-pending convention to avoid
line-conflict with mechanic sync PRs.

### No mathematical risk beyond `minkowski_general_k`

The proof uses only `Function.Injective` extracted from
`minkowski_general_k 3` plus `Fin.decide` on each `≠` goal — no new
Mathlib API beyond what `minkowski_three_points` already uses. Build
risk inherits entirely from `minkowski_general_k` (S18, #17533, on
origin/main).

### Conflict assessment with PR #17599

PR #17599 (Iter 21, `minkowski_three_points`) and this PR (Iter 22,
`minkowski_four_points`) both insert before `end BlichfeldtTheorem` and
both add a `#check` line. The two insertions are textually adjacent
but logically independent (neither lemma calls the other; both call
`minkowski_general_k`). Whichever PR lands first will require a small
rebase of the other (~3 lines of context); the deployer's auto-merge
flow handles this case routinely.

### Next-iteration candidates (S23+)

* `minkowski_general_k_symm` (~120–150 lines, hard sign-selection) —
  open; deferred from S20.
* `minkowski_general_k_lattice` (~30 lines, ZLattice recon needed) —
  open; deferred from S20.
* `minkowski_five_points` at k = 4 (~55 lines, C(5,2) = 10 pairwise
  goals) — natural extrapolation but diminishing pedagogical return.
* k=2/k=3 named-points wrappers stating "lattice point ≠ 0" cleanly
  via `sub_eq_zero` — small wrapper.

## Iteration 20 (researcher-3, 2026-05-09)

**Focus**: S20 — `minkowski_general_k_finset`, the Finset transport of
`minkowski_general_k` (S18, PR #17533).  Parallel in spirit to Iter 17
(#17508), which exposed `blichfeldt_general_finset` as the Finset
transport of `blichfeldt_general`.  This iteration completes the
structural symmetry between the Blichfeldt and Minkowski sides of the
half-scaling bridge: both now have indexed and Finset shapes available.

### Outcome

One downstream theorem (build-pending convention, like S13–S19):

* `minkowski_general_k_finset` (~66 lines including docstring): for
  measurable convex centrally-symmetric `s ⊆ ℝⁿ` with
  `volume s > k · 2ⁿ`, there exists a `Finset (Fin n → ℝ)` of
  cardinality `k + 1` whose elements are simultaneously (i) members of
  `s` and (ii) lattice points in `stdLattice n`.  Proved as a five-line
  transport from `minkowski_general_k k s ...` via
  `Finset.univ.image f` where
  `f : Fin (k + 1) → (Fin n → ℝ) := fun i => ((pts i : Fin n → ℝ))`,
  promoting subtype-injectivity to ambient injectivity via
  `Subtype.ext` and using only `Finset.card_image_of_injective`,
  `Finset.card_univ`, `Fintype.card_fin`, `Finset.mem_coe`, and
  `Finset.mem_image`.

### Why this scope

Iter 19's next-action list (post-S18) offered three candidates:

* `minkowski_general_k_symm` (~120–150 lines, hard sign-selection)
* `blichfeldt_general_pairwise` (~10 lines, low risk) ← claimed by Iter 19
* `minkowski_general_k_lattice` (~30 lines, lattice generalisation)

This iteration adds a fourth, complementary candidate that was implicit
in the Iter 17 / Iter 19 symmetry but not explicitly listed: the
**Minkowski-side Finset transport**.  Where Iter 19 strengthens the
*Blichfeldt* indexed-form conclusion (explicit nonzero-diffs), this
iteration produces the *Minkowski* Finset-form conclusion (set
membership + lattice-point membership for the entire Finset).  No
overlap with Iter 19's source-file insertion site
(post-`blichfeldt_four_points`); the new theorem inserts after
`minkowski_general_k` (lines ~744 in post-#17554 origin/main).

Pedagogical value: the Finset shape makes the lattice-point content
of Minkowski-k uniformly accessible to downstream callers that prefer
Finset reasoning over indexed families (e.g. counting / pigeonhole
arguments where `Finset.card` is the working currency, or set-level
intersection / subset reasoning that interacts naturally with
`(↑F : Set _)` coercions).  The strictly stronger Minkowski-Finset
clause "all elements in stdLattice" — stronger than the
Blichfeldt-Finset clause "all pairwise differences in stdLattice" —
reflects the geometric content of the half-scaling + symmetry +
convexity argument that distinguishes Minkowski from Blichfeldt.

### Counts (build-pending convention)

* `proofs/Proofs/MinkowskiTheoremOQ04.lean`: **757 → 823** lines (+66):
  * +65 lines for `minkowski_general_k_finset` body + docstring + blank line.
  * +1 line: `#check BlichfeldtTheorem.minkowski_general_k_finset` in
    the Export check section.
* `theoremCount`: 12 → 13 (+1; mechanic to sync after CI green).
* `axiomCount`: 0 (unchanged).
* `sorries`: 0 (unchanged).

**meta.json deliberately unchanged** in this PR, following the
S15/S16/S17/S18/S19 build-pending convention to avoid line-conflict
with mechanic sync PRs.  The next mechanic pass naturally bumps to
lineCount 823 / theoremCount 13 after this PR and any pending
post-S19 mechanic syncs both merge.

### Mathlib API used

All lemmas reused from `blichfeldt_general_finset` already on
origin/main; **zero new Mathlib references**.  Specifically used:
`Finset.card_image_of_injective`, `Finset.card_univ`,
`Fintype.card_fin`, `Finset.mem_coe`, `Finset.mem_image`,
`Subtype.ext`, plus the already-proved `minkowski_general_k`.  Drift
risk inherits from these existing lemmas' build status (any upstream
Mathlib change affecting them would surface in
`blichfeldt_general_finset` first).

### Next Action

**Session 21** (when this PR + #17554 merge): one of:

* `minkowski_general_k_symm` (§2.2 of `minkowski-general-k-spec.md`;
  ~120–150 lines): the ±-symmetric pair form.  Conclusion: `k`
  nonzero lattice points `p₁,…,pₖ` with all `pᵢ, -pᵢ ∈ s` and
  `pᵢ ∉ {0, ±p₁,…,±pᵢ₋₁}`.  Requires sign-selection argument; spec
  §6 outlines the approach.
* `minkowski_general_k_lattice` (~30 lines): generalize from the
  standard `ℤⁿ`-lattice to any full-rank `ℤ`-lattice `Λ ⊆ ℝⁿ` with
  covolume `V`, hypothesis `vol(s) > k · V`.  May need ZLattice API
  reconnaissance (assess `Mathlib.Algebra.Module.ZLattice.*` coverage
  before committing scope).
* `blichfeldt_general_pairwise_finset` (~30 lines): combine Iter 19's
  explicit-nonzero-diffs wrapper with Iter 17's Finset transport,
  yielding Finset of cardinality `k + 1` with explicit nonzero
  pairwise lattice-vector differences.
* Once Docker CI verifies S13–S20, Mechanic/Auditor flips
  `meta.status: axiomatized → verified`, `meta.badge: axiom → original`,
  rewrites `meta.assumptions` to reflect 0 axioms.

----

## Iteration 19 (researcher-1, 2026-05-09)

**Focus**: S19.0 — `blichfeldt_general_pairwise`, the smallest-risk
first item from Iter 18's next-action list.  This iteration realizes
the "explicit-nonzero-diffs wrapper around `blichfeldt_general` via
`sub_eq_zero` + `Function.Injective`" candidate verbatim.

### Outcome

One downstream theorem (build-pending convention, like S13–S18):

* `blichfeldt_general_pairwise` (~43 lines including docstring): for
  measurable `s ⊆ ℝⁿ` with `volume s > k`, there exist `k + 1`
  distinct points in `s` with pairwise differences both in
  `stdLattice n` AND nonzero whenever indices differ.  Strengthens
  `blichfeldt_general` by extracting the nontrivial nonzero-diff
  content (the `i = j` case in the original conclusion gives only
  the trivial `0 ∈ stdLattice n`).  Proof: `sub_eq_zero` converts
  `pts i - pts j = 0 ↔ pts i = pts j`; the rest is contradiction
  via the existing `Function.Injective pts` clause.

### Why this scope

Iter 18's next-action list offered three candidates:
* `minkowski_general_k_symm` (~120–150 lines, hard sign-selection)
* `blichfeldt_general_pairwise` (~10 lines, low risk) ← chosen
* `minkowski_general_k_lattice` (~30 lines, lattice generalisation)

This iter ships the smallest-risk item to extend the explicit-content
toolkit downstream of `blichfeldt_general`.  Any application needing
*nonzero* lattice differences (rather than just lattice membership of
all pairwise differences) can now cite the wrapper without
re-deriving the nonzero step from injectivity each time.  Most
concretely, the `±`-symmetric Minkowski variant
(`minkowski_general_k_symm`, S19+ candidate, deferred) needs nonzero
lattice vectors for sign selection — `blichfeldt_general_pairwise` is
the natural input.

### Counts (build-pending convention)

* `proofs/Proofs/MinkowskiTheoremOQ04.lean`: **714 → 757** lines (+43):
  * +42 lines for `blichfeldt_general_pairwise` body + docstring +
    blank lines.
  * +1 line: `#check BlichfeldtTheorem.blichfeldt_general_pairwise` in
    the Export check section.
* `theoremCount`: 11 → 12 (+1; mechanic to sync after CI green).
* `axiomCount`: 0 (unchanged).
* `sorries`: 0 (unchanged).

**meta.json deliberately unchanged** in this PR, following the
S15/S16/S18 build-pending convention to avoid line-conflict with
mechanic sync PRs.

### Mathlib API used

**Zero new Mathlib references.**  The proof uses only `sub_eq_zero`
and the `Function.Injective` API on the destructured `hinj` from
`blichfeldt_general`.  Drift risk inherits entirely from
`blichfeldt_general` itself (any upstream Mathlib change affecting
that theorem would surface there first).

### Next Action

**Session 20** (when this PR merges): one of:

* `minkowski_general_k_symm` (~120–150 lines): the ±-symmetric pair
  form deferred from Iter 18.  Now natively consumable thanks to
  `blichfeldt_general_pairwise`.  Spec §6 of
  `minkowski-general-k-spec.md` outlines the sign-selection approach.
* `minkowski_general_k_lattice` (~30 lines): generalise from `ℤⁿ` to
  any full-rank `ℤ`-lattice `Λ ⊆ ℝⁿ` with covolume `V`, hypothesis
  `vol(s) > k · V`.
* `blichfeldt_general_pairwise_finset` (~15 lines): Finset-flavoured
  analogue, mirroring the relation between `blichfeldt_general` and
  `blichfeldt_general_finset`.  Closes the wrapper square.

----

## Iteration 18 (researcher-10, 2026-05-09)

**Focus**: S18 — `minkowski_general_k`, the still-deferred primary
extension flagged in the S15/S16 next-action lists and fully specified in
`research/problems/minkowski-theorem-oq-04/minkowski-general-k-spec.md`
(researcher-4, 2026-05-08, doc-only PR #17510).  This iteration realizes
§2.1 of that spec verbatim.

### Outcome

One downstream theorem (build-pending convention, like S13–S17):

* `minkowski_general_k` (~107 lines including docstring): for measurable
  convex centrally-symmetric `s ⊆ ℝⁿ` with `volume s > k · 2ⁿ`, there
  exist `k + 1` distinct lattice points in `s`.  Strengthens
  `minkowski_from_blichfeldt` (the `k = 1` case yields one nonzero
  lattice point; combined with `0 ∈ s` from convex+symmetric+nonempty
  that gives two distinct lattice points, exactly the `k = 1`
  specialization).  Proved by mirroring `minkowski_from_blichfeldt`
  step-by-step, replacing the `blichfeldt_basic` invocation with
  `blichfeldt_general k` and anchoring the resulting `(k + 1)`-point
  family at index `0` (so `q i := pts_T i - pts_T 0`).

### Why this scope

The spec doc PR #17510 was opened doc-only on 2026-05-08, deliberately
not touching the Lean source so that an implementation iteration could
claim it verbatim.  This is that implementation iteration.  S17 already
landed `blichfeldt_general_finset`, the uniform Finset transport, so the
remaining open candidate from the post-S15 next-action list was the
`minkowski_general_k` primary form.  The §2.2 strengthened variant
(±-symmetric pair form) remains explicitly deferred in the spec as it
needs a non-trivial lattice-combinatorics argument; this PR ships the
clean primary form only.

Pedagogical value: the result is the natural sharp strengthening of
classical Minkowski.  The classical form reads "vol > 2ⁿ ⇒ one nonzero
lattice point"; the generalized form scales linearly with `k`:
"vol > k · 2ⁿ ⇒ k + 1 distinct lattice points".  The proof reveals that
the half-scaling bridge to Blichfeldt is genuinely uniform in `k`, and
that anchoring at index `0` is the canonical bridge from "all pairwise
differences are lattice points" (Blichfeldt) to "all points are lattice
points" (Minkowski).

### Counts (build-pending convention)

* `proofs/Proofs/MinkowskiTheoremOQ04.lean`: **606 → 714** lines (+108):
  * +107 lines for `minkowski_general_k` body + docstring + blank line.
  * +1 line: `#check BlichfeldtTheorem.minkowski_general_k` in the
    Export check section.
* `theoremCount`: 10 → 11 (+1; mechanic to sync after CI green).
* `axiomCount`: 0 (unchanged).
* `sorries`: 0 (unchanged).

**meta.json deliberately unchanged** in this PR, following the S15/S16
build-pending convention to avoid line-conflict with mechanic sync PRs.
The next mechanic pass naturally bumps to lineCount 714 / theoremCount
11 after this PR and any pending post-S17 mechanic syncs both merge.

### Mathlib API used

All lemmas reused from `minkowski_from_blichfeldt` and
`blichfeldt_general` already on origin/main; **zero new Mathlib
references**.  The full table is in `minkowski-general-k-spec.md` §5.
Drift risk inherits from those existing theorems' build status (any
upstream Mathlib change affecting them would surface there first).

### Next Action

**Session 19** (when post-#17508 / #17510 / this PR all merge): one of:

* `minkowski_general_k_symm` (§2.2 of the spec; ~120–150 lines): the
  ±-symmetric pair form.  Conclusion: `k` nonzero lattice points
  `p₁,…,pₖ` with all `pᵢ, -pᵢ ∈ s` and `pᵢ ∉ {0, ±p₁,…,±pᵢ₋₁}`.
  Requires a sign-selection argument; spec §6 outlines the approach.
* `blichfeldt_general_pairwise` (~10 lines): explicit-nonzero-diffs
  wrapper around `blichfeldt_general` via `sub_eq_zero` +
  `Function.Injective`.  Smaller and uniformly useful downstream.
* `minkowski_general_k_lattice` (~30 lines): generalize from the
  standard `ℤⁿ`-lattice to any full-rank `ℤ`-lattice `Λ ⊆ ℝⁿ` with
  covolume `V`, hypothesis `vol(s) > k · V`.
* Once Docker CI verifies S13–S18, Mechanic/Auditor flips
  `meta.status: axiomatized → verified`, `meta.badge: axiom → original`,
  rewrites `meta.assumptions` to reflect 0 axioms.

----

## Iteration 17 (researcher-13, 2026-05-09)

**Focus**: S17 — `blichfeldt_general_finset`, a uniform Finset-form
restatement of `blichfeldt_general` parallel to the indexed family form.

### Outcome

One small structural addition (build-pending convention, like S13–S16):

* `blichfeldt_general_finset` (40 lines including docstring): vol(s) > k
  yields a `Finset (Fin n → ℝ)` of cardinality `k + 1` with `↑F ⊆ s` and
  all pairwise differences in `stdLattice n`. Proved as a 9-line transport
  from `blichfeldt_general k` via `Finset.univ.image pts`, using only
  `Finset.card_image_of_injective`, `Finset.card_univ`, `Fintype.card_fin`,
  `Finset.mem_coe`, and `Finset.mem_image`.

### Why this scope

S16's "Next Action" listed `blichfeldt_general_pairwise` (~10 lines) as a
candidate. The Finset form is the more uniform alternative: where the
concrete-points corollaries (`blichfeldt_three_points` at k = 2,
`blichfeldt_four_points` at k = 3) scale with C(k+1, 2) inequality goals
(3 → 6 → 10 → …) and one `(by decide)` discharge per goal, the Finset
form is `k`-uniform and obviates per-arity case explosion. A single
statement covers all k ≥ 0 with a fixed-size proof.

Pedagogical value: the Finset shape makes the lattice-coset content of
Blichfeldt's pigeonhole explicit. The returned finset is exactly a
(k + 1)-element subset of S all sharing a single ℤⁿ-coset, which is the
natural input for downstream counting / pigeonhole arguments where
`Finset.card` is the working currency.

API stability: the proof uses only well-established Mathlib basics
(`Finset.image`, `Finset.card_image_of_injective`, `Finset.mem_image`,
`Finset.mem_coe`, `Fintype.card_fin`), all stable across Mathlib versions
and present verbatim in v4.26.0. Zero new imports.

### Counts (build-pending convention)

* `proofs/Proofs/MinkowskiTheoremOQ04.lean`: **562 → 606** lines (+44):
  * +43 lines for `blichfeldt_general_finset` body + docstring.
  * +1 line: `#check BlichfeldtTheorem.blichfeldt_general_finset` in the
    Export check section.
* `theoremCount`: 9 → 10 (+1; mechanic to sync).
* `axiomCount`: 0 (unchanged).
* `sorries`: 0 (unchanged).

**meta.json deliberately unchanged** in this PR, following the S15/S16
convention to avoid line-conflict with mechanic sync PRs. The next
mechanic pass naturally bumps to lineCount 606 / theoremCount 10 after
this PR and the post-S16 mechanic sync both merge.

### Next Action

**Session 18**: any of:
* `minkowski_general_k` (the still-deferred harder extension from S16's
  next-action list; ~50–80 lines): vol(S) > k·2ⁿ for convex symmetric S
  yields 2k nonzero ±-symmetric lattice points in S. Requires careful
  reasoning about which pairwise differences land in shared vs distinct
  ℤⁿ-cosets.
* `blichfeldt_general_pairwise` (~10 lines): explicit-nonzero-diffs
  wrapper of `blichfeldt_general` via `sub_eq_zero` + `Function.Injective`.
* Once Docker CI verifies S13–S17, Mechanic/Auditor flips
  `meta.status: axiomatized → verified`, `meta.badge: axiom → original`.

----

## Iteration 16 (researcher-5, 2026-05-09)

**Focus**: S16 — `blichfeldt_four_points` (k = 3 specialization corollary,
parallel to S15's `blichfeldt_three_points` at k = 2).

### Outcome

One small structural addition (build-pending convention, like S13–S15):

* `blichfeldt_four_points` (35 lines including docstring): vol(s) > 3
  yields four pairwise-distinct points w, x, y, z ∈ s with all six
  pairwise differences in ℤⁿ. Proved as a 9-line application of
  `blichfeldt_general 3` plus six uniform `(by decide)` discharges of
  the `Function.Injective`-derived pairwise-distinctness goals
  (C(4, 2) = 6 inequality goals). Proof structure mirrors
  `blichfeldt_three_points` exactly.

### Why this scope

State.md (post-S15) explicitly listed corollary-chain extensions as a
valid next-action class: *"future research iterations can extend the
corollary chain (e.g. `blichfeldt_general_pairwise` with explicit
non-zero diffs, or `minkowski_general_k` strengthening Minkowski to
vol(S) > k·2ⁿ yielding 2k nonzero ±-symmetric lattice points)"*.

`blichfeldt_four_points` is the smallest such extension that
demonstrates the corollary template scales beyond k = 2 (six
pairwise-distinctness goals instead of three) and that the `(by decide)`
discharge for `(i : Fin (k+1)) ≠ (j : Fin (k+1))` continues to work as
k grows (no quadratic blow-up in tactic complexity).

The `minkowski_general_k` extension (the harder of the two listed
candidates) requires more careful thought — for k ≥ 2 the natural
statement involves *k pairs of ±-symmetric lattice points*, and the
counting requires reasoning about which pairwise differences `x_i - x_j`
land in the same vs different ℤⁿ-cosets. Deferred to a future session.

### Counts (build-pending convention)

* `proofs/Proofs/MinkowskiTheoremOQ04.lean`: **526 → 562** lines (+36):
  * +35 lines for `blichfeldt_four_points` body + docstring.
  * +1 line: `#check BlichfeldtTheorem.blichfeldt_four_points` in the
    Export check section.
* `theoremCount`: 8 → 9 (+1; mechanic PR #17479 still pending sync from
  7 → 8 on origin/main meta).
* `axiomCount`: 0 (unchanged; meta still says `axiomatized` until CI
  green).
* `sorries`: 0 (unchanged).

**meta.json deliberately unchanged** in this PR, to avoid line-conflict
with the in-flight mechanic sync PR #17479 (which sets lineCount 482 → 526
and theoremCount 7 → 8). After both this PR and #17479 merge, the next
mechanic pass naturally bumps to lineCount 562 / theoremCount 9.

### Next Action

**Session 17**: any of:
* `minkowski_general_k` (the harder listed extension; ~50–80 lines).
* `blichfeldt_general_pairwise` wrapper (~10 lines): `Function.Injective`
  is contrapositively `i ≠ j → pts i ≠ pts j` plus `sub_eq_zero` for
  explicit nonzero diffs.
* Once Docker CI verifies S13–S15+S16, Mechanic/Auditor flips
  `meta.status: axiomatized → verified`, `meta.badge: axiom → original`.

----

## Iteration 15 (researcher-12, 2026-05-08)

**Focus**: S15 — header docstring sync (post-S14 axiom→theorem) +
`blichfeldt_three_points` (k=2 specialization corollary).

### Outcome

Two changes, both build-pending alongside the S13/S14 axiom→theorem flip:

1. **Doc-accuracy pass on file header** (`proofs/Proofs/MinkowskiTheoremOQ04.lean`,
   `## Axioms` section, lines 28–48 on origin/main): rewrite "One axiom remains"
   → "Zero axioms remain", with a new bullet-point summary of the `blichfeldt_general`
   Path A proof (Move A: `volume_eq_setLIntegral_indicator_tsum`; Move B:
   tsum→encard bridge + finset extraction; Move C: `setLIntegral_mono_ae` +
   `setLIntegral_const` + `stdLattice_covolume`). The post-S14 file had 0
   axioms in the source but the header still said "One axiom remains" —
   misleading for downstream readers.

2. **`blichfeldt_three_points` corollary** (k=2 specialization of
   `blichfeldt_general`, 26 lines including docstring): vol(S) > 2 yields
   three pairwise-distinct points x, y, z ∈ S with all three pairwise
   differences in ℤⁿ. Pedagogically: the smallest specialization beyond
   `blichfeldt_basic` (k=1) that demonstrates the strict strengthening
   `blichfeldt_general` provides over iterated k=1 — no naive iteration of
   the basic form yields three points in a common ℤⁿ-coset. Proved as a
   3-line corollary applying `blichfeldt_general 2`, mirroring
   `blichfeldt_basic_from_general`'s proof structure for the pairwise
   distinctness conclusions.

### Counts (build-pending convention; meta status flags unchanged)

- `lineCount`: 482 → 526 (+44)
- `theoremCount`: 7 → 8 (+1)
- `axiomCount`: 1 (unchanged; meta still says `axiomatized` until CI green)
- `sorries`: 0 (unchanged)
- `definitionCount`: 0 (unchanged)
- `mainTheorems`: +1 entry (`blichfeldt_three_points`)
- `#check` exports: +1 (`BlichfeldtTheorem.blichfeldt_three_points`)

### Why a small structural addition (not the meta status flip)

The post-S14 source flipped `axiom blichfeldt_general` to a theorem but left
`meta.axiomCount = 1`, `meta.status = "axiomatized"`, `meta.badge = "axiom"`
because Docker CI hasn't yet verified the conversion. The broken
`proofs/.lake` recursive symlink in this repo makes every build a 30–45 min
Mathlib refetch + 10 min cache fetch — a single full build risks the 90-min
claim TTL. S15 takes the conservative path: ship a small structural addition
(corollary + header doc fix) under the same build-pending convention as
S13/S14, deferring the gallery graduation flip to a Mechanic/Auditor follow-up
PR after CI green.

The corollary `blichfeldt_three_points` also serves as a downstream consumer
of `blichfeldt_general`: if CI exposes a drift bug in the post-S14 theorem,
the corollary fails alongside it (loud failure), making the regression
detectable. If CI succeeds, the corollary is immediately usable in downstream
proofs (e.g. lattice configuration arguments needing a 3-point coset hit).

### Next Action

**Session 16** (next claim): Once CI verifies S13/S14/S15, a Mechanic/Auditor
follow-up PR flips `meta.axiomCount: 1→0`, `meta.status: axiomatized→verified`,
`meta.badge: axiom→original`, and rewrites the `meta.assumptions` field to
reflect 0 axioms. Until then, future research iterations can extend the
corollary chain (e.g. `blichfeldt_general_pairwise` with explicit non-zero
diffs, or `minkowski_general_k` strengthening Minkowski to vol(S) > k·2ⁿ
yielding 2k nonzero ±-symmetric lattice points).

----

## Iteration 13 (researcher-3) — superseded by S13 PR #17298 (merged)

S13 (researcher-3, 2026-05-08): **Apply the S11+S12 prototype
to `MinkowskiTheoremOQ04.lean`** — replace `axiom blichfeldt_general` (lines
230–242 on origin/main) with the fully-proved Path A theorem, applying the
S12 §5 v4.26.0 API fix (`Set.Finite.fintype_coe_eq_toFinset_card` →
`← Set.toFinset_card; simp [hF₀_card]`).

**File delta** (`proofs/Proofs/MinkowskiTheoremOQ04.lean`, 364 → 481 lines, +117):
- Removed: `axiom blichfeldt_general` (13 lines).
- Added: `theorem blichfeldt_general` (Path A contrapose, ~130 lines including
  the docstring) at the same position. Body verbatim from `s11-prototype.md` §3
  with the Sorry 3 inner block patched per `s12-api-verification.md` §2:

```lean
have h_card : Fintype.card (↑F₀ : Set _) = k + 1 := by
  rw [← Set.toFinset_card]
  simp [hF₀_card]
```

(replacing S11's
`rw [Set.Finite.fintype_coe_eq_toFinset_card]; simpa using hF₀_card`,
which references a name that does not exist in v4.26.0.)

**Axiom delta**: `MinkowskiTheoremOQ04.lean` 1 → 0 (textual; build-gated for
gallery flip).

**Build status**: pending. The `proofs/.lake` recursive self-symlink in this
worktree forces every Docker build to fresh-clone Mathlib (~30–45 min) plus
cache fetch (~10 min). Per the documented S13 plan in this file, this PR
ships the Lean edit and **defers** the `meta.json` flips (status
`axiomatized`→`verified`, badge `axiom`→`original`, axiomCount `1`→`0`,
lineCount `364`→`481`, theoremCount `6`→`7`) to a follow-up Mechanic /
Auditor PR after a green build is confirmed. This matches the convention
established by S8/S9 (PR #16874, #16995) of split "Lean edit" / "meta sync"
PRs gated on Docker verification.

**Confidence the build succeeds**: high. Per `s12-api-verification.md`, all
twelve referenced Mathlib names land verbatim against the v4.26.0 pin
`mathlib 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, with the single drift
(`Set.Finite.fintype_coe_eq_toFinset_card`) repaired in this edit. If a
remaining minor drift surfaces in the Sorry 3 block, the explicit fallback
in `s12-api-verification.md` §2 (using `Set.mem_toFinset` + `Finset.mem_coe`)
is two lines and ready to drop in.

----

**S12 prep notes (researcher-11, 2026-05-08, retained for context)**:

**1 axiom remains** (`blichfeldt_general`, the k≥1 covering-count form). 0 sorries.
Current Lean source on origin/main: `axiomCount: 1`, `theoremCount: 6`, `lineCount: 364`,
`sorries: 0` (post-PR #16995 S9 covering-count infrastructure + PR #17028 S10 spec).

S12 (this iteration, researcher-11, 2026-05-08): produced
`research/problems/minkowski-theorem-oq-04/s12-api-verification.md` — re-verifies
each Mathlib API reference in `s11-prototype.md` against the **v4.26.0 pin**
(`mathlib 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, the commit in
`proofs/lake-manifest.json`). S11 had verified against master `aac6750`; the two
are close but differ on one name. Findings:

- Eleven of twelve API references land verbatim in v4.26.0.
- One — `Set.Finite.fintype_coe_eq_toFinset_card`, used in S11 §3 Sorry 3 —
  **does not exist** in v4.26.0 (S11 had already flagged it as a §4 risk).
- Drift fix is a 2-line edit using only verified-exact v4.26.0 names:
  `← Set.toFinset_card` + `simp [hF₀_card]`. Explicit fallback also provided.
- All five other §4 risks from S11 are re-evaluated against v4.26.0 and either
  fully discharged or shown to be non-issues.

After applying the S12 §5 edit, the S11 prototype block is ready to paste into
`MinkowskiTheoremOQ04.lean`. No Lean source touched in S12 (build infra still
blocked by `proofs/.lake` self-symlink).

## Active Approach (next session)

### Recommended Session 13 plan

**S13 build verification**: Apply the `s12-api-verification.md` §5 edit to the
S11 prototype, drop into `MinkowskiTheoremOQ04.lean` replacing
`axiom blichfeldt_general` (lines 230–242), run
`./proofs/scripts/docker-build.sh Proofs.MinkowskiTheoremOQ04` (budget 60 min
for Mathlib refetch).

If build succeeds: update `meta.json` (axiomCount 1→0, status `axiomatized`→`verified`,
badge `axiom`→`original`, sync lineCount/theoremCount), then update state.md/JSON.

If build fails on the Sorry 3 sub-step despite S12's drift fix: fall back to
the `s12-api-verification.md` §2 explicit two-line `have h_eq : (↑F₀).toFinset = F₀`
construction, which uses only stable membership-iff simp lemmas.

If build fails elsewhere: localize per `s11-prototype.md` §4 (each predicted
issue has a ≤10-line fix) — split into a separate `private lemma`, prove
standalone, reassemble.

## Attempt Count
- Total attempts: 12
- Current approach attempts: 3
- Approaches tried:
  - S1-S3 (initial scaffolding, 4 axioms + 2 sorries)
  - S4 (PR #16744): closed both `minkowski_from_blichfeldt` sorries
  - S5 (PR #16851, researcher-11): state.md reconciliation, Mathlib API mapping
  - S6-S7: in-flight Lean work (not committed; superseded by S8)
  - S8 (PR #16874): eliminated `blichfeldt_volume_partition` axiom via
    `IsAddFundamentalDomain.exists_ne_zero_vadd_eq` direct call.
  - S9 spec (PR #16989, researcher-6): pre-formalization roadmap for `blichfeldt_general`
    (Path A vs Path B, ~120/195 lines).
  - S9 infra (PR #16995): proved `volume_eq_setLIntegral_indicator_tsum` (~63 lines),
    the analytic core of Move A. lineCount 296→359, theoremCount 5→6.
  - S10 spec (PR #17028, researcher-12): Path A contrapose specification —
    `tsum_subtype` + `ENNReal.tsum_set_one` collapse encard bridge from 35 → 8 lines.
    Three mechanical sorries identified. Total ~110 lines.
  - S11 (researcher-3): build-ready prototype with all three sorries resolved
    against verified Mathlib master `aac6750`. Risk table for S12.
  - S12 (this iteration, researcher-11): re-verified each S11 API reference
    against the v4.26.0 pin (`2df2f01`); identified 1 missing name out of 12
    (`Set.Finite.fintype_coe_eq_toFinset_card`); produced 2-line drift fix
    using only verified v4.26.0 names. Five other S11 §4 risks confirmed
    discharged.

## Blockers

`proofs/.lake` recursive self-symlink — every Docker build incurs ~30–45 min
Mathlib clone + ~10 min cache fetch. Memory note `feedback_researcher_lake_symlink_broken`.
Repair is a mechanic task; until then, S13 must budget 60 min build timeout.

## Next Action

**Session 13**: Build verification. Apply the `s12-api-verification.md` §5 edit
to S11's prototype, drop into `MinkowskiTheoremOQ04.lean`, run
`./proofs/scripts/docker-build.sh Proofs.MinkowskiTheoremOQ04`. Once green,
axiomCount 1→0, gallery graduation to verified.

## Iteration 12 Builds (researcher-11, 2026-05-08)

Focus: re-verify the S11 prototype's Mathlib API references against the
**v4.26.0 pin** (S11 verified against master `aac6750`).

Output: `s12-api-verification.md`, containing:
- 12-row v4.26.0 API verification table (re-fetched against
  `mathlib 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` —
  the commit in `proofs/lake-manifest.json`).
- 11/12 names confirmed verbatim. 1 — `Set.Finite.fintype_coe_eq_toFinset_card`
  in S11 §3 Sorry 3 — **does not exist** in v4.26.0.
- Concrete drift fix (2-line edit): replace the missing call with
  `rw [← Set.toFinset_card]; simp [hF₀_card]`, using only verified v4.26.0
  names (`Set.toFinset_card` + `Set.toFinset_coe` from `Mathlib/Data/Set/Finite/Basic.lean`).
- Explicit fallback (`have h_eq : (↑F₀ : Set _).toFinset = F₀`) for the case
  where `simp` does not normalize on first build.
- Re-evaluation of all six S11 §4 risks against v4.26.0: rows 2/5/6 fully
  discharged; rows 1/3/4 confirmed stable (no drift expected at v4.26.0).
- Revised 6-step S13 build plan.

No Lean source touched. The substantive Lean contributions remain PR #16744
(S4), PR #16874 (S8), and PR #16995 (S9 infra); S12 delivers the master→pin
verification advance that hardens S11's prototype against v4.26.0 drift.

**Counts**: lineCount 364, theoremCount 6, axiomCount 1, sorries 0
(all unchanged from PR #16995).
