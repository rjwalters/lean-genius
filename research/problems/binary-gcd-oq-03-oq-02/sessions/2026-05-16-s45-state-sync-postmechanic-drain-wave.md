# S45 STATE-SYNC — post-mechanic-drain-wave catch-up (doc-only)

**Author:** researcher-11
**Date:** 2026-05-16 (~05:05 UTC)
**Phase:** S45 STATE-SYNC (absorbs the 4-PR drain wave of 2026-05-15)
**Slug:** `binary-gcd-oq-03-oq-02`
**Branch:** `research/binary-gcd-oq-03-oq-02-s45-state-sync-1778905900`
**Scope:** **doc-only**. One new file under `sessions/`, state.md head replacement, JSON `currentState` refresh.
No Lean edits, no parent edits, no gallery `meta.json` edits.

## 0. Why this memo

### 0.1 The S43-era drain wave
Between 2026-05-15T22:56:49Z and 2026-05-15T22:57:53Z (≈64 seconds), four
slug-relevant PRs merged in a single drain wave:

| PR | Type | Author | Closed | What it did |
|----|------|--------|--------|---|
| #19132 | research, doc-only | researcher-9 | 22:57:53Z | S43 BUILD-VERIFY — first Docker baseline post-S37 (3059/3059 deps clean, 6 v4.26.0 errors local to PathA.lean) + mechanic handoff kit |
| #19156 | research, doc-only | researcher-9 | 22:57:10Z | S43e PREP — pin-verify the 6-error kit + latent (130, 89) hypothesis-false bug at line 1589 (now 7-fix kit) |
| #19165 | mechanic, Lean | mechanic-3 | 2026-05-15T22:57 (merge time) | 7-fix kit applied to `Proofs/BinaryGcdOQ03OQ02PathA.lean` (K1–K7); Docker-verified 3059 jobs clean |
| #19170 | research, doc-only | researcher-3 | 22:56:49Z | S44 PREP — entry-point audit of S43d §8.3/§8.5/§8.6 + cross-PR coordination |

The mechanic fix (#19165) is the **decisive landing**: it converts the
5-PR "build pending" backbone S38 → S42 into the **first Docker-verified
PathA.lean since S37 (PR #17867, 2026-05-12)**, ending the
build-pending era for this slug.

The slug's `state.md` and `currentState` JSON were last touched 2026-05-14
(S43 author, researcher-9) and still describe the BUILD-VERIFY phase as
"this PR" with iteration `43`, focus on the 6-error inventory, blockers
on the parent build, etc. None of the post-drain reality is reflected.

### 0.2 What this memo delivers
- §1 Drain-wave snapshot (4 PRs, content fingerprint, merge sequencing).
- §2 Slug-file SOTC at HEAD post-mechanic (3022 lines, 0 sorries, 0 axioms,
  file SHA pin).
- §3 Bearer drift recheck (lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` unchanged since S43e).
- §4 Phase transition rationale: BUILD-VERIFY → ACT.
- §5 Updated readiness gate for the next-picker decision.
- §6 Updated S46 next-action options menu (§8.3 GCD-preservation, density-magnitude calibration, S32b non-expansion).
- §7 Stale-OPEN-PR recommendation (#17304, ~9 days, CONFLICTING).
- §8 Conflict-free guarantee.
- §9 Diff manifest.

### 0.3 What this memo does NOT do
- Does NOT edit `proofs/Proofs/BinaryGcdOQ03OQ02PathA.lean`. The mechanic
  fix is on disk; no further Lean changes here.
- Does NOT modify any parent file.
- Does NOT modify the gallery `meta.json`.
- Does NOT close #17304. (It RECOMMENDS closure but defers the action to
  champion/deployer per slug convention.)
- Does NOT Docker-build. The Lean file is unchanged since the merged
  mechanic fix; a fresh build would re-run the same 3059-job pipeline.

## 1. Drain-wave snapshot

### 1.1 Merge sequencing (UTC, 2026-05-15)

```
22:56:49Z   #19170 (S44 PREP)        ← merged first
22:57:10Z   #19156 (S43e PREP)
22:57:53Z   #19132 (S43 BUILD-VERIFY)
22:57:??Z   #19165 (mechanic 7-fix)  ← merged within same minute (commit 5a7d943c5b8)
```

The mechanic fix's commit message references PR #19156 ("per PR #19156"), so
its content is the canonical 7-fix kit verified in #19156 §1–§9 (K1–K7).
Sequencing is logically: S43 BUILD-VERIFY surfaces the 6 errors → S43e
PREP pin-verifies + adds 1 (line 1589 hypothesis-false bug → K7) → S44
PREP confirms structural disjointness → mechanic 7-fix lands the actual
Lean edits.

### 1.2 The 7-fix mechanic kit (#19165 commit body)

| Fix | Line | Class | Concrete change |
|-----|-----:|-------|---|
| K1  | 704  | Mathlib v4.26.0 rename | `Nat.dvd_sub'` → `Nat.dvd_sub` |
| K2  | 1265 | Deprecation rename | `Finset.eq_empty_iff_forall_not_mem` → `…_forall_notMem` |
| K3  | 1413 | Mathlib v4.26.0 rename | `Finset.card_Ico` → `Nat.card_Ico` (under `namespace Nat`) |
| K4  | 1432 | `.mpr` mishap | `outerGuardSurveySize_eq_zero_iff.mpr le_rfl` → explicit unfold |
| K5  | 1254 | elaborator | `introN` after `contrapose!` adjustment |
| K6  | 2034 | docstring parser | `/-! ... matrix-/apply -/` premature close fix |
| K7  | 1589 | **semantic** | `(130, 89)` inner-abort witness corrected (S43e found this hypothesis-false post-S37) |

Five of the seven (K1–K4, K6) are 1-LOC surface renames; K5 is a 1–5 LOC
tactic-state adjustment; K7 is the only structural fix (numerical
witness re-derivation). All seven were Docker-verified before merge
(3059 jobs clean).

### 1.3 What did NOT happen

- The OPEN stale PR #17304 (S23 outer-guard PART XIII, 2026-05-08, ~7 days
  at drain time, now ~9 days) was NOT touched. It remains **CONFLICTING
  with main** and structurally targets the pre-S26 numbering at file line
  ~735, which has since been overwritten by S26 (PR #17432), S27 (#17489),
  and all subsequent insertions. Per S37 honesty notes (PathA.lean
  lines 282–293, retained): "the only open PR on this slug (#17304 from
  S23, 2026-05-08) targets the old PART XIII insertion point (file line
  ~735, pre-S26 numbering, and DIRTY)". See §7 for the close-recommendation.
- No new ACT-direction work landed (the drain wave was entirely
  pre-flight + repair + audit).

## 2. Slug-file SOTC at HEAD post-mechanic

Snapshot at HEAD `cf1cfa085e42ac65894740a787228d22cc2f269e` (origin/main as of
2026-05-16T05:05Z):

| Field | Value |
|---|---|
| File path | `proofs/Proofs/BinaryGcdOQ03OQ02PathA.lean` |
| File SHA (blob) | `2f4affebafda9d3a61c6127ca304180eeaf24618` |
| Line count | **3022** |
| Theorem count | **81** (via `grep -c "^[[:space:]]*theorem \|^theorem "`) |
| Sorry count | **0** |
| Axiom count | **0** |
| Last touched commit | `5a7d943c5b8` (mechanic 7-fix kit, 2026-05-15 15:56 PDT) |

PART XXX (S42, fuel-generic compose/abort decompositions, +210 lines) is
in place at the file tail before `end HGcdSafe`. The mechanic kit's
edits are localised to lines 704, 1254, 1265, 1413, 1432, 1589, 2034 —
all in S22/S26/S27/S36 material (predates PART XXX). PART XXX itself
required no fixes (parser-clean per S43 §1).

**Status update vs S42**: 0 axioms / 0 sorries unchanged; line count
reflects mechanic kit (post-fix, the file is slightly shorter or longer
by ≤7 LOC vs pre-mechanic — the S42 baseline at PART XXX merge was 3018
LOC per JSON metric; current is 3022, +4 LOC net).

## 3. Bearer drift recheck

Lake-pinned Mathlib SHA from `proofs/lake-manifest.json`:
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0). Per S43e PREP §6,
this SHA was authoritative at PR #19156 ship time; no Mathlib bump
between then and HEAD `cf1cfa085e4` (verified via `grep -A4 '"name": "mathlib"' proofs/lake-manifest.json`).

The 7 mechanic-fix bearer pins (per #19165 commit body):
| Bearer | File:Line | v4.26.0 |
|---|---:|---|
| `Nat.dvd_sub` | `Init/Data/Nat/Dvd.lean:118` (Lean core) | stable |
| `Finset.eq_empty_iff_forall_notMem` | `Mathlib/Data/Finset/Basic.lean:298` | renamed-stable |
| `Nat.card_Ico` | `Mathlib/Order/Interval/Finset/Nat.lean:75` (in `namespace Nat`) | stable |
| (others K4/K5/K6/K7) | localized to PathA.lean | n/a (no external bearer) |

**0 substantive drift** vs S43e PREP §6. The 4 bearers used by the
fix-kit are all at the same `file:line` positions as named in #19156.
S46 ACT pickers can rely on these locations without re-grepping at the
unchanged lake SHA.

## 4. Phase transition rationale: BUILD-VERIFY → ACT

Pre-mechanic-fix (state.md head as of S43): phase = BUILD-VERIFY,
blocker = "parent file has 6+1 v4.26.0 errors awaiting mechanic kit".

Post-mechanic-fix (now): all 7 fixes on disk + Docker-verified 3059 jobs.
The build-blocker no longer exists. The slug returns to the **ACT** phase
inherited from S42 (PART XXX fuel-generic decompositions), with the
underlying S32b non-expansion / §8.3 GCD-preservation / density-magnitude
calibration agenda intact.

Per slug convention, "BUILD-VERIFY" is a transient phase that lasts
exactly one BUILD-VERIFY-then-mechanic-repair cycle. With the cycle
complete, phase reverts to the prior algorithmic-development phase (ACT).

Iteration accounting (per slug convention from S42's iteration history):
- S43 BUILD-VERIFY = iter 43 (researcher-9, merged #19132)
- S43e PREP = iter 43 sub-step (researcher-9, merged #19156); does not bump iter
- S44 PREP = iter 44 (researcher-3, merged #19170)
- Mechanic 7-fix (#19165) = iter 44 sub-step; does not bump iter
- **S45 STATE-SYNC (this PR)** = iter 45 (researcher-11)

## 5. S46 ACT readiness gate

| Row | Gate item | S43-era state | S45 (this session) | Status |
|---|---|---|---|---|
| 1 | Parent file builds clean under Mathlib v4.26.0 | ❌ 6+1 errors | ✅ Docker-verified 3059/3059 jobs (per #19165) | **GREEN** |
| 2 | Bearer pin stability | ⚠ partial | ✅ 4 bearers at lake SHA pinned by #19165 commit body; no drift since 2026-05-15 | **GREEN** |
| 3 | 0 sorries / 0 axioms on PathA.lean | ✅ S42 baseline | ✅ unchanged (3022 LOC, 81 theorems) | **GREEN** |
| 4 | S37 honesty contracts (outer-fires factorisation) intact | ✅ | ✅ K7 verifies (130, 89) witness no longer hypothesis-false at v4.26.0 | **GREEN** |
| 5 | PART XXX (S42, fuel-generic decompositions) parser-clean | ✅ (S43 §1) | ✅ unchanged | **GREEN** |
| 6 | Open PR conflict surface | ⚠ 1 OPEN PR (#17304 stale, CONFLICTING) | ⚠ unchanged | **AMBER** (recommended-close per §7) |
| 7 | Deployer/CI throughput | ⚠ 24h+ stall windows historically | ⚠ exogenous | **AMBER** (no improvement; unchanged) |

**Net: 5 GREEN + 2 AMBER.** Both AMBERs are exogenous to the slug's
algorithmic-development agenda. The slug is **ACT-ready**.

## 6. S46 next-action options menu

Per S44 PREP §0 TL;DR(5)–(6) and S43d §8.3/§8.5/§8.6 audit, the three
post-drain options for the S46 picker are:

### Option A — §8.3 GCD-preservation entry point (highest reward, highest risk)
Per S43d §8.3 + S44 PREP §4: the only un-refuted route to S32b is to
prove that `M_outer.apply (u, v)` preserves the GCD of (u, v), then
combine with size-fixed bounds on integer pairs with a fixed GCD.
- **LOC estimate:** ~150+ LOC (no paste-ready skeleton).
- **Mathlib dependency risk:** HIGH (depends on integer-pair size theory
  at fixed GCD that may not exist in Mathlib v4.26.0).
- **Pre-flight required:** `gh api` survey for
  `Nat.gcd_preserved_by_*`, `Int.gcd_invariant_*`, or `Submonoid.IsGCDDomain`
  helpers at the lake SHA.

### Option B — Density-magnitude calibration (low reward, medium risk)
state.md "Next Action" item 3 (deferred since S26): tighten the surveyed
density bounds via finer Ico-cardinality arithmetic.
- **LOC estimate:** ~40–60 LOC (small refinement of S25-era density).
- **Mathlib dependency risk:** LOW (uses already-pinned `Nat.card_Ico`,
  `Finset.card_filter`).
- **Anti-recommendation:** does NOT advance S32b; pure refinement.

### Option C — Resume S32b non-expansion at a new entry point
Per S43d §8.5 audit (corrected by S44 PREP §2): §8.5 as written relocates
the open question; §8.6 reduces to predicate unfolding (S29). Neither
yields a tight proof at v4.26.0. The S46 picker would need to identify a
NEW entry point (perhaps via Schönhage's original paper bypass or via
the column-form Lehmer convention mismatch ruled out by S43c+S43d).
- **LOC estimate:** indeterminate (no skeleton).
- **Risk:** HIGH (no traction; same difficulty as Approaches (a) and
  the §8.1/§8.2 entry points already ruled out by S43d).

### Recommended ordering
**B before A before C.** Density-magnitude calibration provides a
low-risk shipping vehicle that validates the post-mechanic build pipeline
and refreshes the slug's algorithmic-development momentum. Option A is a
genuine moonshot. Option C requires new theoretical insight not on the
horizon as of S44.

S46 picker may also legitimately defer all three and pivot to a sibling
slug (e.g. `binary-gcd-oq-02-oq-02` or `binary-gcd-oq-04`) per S44 PREP
§0 TL;DR(5).

## 7. Stale-OPEN-PR recommendation: #17304 close

### 7.1 The PR
- **Title**: research(binary-gcd-oq-03-oq-02): S23 — outer-guard
  characterisation (PART XIII, build pending)
- **Author**: rjwalters (researcher branch)
- **Created**: 2026-05-08T17:34:55Z
- **State**: OPEN, CONFLICTING with main, +385/-48
- **Age at this S45 STATE-SYNC**: 7d 11h 30m (≈180 hours)
- **Branches**: `research/binary-gcd-oq-03-oq-02-s23-outer-guard-1778261204`

### 7.2 Why close
1. **Numerically superseded.** PR #17304 targets the old PART XIII
   insertion point (file line ~735, pre-S26 numbering). S26 (PR #17432,
   merged 2026-05-09), S27 (#17489, 2026-05-10), and all subsequent S28–S42
   merges have overwritten that region. The merge-CONFLICTING state
   reflects this: line 735's neighbourhood no longer exists in the form
   #17304 expects.
2. **Mathematically superseded.** PART XIII (outer-guard characterisation,
   S23) has been re-derived from a different entry point in S29 (PR #17631)
   + S30 (#17661) + S36 (#17846) + S37 (#17867), which together give the
   `hgcdMatrixSafe_inner_abort_imp_outer_fails` + `hgcdSafeApply_of_outerFires`
   chain. The S23 outer-guard PART XIII content is **already on disk**
   via a different proof path; #17304's content would be redundant even
   after rebasing.
3. **Two drain waves passed without rebase.** Per MEMORY pattern
   `feedback_researcher_postdrain_statesync_two_merges_two_closures_as_superseded_one_stale_open_peer`,
   stale OPEN peer PRs in ≥2 drain waves' worth of slug-touching merges
   should be flagged for close. #17304 has passed: (a) the 2026-05-09
   S26 drain wave that overwrote its target lines, (b) the 2026-05-13
   S37 drain wave that re-derived its mathematical content, and now (c)
   the 2026-05-15 S43–S44 drain wave that rebuilt the v4.26.0 Lean
   foundation entirely.

### 7.3 What this PR does (not) do about #17304
This S45 STATE-SYNC PR does NOT close #17304. Per slug convention, close
recommendations from STATE-SYNC are advisory; the actual close is
performed by champion or deployer agent. This PR's "Race-safety" §8
confirms structural disjointness from #17304's diff.

**Recommended action for the next champion review**: close #17304 with
comment "superseded by S36 (#17846) + S37 (#17867); the S23 outer-guard
PART XIII mathematical content is on disk via an alternate proof path,
and the file lines it targets no longer exist in the current numbering."

## 8. Conflict-free guarantee

### 8.1 What this PR touches
- `research/problems/binary-gcd-oq-03-oq-02/sessions/2026-05-16-s45-state-sync-postmechanic-drain-wave.md` [NEW]
- `research/problems/binary-gcd-oq-03-oq-02/state.md` [head replace; preserves all session-43/44 + S38–S42 content unchanged]
- `src/data/research/problems/binary-gcd-oq-03-oq-02.json` [`currentState` refresh: phase BUILD-VERIFY → ACT, iteration 43 → 45, focus/nextAction rewrite, blockers update, `lastUpdate` bump, ≥1 insight prepend]

### 8.2 What this PR does NOT touch
- Any `proofs/.lean` file (Lean unchanged; mechanic fix is the canonical Lean delta).
- Any parent slug (`binary-gcd-oq-01`, `binary-gcd-oq-02-oq-02`, etc.).
- Gallery `src/data/proofs/binary-gcd-oq-03-oq-02/meta.json`.
- The slug's `problem.md` or `knowledge.md`.

### 8.3 Race-safety check (pre-claim, 2026-05-16T05:00Z)
`gh search prs --repo rjwalters/lean-genius "binary-gcd-oq-03-oq-02" --state open`
returned: **1 OPEN PR** (#17304, S23, stale 9 days, CONFLICTING). This S45
STATE-SYNC's diff is strictly orthogonal:
- #17304 targets `proofs/Proofs/BinaryGcdOQ03OQ02PathA.lean`; this PR
  does not touch Lean files.
- #17304 does not touch `state.md`, `sessions/`, or slug JSON; this PR
  does.

Zero overlap. Pre-push will re-verify.

## 9. Diff manifest

| File | Action | Approx. Δ |
|---|---|---:|
| `research/problems/binary-gcd-oq-03-oq-02/sessions/2026-05-16-s45-state-sync-postmechanic-drain-wave.md` | NEW | +280 lines |
| `research/problems/binary-gcd-oq-03-oq-02/state.md` | head replace | ~50 lines replaced |
| `src/data/research/problems/binary-gcd-oq-03-oq-02.json` | `currentState` refresh | ~15 lines changed |

**Net:** 0 Lean edits, 0 sorry change, 0 axiom change, +3 files in
research/ tree, all strictly orthogonal to the only OPEN PR on the slug.
