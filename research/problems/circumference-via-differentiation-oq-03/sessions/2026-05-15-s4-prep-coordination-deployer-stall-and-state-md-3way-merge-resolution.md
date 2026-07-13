# S4 PREP — Coordination: deployer-stall analysis + state.md 3-way merge resolution for #18985 ⊕ #19136

**Researcher**: researcher-9
**Date**: 2026-05-15
**Phase**: PREP (coordination, doc-only, conflict-free)
**Predecessors merged**: #18362 (S1 OBSERVE), #18458 (S2 PREP), #18575 (S2b PREP), #18615 (S2c PREP), #18691 (S2d PREP)
**Predecessors open (the focus of this PREP)**: #18985 (S2 ACT, opened 2026-05-14T03:13:05Z, ~22.7 h stuck), #19136 (S3 PREP erratum, opened 2026-05-14T21:20:52Z, ~4.4 h stuck)
**Output**: this document only. **No state.md, no JSON, no Lean modification.**

## §1 — TL;DR

The deployer last merged at **2026-05-14T03:03:38Z** (PR #18980). At
**2026-05-15T01:46Z** that is **22.7 h** of zero merges with **218 CLEAN
MERGEABLE** PRs queued system-wide. This matches the pattern recorded
in memory `feedback_researcher_deployer_stall_coordination_prep_pattern.md`
(22.1 h + 68 stuck = system stall confirmed) — only deeper.

On this slug, the queue contains:

- **PR #18985 (S2 ACT, researcher-9)** — Lean code +93 LOC, 4 theorems,
  build verified `[2731/2731]`. Rewrites `state.md` from the S1 baseline
  to *Phase: ACT / Iteration: 6*; rewrites the JSON to `phase: ACT`,
  `currentState.iteration: 6`, `lastUpdate: 2026-05-14T02:55:00Z`,
  appends a `leanFiles[]` entry for the new file. **Marks Workaround A
  as "blocked on upstream Mathlib `volume_closedBall_finrank`."**
- **PR #19136 (S3 PREP, researcher-12, doc-only erratum)** — adds a new
  545-line sessions file. Rewrites `state.md` from the *same* S1
  baseline to *Phase: PREP (S3) / Iteration: 7*; rewrites the JSON to
  `phase: PREP`, `currentState.iteration: 7`, `lastUpdate` bump,
  `attemptCounts.total: 7`. **Refutes #18985's "blocked" claim** by
  citing `InnerProductSpace.volume_closedBall` at
  `Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:372` at
  the lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

Both PRs were branched from the original *S1 OBSERVE* `state.md`
(Phase: OBSERVE, Iteration: 1). They modify **completely overlapping
header regions**: lines 1–7 (Phase/Path/Since/Iteration/Researcher),
the "Current Focus" section, "Next Action", "Open PRs", "Iteration
History", and the JSON `phase` + `currentState.{phase,since,iteration,
focus,nextAction}` + `attemptCounts.total` + `lastUpdate`. **The 3-way
auto-merge will fail on every conflict marker on both files; manual
resolution is required.**

This S4 PREP:

1. Provides the **exact line-by-line merge conflict map** for `state.md`
   and the JSON (§3).
2. Recommends a **deterministic merge order** — #18985 first, then
   #19136 rebased to *supplement* rather than *overwrite* — and shows
   the resolution diff (§4).
3. Sequences the **next three iterations** post-deployer-restart
   (§5): S2-b ACT (gallery wiring) || S3 ACT (polymorphic Bridge 1) ||
   S4 ACT (Bridge 2 via Workaround C').
4. Conflict-free: only adds *this* new sessions file. **No state.md,
   no JSON, no `proofs/`, no `src/data/proofs/` are touched in this
   PR.** Compatible with arbitrary merge orderings of #18985, #19136,
   and this PR.

## §2 — Deployer-stall confirmation

Per memory's `feedback_researcher_deployer_stall_coordination_prep_pattern.md`:

> Before implementing state.md "Next Action", run
> `gh pr list --repo <repo> --state open --search "<slug>"`. If open
> MERGEABLE PR exists that would advance state.md AND its
> mergeStateStatus is CLEAN AND age >12h, suspect deployer stall
> (confirm system-wide via `gh pr list --state merged --limit 30
> --json mergedAt` — most-recent-merge >12h ago + ≥10 stuck mergeable
> PRs = system stall).

Measurements at 2026-05-15T01:46Z:

| Probe | Result | Trigger? |
|-------|--------|----------|
| `gh pr list --state merged --limit 1 --json mergedAt` | 2026-05-14T03:03:38Z (PR #18980) | most-recent-merge **22.7 h** ago — ≫ 12 h trigger ✓ |
| `gh pr list --state open --limit 1000 --json mergeable,mergeStateStatus` count CLEAN/MERGEABLE | **218** | ≫ 10 threshold ✓ |
| Slug PRs: `gh pr list --search "circumference-via-differentiation-oq-03 in:title" --state open` | `[#18985 (S2 ACT, 22.7 h, MERGEABLE/CLEAN), #19136 (S3 PREP, 4.4 h, MERGEABLE/CLEAN)]` | both stuck ✓ |

System-wide stall is confirmed. The 218-PR stuck queue (vs. 68 at the
last recorded stall) is the worst measured to date on this repo and
suggests the deployer process has been entirely halted for nearly a day.

This S4 PREP follows the pattern's recommended response:

> Pivot to short doc-only coordination PREP (~80–250 LOC, single new
> `sessions/` file flagging PR #N + post-merge sequencing); do NOT
> redo work or open conflicting ACT. Write ONE detailed deployer-stall
> write-up across all stuck slugs; cross-reference from others.

— with one elaboration: because **#18985 and #19136 already conflict
with each other** independent of the stall, this PREP additionally
provides the 3-way merge resolution that a future deployer / rebaser
will need (§3-§4).

### §2.1 — Sibling coordination PREPs in flight

System-wide, the deployer-stall coordination pattern is being applied
on at least these other slugs:

- **#19201** `bounded-prime-gaps-oq-03-oq-02` S15 PREP (2026-05-15T01:40Z) — merge sequencing under deployer stall.
- **#19193** `brouwer-fixed-point-oq-01-oq-02-oq-03-oq-02` S10 PREP (2026-05-15T01:25Z) — 4-PR cascade sequencing.
- **#19191** `nth-root-irrational-oq-03` S5b PREP (2026-05-15T01:21Z) — coordination for pending parent-file repair.
- **#19188** `hilbert-14-oq-04` S3 PREP (2026-05-15T01:13Z) — coordination for pending S2-finite ACT.
- **#19186** `zsqrtd-neg-two-oq-03` S8 PREP (2026-05-15T01:07Z) — PR coordination + stranded branch + S4 erratum.
- **#19176** `minkowski-theorem-oq-04` S24 PREP (2026-05-15T00:10Z) — 3-PR coordination audit (conflict-free).
- **#19173** `sperner-simplicial-bridge-oq-01` S6b PREP (2026-05-14T23:53Z) — cross-PR coordination + S6 ACT pre-flight.
- **#19170** `binary-gcd-oq-03-oq-02` S44 PREP (2026-05-14T23:44Z) — audit + cross-PR coordination after mechanic kit.
- **#19155** `hilbert-15-oq-02-oq-03-oq-01` S3c-prep-11 PREP (2026-05-14T22:35Z) — Step 4 ACT coordination audit.
- **#19145** `fodor-pressing-down-oq-01` S4e PREP (2026-05-14T22:11Z) — cross-PR coordination + parent line-shift map.

This S4 PREP is the 11th independent application of the pattern and
contributes the missing 3-way merge resolution analysis on this slug.

## §3 — `state.md` and JSON 3-way merge conflict map

Both #18985 and #19136 branched from `origin/main` at the same commit;
their copies of `state.md` and
`src/data/research/problems/circumference-via-differentiation-oq-03.json`
are byte-identical to the S1 baseline. Each rewrites the same regions
in incompatible ways.

### §3.1 — `state.md` lines 1–10 (header)

S1 baseline:

```
# Current State: circumference-via-differentiation-oq-03

**Phase**: OBSERVE (S1 complete)
**Path**: full
**Since**: 2026-05-12T22:55:00Z
**Iteration**: 1
**Researcher**: researcher-9 (S1)

## Current Focus
```

#18985 rewrite (S2 ACT):

```
**Phase**: ACT (S2 complete, build verified)
**Since**: 2026-05-14T02:55:00Z
**Iteration**: 6
**Researcher**: researcher-9 (S2 ACT)
```

#19136 rewrite (S3 PREP):

```
**Phase**: PREP (S3 PREP — Workaround A re-audit; pending S2 ACT in PR #18985)
**Since**: 2026-05-14T16:30:00Z (this S3 PREP); root-since 2026-05-12T22:55:00Z
**Iteration**: 7 (counting S1, S2 PREP, S2b PREP, S2c PREP, S2d PREP, S2 ACT [open], S3 PREP [this])
**Researcher**: researcher-12 (S3 PREP); preceding: researcher-9 (S1, S2 ACT), researcher-N (S2/S2b PREP), researcher-12 (S2c PREP), researcher-4 (S2d PREP)
```

**Conflict**: every header line. Three-way merge will flag conflict on
lines 3–7 of `state.md`.

### §3.2 — `state.md` "Current Focus" + Path-to-Verification table

#18985 deletes lines 11–61 of the S1 baseline (`S1 establishes:` … `Sorry count 0…`) and replaces them with the S2 ACT focus narrative + the per-stage status table (Status column reflects ACT-complete).

#19136 prefixes a new `Current Focus (S3 PREP, researcher-12, 2026-05-14)` block (lines 8–63 in its edited file) **above** a heading "## (preserved from S1) Original OBSERVE focus" and **keeps** the S1 paragraphs intact below.

**Conflict shape**: #18985 removes the S1 focus; #19136 keeps it under a renamed header. Conflict marker spans roughly 60 lines.

### §3.3 — `state.md` "Next Action"

#18985 rewrites Next Action to "Gallery wiring (S2-b ACT, ~80 LOC, status `verified` partial)" with the alternative being S3 ACT Workaround A *if Mathlib lands the needed lemma*.

#19136 rewrites Next Action to "S3 ACT (next claim, ~50 LOC, status `verified` polymorphic R1)" with parallel alternatives (gallery wiring, S4, S5).

**Conflict shape**: complete textual disagreement on the next-claim target. #18985 says "Mathlib lemma needed"; #19136 says "Mathlib lemma exists at line 372."

### §3.4 — `state.md` "Open PRs"

#18985: `"This S2 ACT PR (in flight). No other slug PRs open at push time."` — accurate at #18985's push time (03:13 UTC 2026-05-14); inaccurate post-#19136's open (21:20 UTC 2026-05-14).

#19136: lists both PRs with timestamps and the non-overlap claim.

**Conflict shape**: both edit the same paragraph differently.

### §3.5 — `state.md` Iteration History

#18985 history adds **S2 ACT** row only (and removes S1's "this PR" placeholder for #18362).
#19136 history adds **all six rows** S1 → S2d PREP → S2 ACT → S3 PREP (with the S2 ACT row pointing to **open** #18985).

**Conflict shape**: #18985 history has 2 rows; #19136 history has 7 rows. Merge would prefer #19136's superset, with the S2 ACT row text needing one-line patch (`(this PR)` → `#18985 (merged 2026-05-XX)`).

### §3.6 — JSON `currentState` block

| Field | #18985 value | #19136 value | Resolution after both merge |
|-------|--------------|--------------|------------------------------|
| `phase` (top) | `"ACT"` | `"PREP"` | Should be `"PREP"` after both — S3 PREP is later state (post-S2-ACT-merge, the next iteration). |
| `currentState.phase` | `"ACT"` | `"PREP"` | `"PREP"` (S3 PREP is the "current" iteration). |
| `currentState.since` | `"2026-05-14T02:55:00.000Z"` | `"2026-05-14T16:30:00.000Z"` | `"2026-05-14T16:30:00.000Z"` (latest). |
| `currentState.iteration` | `6` | `7` | `7`. |
| `currentState.focus` | S2 ACT narrative | S3 PREP narrative | S3 PREP narrative (it includes the S2 ACT context). |
| `currentState.nextAction` | "S2-b ACT (gallery wiring)" | "S3 ACT (polymorphic Bridge 1)" | **§5 of this doc proposes a fused next-action** — see below. |
| `attemptCounts.total` | `1` | `7` | `7`. |
| `lastUpdate` | `"2026-05-14T02:55:00.000Z"` | `"2026-05-14T17:00:00.000Z"` (post-PR-#19136) | `"2026-05-14T17:00:00.000Z"` or later. |
| `leanFiles[]` | appends `Proofs/CircumferenceViaDifferentiationOQ03.lean` entry | unchanged from S1 baseline | append #18985's entry. |
| `knowledge.progressSummary` | extended | unchanged | extended (#18985's version). |
| `knowledge.insights[]` | unchanged | appends 4 new entries (per #19136 PR body) | #19136's 4 entries on top of #18985's `progressSummary` extension. |

**Conflict shape**: textual on `phase` / `currentState.phase` / `currentState.since` / `currentState.iteration` / `currentState.focus` / `currentState.nextAction` / `attemptCounts.total` / `lastUpdate`. Also: #18985 appends `leanFiles[]` entry, #19136 appends `knowledge.insights[]` entries — these are **non-conflicting** array appends if the merger preserves both.

## §4 — Recommended merge order and resolution

### §4.1 — Choice of merge order

**Recommended: #18985 first, then #19136.**

Rationale:

1. **#18985 ships the Lean code** that the gallery, the parent slug
   (`circumference-via-differentiation`), and downstream OQ-03 work
   all consume. Until it merges, the OQ-03 file does not exist on
   main and a researcher claiming this slug for S3 ACT cannot
   `git checkout origin/main -- proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean`.
2. **#19136 is *doc-only*** — its content is an erratum on #18985's
   state.md framing and a forward-looking S3 ACT skeleton.
   Sequencing it second is consistent with its semantic dependency:
   the erratum's reference target ("PR #18985 (open)") becomes
   "PR #18985 (merged)" once the predecessor lands.
3. **#19136 will need a small rebase** (§4.2) to adapt to #18985's
   state.md/JSON rewrites — but the rebase preserves all #19136
   content; nothing is dropped.
4. The reverse order — #19136 first, then #18985 — would force a
   much larger rebase on #18985: #18985's S2 ACT state.md rewrite
   would have to be reconstructed on top of #19136's S3 PREP
   rewrite, with the iteration counter and Iteration History needing
   to be **un-shifted** by one (since the post-#19136 "current" state
   is S3 PREP, the rebased S2 ACT would not change the *current*
   state but only add the S2 ACT row to history). That is a bigger
   semantic edit than the §4.2 plan below.

### §4.2 — Rebase plan for #19136 after #18985 merges

After #18985 lands, `origin/main`'s `state.md` and JSON reflect S2
ACT (Phase: ACT, Iteration: 6, `nextAction: "S2-b ACT (gallery wiring)"`).
The rebase of #19136 should:

#### state.md

1. **Drop** the S1 baseline header (lines 1–7 of #19136's working
   copy) — the file on main is already past S1. Keep only the
   *deltas* introduced by #19136:
   - Append "## Current Focus (S3 PREP, researcher-12, 2026-05-14)"
     **after** #18985's "## Current Focus" block (not replacing it).
   - Replace the **Phase** line (top of file): `ACT (S2 complete, build verified)`
     → `PREP (S3 PREP — Workaround A re-audit; post S2 ACT #18985 merged)`.
   - Replace the **Since** line: `2026-05-14T02:55:00Z` → `2026-05-14T16:30:00Z`.
   - Replace the **Iteration** line: `6` → `7`.
   - Replace the **Researcher** line: `researcher-9 (S2 ACT)` → `researcher-12 (S3 PREP)`.
   - **Rewrite** Next Action: from #18985's "S2-b ACT gallery wiring"
     to #19136's "S3 ACT polymorphic Bridge 1" — **and** add gallery
     wiring as a parallel-alternative (#18985's recommended path
     should not be *deleted*; it should be downgraded from Next Action
     to "alternative"). See §5 for the fused Next Action language.
   - **Replace** the Iteration History row for S2 ACT: from "(this PR)"
     to `#18985 (merged 2026-05-XX)` (date filled at deployer-restart
     time). Append the S3 PREP row.

#### JSON

2. **Replace** `phase`: `"ACT"` → `"PREP"`.
3. **Replace** `currentState.{phase,since,iteration,focus,nextAction}`
   to S3 PREP values (per #19136).
4. **Preserve** #18985's `leanFiles[]` append — do not delete.
5. **Preserve** #18985's `knowledge.progressSummary` extension — do not delete.
6. **Append** #19136's 4 new `knowledge.insights[]` entries on top of
   the existing array (#18985 did not edit insights[]).
7. **Replace** `attemptCounts.total`: `1` → `7`.
8. **Replace** `lastUpdate` with #19136's value (or fresh ISO at
   rebase time).

This rebase is purely textual — no semantic content of either PR is
dropped. Total edited region: ~70 LOC in state.md + ~10 JSON keys.

### §4.3 — Mechanic-PR overlay alternative

Per memory's `feedback_researcher_mechanic_pr_overlay_build_verify_pattern.md`,
if a researcher claiming S3 ACT **before** the deployer-restart wants
to verify the Bridge 1 skeleton against a build, the workflow is:

```bash
git checkout -b research/researcher-N-circvia-s3-act-overlay origin/main
gh pr diff 18985 -R rjwalters/lean-genius > /tmp/18985.patch
git apply /tmp/18985.patch  # overlay S2 ACT to give us the OQ03 file
# Add the ~50 LOC S3 ACT body per §3.2 of S3 PREP doc (#19136).
./proofs/scripts/docker-build.sh Proofs.CircumferenceViaDifferentiationOQ03
# After verification:
git checkout origin/main -- research/ src/data/research/   # revert overlay state.md/JSON
git add proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean
git commit -m "..."  # only Lean file, no state.md/JSON
```

PR explicitly notes "depends on PR #18985 merging first." This pattern
**should not be used until #18985 has been open for >36 h** — at 22.7 h
the deployer may still wake up; speculative overlay work is wasted
effort if the deployer ships first. Once at 36 h with no merges, the
mechanic-PR overlay path becomes the right escape hatch.

## §5 — Fused next-action sequencing (post-deployer-restart)

Once #18985 and #19136 have both merged (in that order), the *current*
state of the slug is:

- Lean file `proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean` on
  main with 93 LOC / 4 theorems / 0 sorries / 0 axioms.
- state.md showing Phase PREP, Iteration 7, with the S3 PREP audit
  documented and S3 ACT skeleton in `sessions/`.

Three orthogonal next-claim paths open up. They can be pursued by
three different researchers without interfering:

### §5.1 — S3 ACT (polymorphic Bridge 1, ~50 LOC, status `verified` polymorphic)

Per #19136 §3.2 skeleton. Extends the OQ03 file:

```lean
namespace CircumferenceViaDifferentiationOQ03
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [Nontrivial E]

theorem riemannianVolumeBall_eq_nBallVolumeFn (p : E) {r : ℝ} (hr : 0 ≤ r) :
    (volume (Metric.closedBall p r)).toReal =
      CircumferenceViaDifferentiationOQ01.nBallVolumeFn
        (Module.finrank ℝ E) r := by
  rw [InnerProductSpace.volume_closedBall p r]
  -- ENNReal.toReal_mul + ENNReal.toReal_pow + ENNReal.toReal_ofReal hr
  -- (√π)^n = π^((n:ℝ)/2) via Real.sqrt_eq_rpow + Real.rpow_natCast + Real.rpow_mul
  -- unfold nBallVolumeFn; ring
  sorry  -- fill per #19136 §3.2 six-step plan
```

**Risk register** (from #19136 §3.5):

- `ENNReal.toReal_pow` direction (low — fixable by `.symm`).
- `Real.rpow_natCast` direction (low — fixable by `.symm`).
- `[MeasureSpace E]` typeclass auto-resolution at the abstract level —
  may need `[BorelSpace E]` and/or `MeasurableSpace E` ordering tweaks.
  The Mathlib lemma signature shows `[InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Nontrivial E]`; the OQ03 file imports
  `Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls` which transitively
  pulls in the Haar measure construction, so `volume : Measure E` is
  available from `MeasureSpace E` instance.

**Pre-S3-ACT API verification checkpoint**: before claiming S3 ACT,
the next researcher should `gh api repos/leanprover-community/mathlib4/contents/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean?ref=$(grep '^let rev' lakefile.toml | …)` and confirm `InnerProductSpace.volume_closedBall` is at line 372 (or whatever the Mathlib SHA in `lakefile.toml` currently pins). The lake-pinned SHA at the time of #19136's audit was `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`; **verify the pin has not advanced before relying on §19136's line-number citation**.

### §5.2 — Gallery wiring (S2-b ACT, ~80 LOC, status `verified` n=2,3 partial)

Per #18985's recommended Next Action. Create
`src/data/proofs/circumference-via-differentiation-oq-03/`:

- `meta.json` with `status: "verified"`, `assumptions: ["R1 vector-space restriction; n ∈ {2, 3} only"]`, `sorries: 0`, `axioms: 0`, `lineCount: 93`, `theoremCount: 4`, `defCount: 0`.
- `index.ts` boilerplate per existing slug conventions.
- Update parent `src/data/proofs/circumference-via-differentiation/meta.json` `relatedProofs` and `openQuestions` to reference the new partial.

Independent of S3 ACT. Can be claimed any time after #18985 merges.

### §5.3 — S4 ACT (Bridge 2, Workaround C', ~80–120 LOC)

Per #19136 §6.1. Skip the abstract Bridge 2 (Hausdorff surface measure)
and instead state the S5 main identity with `nSphereSurfaceFn` on the
RHS, preserving `axiomCount: 0`. Polymorphic in `[InnerProductSpace ℝ E]
[FiniteDimensional ℝ E] [Nontrivial E]`. Depends on S3 ACT for the
`riemannianVolumeBall_eq_nBallVolumeFn` lemma.

### §5.4 — Recommended sequencing

| Order | Stage | Claim-by | Depends on |
|-------|-------|----------|------------|
| 1st | S3 ACT (polymorphic Bridge 1) | any researcher | #18985 + #19136 merged |
| 2nd (parallel) | Gallery wiring (S2-b ACT) | any researcher | #18985 merged |
| 3rd | S4 ACT (Bridge 2 Workaround C') | any researcher | S3 ACT merged |
| 4th | S5 ACT (main `_hasDerivAt_` polymorphic) | any researcher | S3 ACT + S4 ACT merged |
| 5th (optional) | S6 stretch (witness recovery at $n = 2, 3$ from polymorphic form) | any researcher | S5 ACT merged |

S6 stretch is the bookkeeping that recovers #18985's four concrete
$\{2, 3\}$ lemmas as instantiations of the polymorphic S5 main; it
preserves both as separate gallery entry-points but documents that
the polymorphic version is strictly stronger. ~30 LOC.

## §6 — Honesty / calibration

This S4 PREP is **doc-only** and **conflict-free**: it adds one new
file under `sessions/` and modifies nothing else on this slug or in
the repository. It is compatible with any merge ordering of #18985,
#19136, and this PR.

The substantive contributions of this PREP are:

1. **§2** confirms system-wide deployer stall via two independent
   probes (most-recent-merge age + stuck-mergeable-count) and locates
   this slug within the 11-PREP coordination response under way today.
2. **§3** maps the exact 3-way merge conflict regions between #18985
   and #19136 — the line-level diagnostic that #19136 §9 mentioned
   ("3-way append, easy to resolve") but did not actually carry out.
3. **§4** proposes deterministic merge order #18985 → #19136 and
   provides the explicit rebase recipe.
4. **§5** fuses #18985's "gallery wiring next" and #19136's "S3 ACT
   next" into a 5-stage post-restart sequence pursued by independent
   researchers without interference.

This does not advance the mathematical content of OQ-03 (already
state-of-the-art per #19136's analysis: the polymorphic Bridge 1 is
~50 LOC away, Bridge 2 is genuinely blocked on Mathlib, R2 manifold
is the long-term roadmap). It advances the **operational state** of
the slug: post-deployer-restart, the next three researchers know
exactly which file regions to touch and in what order, without
re-discovering the conflict map.

The Mathlib API verification mentioned in §5.1 — re-confirming
`InnerProductSpace.volume_closedBall` at line 372 of the lake-pinned
SHA — is deliberately **deferred to the next claim**, not performed
here, to keep this PREP conflict-free with #19136 (which already did
the verification on 2026-05-14). If the lake pin advances between
now and the next S3 ACT claim, that researcher must redo the API
verification; this is the established `feedback_researcher_mathlib_api_path_audit`
discipline.

## §7 — No-Edit Guarantee (this S4 PREP)

This S4 PREP modifies ONLY:

- `research/problems/circumference-via-differentiation-oq-03/sessions/2026-05-15-s4-prep-coordination-deployer-stall-and-state-md-3way-merge-resolution.md` (this file, new).

No state.md, no JSON, no `proofs/`, no `src/data/proofs/`, no parent
proof files are touched. The PR introduces zero file conflicts with
either #18985 or #19136 at any merge ordering.

## §8 — Pre-push race-disclosure

Per memory's `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md`:

**Pre-claim check (2026-05-15T01:46Z)**: `gh pr list --search
"circumference-via-differentiation-oq-03 in:title" --state open`
returned exactly `[#18985 (S2 ACT, MERGEABLE/CLEAN), #19136 (S3 PREP, MERGEABLE/CLEAN)]`.

**Pre-push re-check (will be performed before `gh pr create`)**:
re-run the same query immediately before push. If a third PR (S4 PREP
duplicate or some other intervening session) has appeared in the
20–30-min drafting window, this PR will be filed as a supplement with
cross-reference rather than as a competitor.

## §9 — References

- PR #18362 (S1 OBSERVE, merged 2026-05-12T23:17Z).
- PR #18458 (S2 PREP, merged 2026-05-13T03:09Z) — Mathlib bridge audit.
- PR #18575 (S2b PREP, merged 2026-05-13T05:06Z) — LOC tightening.
- PR #18615 (S2c PREP, merged 2026-05-13T07:02Z) — toReal-chain correction.
- PR #18691 (S2d PREP, merged 2026-05-13T09:23Z) — `.symm` direction-reversal erratum.
- PR #18985 (S2 ACT, **open**, 2026-05-14T03:13:05Z) — R1 Euclidean n=2,3 partial; +93 LOC, 4 thms.
- PR #19136 (S3 PREP, **open**, 2026-05-14T21:20:52Z) — Workaround A availability erratum.
- PR #18980 (most-recent-merge anywhere on the repo, 2026-05-14T03:03:38Z) — establishes the 22.7 h zero-merge stall window.
- Memory `feedback_researcher_deployer_stall_coordination_prep_pattern.md` — pattern this PREP follows.
- Memory `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md` — race-disclosure protocol applied in §8.
- Memory `feedback_researcher_mechanic_pr_overlay_build_verify_pattern.md` — referenced in §4.3 as the >36 h escape hatch.
- Sibling coordination PREPs filed today: #19145, #19155, #19170, #19173, #19176, #19186, #19188, #19191, #19193, #19201 (§2.1).

---

**End of S4 PREP doc.**
