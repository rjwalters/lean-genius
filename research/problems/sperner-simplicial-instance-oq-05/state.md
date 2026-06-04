# Research State: sperner-simplicial-instance-oq-05

## Current State

**Phase**: S7 ACT shipped + S8 ALT (b) reconciled via external mechanic mega-batch (#22005, 2026-06-02). Scarf1d leaf file is now registered in `meta.additionalFiles[]`. Remaining S8+ actions: (a) S8 PREP for `scarfWalk_isPanchromatic` signature amendment, (c) S8 ALT 2-D Hex-no-draw (deferred behind sister slug).
**Path**: full
**Since**: 2026-05-12
**Last Updated**: 2026-06-04 (Session 15 S1 STATE-SYNC, researcher-1)
**Iteration**: 13

## Session 15 (this session, 2026-06-04, researcher-1) — S1 STATE-SYNC (S8 ALT (b) external completion + head reconciliation)

**Scope**: doc-only state-sync. No Lean diff, no `meta.json` diff.

**Trigger**: Session 14 (2026-06-01) head listed three pending S8+ actions:
(a) S8 PREP for `scarfWalk_isPanchromatic` signature amendment,
(b) S8 ALT gallery promotion (add `Proofs/SpernerSimplicialInstanceOQ05Scarf1d.lean`
to `meta.additionalFiles[]`), and (c) S8 ALT 2-D Hex-no-draw.

Pre-claim audit (2026-06-04T~21:30Z) shows action (b) was completed externally
by the mechanic mega-batch PR #22005 (`27a6945a83f`, merged 2026-06-02 03:22:26
PDT) titled *"fix(meta): register 25 orphan companions across 25 slugs"*. The
commit added the Scarf1d leaf path to this slug's `meta.additionalFiles[]`
alongside 24 other orphan companions surfaced by `orphan_scan_v8`.

**Action**:
- Updated head **Phase** to acknowledge S8 ALT (b) external reconciliation,
  list the remaining (a) and (c) S8+ actions, and bump **Iteration** 12 → 13.
- Updated **Last Updated** to 2026-06-04 (Session 15 STATE-SYNC, researcher-1).
- Relabeled Session 14 header to drop the now-obsolete "this session"
  parenthetical (carries forward to Session 15).

**Verification**:
- `jq '.meta.additionalFiles' src/data/proofs/sperner-simplicial-instance-oq-05/meta.json`
  → `["Proofs/SpernerSimplicialInstance.lean", "Proofs/SpernerMathlib4.lean", "Proofs/SpernerSimplicialInstanceOQ05Scarf1d.lean"]`.
- `git log --oneline -- src/data/proofs/sperner-simplicial-instance-oq-05/meta.json`
  → top entry is `27a6945a83f fix(meta): register 25 orphan companions across 25 slugs (mega-batch) (#22005)`.
- Counts on `SpernerSimplicialInstanceOQ05.lean`: 185 lines, 3 theorems,
  0 axioms, 0 sorries, 1 def — matches `meta.json` top-level counters exactly.
- Counts on `SpernerSimplicialInstanceOQ05Scarf1d.lean` (additionalFile):
  170 lines, 5 theorems, 4 defs, 0 axioms, 1 real sorry (line 105,
  `scarfWalk_isPanchromatic` — the same pre-existing sorry covered by
  Session 14 §"File diff").

**Remaining Next Action (unchanged from Session 14)**:
- (a) S8 PREP for `scarfWalk_isPanchromatic` signature amendment with parity
  hypothesis (e.g. `c 0 ≠ c m`), then S8 ACT discharge. HIGH risk.
- (c) S8 ALT 2-D Hex-no-draw — deferred behind sister slug
  `sperner-simplicial-instance-oq-01` 2-D triangulation instance.

**No claim status change**; the slug remains in-progress (S8+ work outstanding).

---

## Session 14 (2026-06-01, researcher-1) — S7 ACT (helper lemmas + concrete `decide` soundness)

**Audit finding (S7 entry)**: the existing `scarfWalk_isPanchromatic` theorem statement is **unprovable** without an extra parity/endpoint hypothesis. Counterexample: `m = 3`, `c ≡ 0`, `start = ⟨0, _⟩`, `k = ⟨1, _⟩` — no panchromatic cell exists, walk runs out of fuel OR hits the right boundary stuck, returns a non-panchromatic cell. The S5 PREP §4 discharge plan was sketched without the parity hypothesis and so cannot close as written.

**Decision (S7 ACT)**: defer the signature change to S8 PREP (it has gallery / cross-reference fallout via `exists_panchromatic_constructive`). For S7, scope to **net-additive structural reduction lemmas + concrete `decide`-proven soundness** that any future S8+ discharge will need either way.

**File diff** (`proofs/Proofs/SpernerSimplicialInstanceOQ05Scarf1d.lean`, 118 → 170 LOC):
- 3 new named theorems (0 sorries each):
  - `scarfWalk_eq_scarfWalkAux` (rfl unfolding)
  - `scarfWalkAux_zero_fuel` (rfl base case)
  - `scarfWalkAux_of_panchromatic_start` (positive-fuel short-circuit, `unfold ; simp [h]`)
- 1 anonymous `example` (kernel-level `decide` proof on `m = 3`, `c(n) = ⟦n ≤ 1⟧`, `start = ⟨0, _⟩`, `k = ⟨1, _⟩` — the Scarf walk lands on a panchromatic cell)

Total: 4 declarations, 0 new sorries, 0 new axioms. The pre-existing `scarfWalk_isPanchromatic` sorry is **unchanged** (its discharge is deferred to S8 ACT post-signature amendment).

**Build verification**:
```
⚠ [1098/1098] Built Proofs.SpernerSimplicialInstanceOQ05Scarf1d (7.2s)
warning: Proofs/SpernerSimplicialInstanceOQ05Scarf1d.lean:102:8: declaration uses 'sorry'
Build completed successfully (1098 jobs).
=== Build succeeded ===
```

Result: **PASS**. Single warning is the pre-existing `scarfWalk_isPanchromatic` sorry (unchanged from S6). All 4 new declarations compile clean. `decide` successfully reduces `IsPanchromatic1d c (scarfWalk c (0 < 3) ⟨0, _⟩ ⟨1, _⟩ _)` to `True` at the kernel — **kernel-level Scarf-walk verification** on a concrete 3-cell instance. In-session fix: `by norm_num` → `by decide` for the `Fin` proofs (`norm_num` requires Mathlib.Tactic.NormNum import, out of scope here).

**Next action (S8+)**:
- (a) **S8 PREP** to amend `scarfWalk_isPanchromatic` signature with a parity hypothesis (e.g. `c 0 ≠ c m`), with downstream impact analysis for `exists_panchromatic_constructive`. Then S8 ACT discharges the amended theorem using S5 PREP §4 plan + S7 structural lemmas. Risk: HIGH.
- (b) **S8 ALT gallery promotion**: add Scarf1d leaf file to `meta.json` `additionalFiles[]` (mirror per project_mechanic_additionalfiles_format_convention memory).
- (c) **S8 ALT 2-D Hex-no-draw**: deferred — requires the 2-D triangulation instance from sister slug `sperner-simplicial-instance-oq-01`.

## Session 13 (2026-05-30, researcher-1) — S6 ACT (C2-1d Scarf walk skeleton)

INFRA gates for S5 PREP's "ACT-pending under build pending" qualifier
have lifted (Docker 29.4.1 stable, disk 57 Gi avail at S6 entry).
S5 PREP §3's paste-ready ~95 LOC skeleton transcribed to new leaf
file `proofs/Proofs/SpernerSimplicialInstanceOQ05Scarf1d.lean` with
minor adaptations:

* `open Triangulation` (parent namespace; PREP's `open SpernerSimplicialInstance` does not exist as a namespace)
* `Triangulation.intervalTriangulation` full path

File contents:
- 6 defs (`IsPanchromatic1d`, `step`, `scarfWalkAux`, `scarfWalk`)
- 1 `Decidable IsPanchromatic1d` instance (via `infer_instance`, per F2)
- 2 theorems: `scarfWalk_isPanchromatic` (1 sorry, discharge plan in
  S5 PREP §4) + `exists_panchromatic_constructive` (proof-term using
  the previous)

Total: ~119 LOC, 1 sorry, 0 axioms.

**Build verification**: Docker build of `Proofs.SpernerSimplicialInstanceOQ05Scarf1d`
under recovered INFRA — [result recorded in session memo §"Build verification"].

The single sorry is the soundness theorem `scarfWalk_isPanchromatic`;
S5 PREP §4 has a ~40 LOC discharge plan (monotone-walk invariant +
no-revisit corollary + fuel-exhaustion impossibility). Discharge is
S7's scope.

## Session 12 (2026-05-16, researcher-3) — S5 PREP (C2-1d readiness refresh)

Doc-only readiness gate for the (C2-1d) Scarf walk ACT pending since
S2 PREP #18489 (2026-05-13, T+3d). On review of #18489 against the
parent file at the v4.26.0 pinned Mathlib SHA `2df2f0150c…`, two
material findings emerged:

- **F1 (HIGH — would block paste)**: the recommended skeleton's
  `step` body uses `iadj m i k'` directly, but `iadj` is `private`
  at `proofs/Proofs/SpernerSimplicialInstance.lean:818`. A new module
  pasting `match h_adj : iadj m i k'` would fail with `unknown
  identifier 'iadj'`. Fix: route through the public `T.adj` structure
  field (line 97; `T := intervalTriangulation m hm`).
- **F2 (MED)**: PREP #18489's `Decidable IsPanchromatic1d` instance
  uses an unnecessarily complex `decEq |>.recOn` hand-roll where
  `unfold IsPanchromatic1d ; infer_instance` suffices (`Decidable.not`
  ships in core Mathlib).

This PREP packages both fixes into a consolidated paste-ready
~95 LOC skeleton (one `sorry` for `scarfWalk_isPanchromatic`
soundness; 4-step discharge plan ~40 LOC in §4 of the memo).
Mathlib pin is byte-stable since S3 PREP #18712 (no bearer-line
recheck needed; the F1 fix routes through `T.adj` rather than
`Finset.Basic`, sidestepping the bearer-drift class entirely).

**ACT-readiness gate**: 8/10 GREEN (substantive), 2/10 RED (INFRA:
Docker daemon hung, disk 100%). Next session has the option of S6
PREP-2 (further INFRA-awaiting iteration) or S6 ACT under "build
pending" qualifier (precedent on this slug: #18648, #19105 both
build-pending at merge).

### Files updated (Session 12)

- NEW `research/problems/sperner-simplicial-instance-oq-05/sessions/2026-05-16-s5-prep-c2-1d-readiness-refresh.md`
  (~350 LOC; 9 sections covering F1+F2 corrections, paste-ready
  skeleton, discharge plan, Mathlib bearer audit, readiness gate,
  risk inventory, out-of-scope including mechanic handoff for
  `leanFiles[]` drift, acceptance criteria, references, host context).
  This is the **first session memo under the canonical**
  `research/problems/sperner-simplicial-instance-oq-05/sessions/`
  path (predecessor session memos all live in the misplaced
  `research/sperner-simplicial-instance-oq-05/sessions/` directory;
  cleanup remains mechanic territory).
- `research/problems/sperner-simplicial-instance-oq-05/state.md`
  (this Session 12 entry; head reflects iter 9 → 10, phase update).
- `src/data/research/problems/sperner-simplicial-instance-oq-05.json`
  (`phase`, `currentState.{phase,since,focus,iteration,nextAction,
  attemptCounts.total}`, `knowledge.progressSummary` prepended,
  `knowledge.nextSteps` refreshed to reflect C2-1d ACT-readiness +
  C3 readiness-refresh as parallel target, `lastUpdate`).

**No Lean diff**, no gallery `meta.json` touch, no `leanFiles[]`
edit (the +27 LOC parent-file drift / +1 def-count drift +17 LOC
OQ05 drift is handed off to mechanic per the memo's §6 OOS-2 — see
the ready-to-paste numbers there).

### Build verification

- N/A (doc-only PR; no `.lean` diff; no Mathlib clone needed).
- Docker daemon hung throughout this session (`docker info` returns
  Client section only). Disk at 100% / 4.2 Gi avail. Both
  RED-gated INFRA criteria; both unrelated to slug correctness.
- Mathlib pin verified at `proofs/lake-manifest.json` line containing
  `"rev": "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"`.

### Coordination notes

- Pre-claim probe (~2026-05-16T17:27Z): 0 open PRs on slug. Last
  merged: #19606 mechanic batch lineCount fix at 13:51Z (~T-3.5h
  before claim) — touched only `src/data/proofs/.../meta.json` not
  the research JSON; no scope overlap with this session.
- Branch: `research/sperner-oq05-s5-prep-c2-1d-readiness-1735Z`,
  based on `origin/main @ 535adef5c3d` (S3c-prep-15).
- gh PR creation: explicit `--repo rjwalters/lean-genius` flag set
  per recent fork-remote-resolution gotcha.

### Next Action (post-Session 12)

| Priority | ACT | Effort | Risk | Notes |
|---|---|---|---|---|
| 1 | **S6 ACT (C2-1d) under "build pending"** | ~95 LOC + 1 sorry → 1 PR; or ~135 LOC 0 sorry | MED (soundness sorry discharge) | Paste §3 skeleton from this PREP's memo; F1+F2 already applied. Leaf-only file; `T.adj` is public; precedent #18648 ACT also build-pending at merge. |
| 1 | **S6 PREP-2 (C2-1d) — further INFRA-await** | <20 LOC | LOW | Only if Docker / disk persist RED through next claim window. Re-spot-check bearers, refresh ACT-readiness gate timestamp. |
| 2 | **S6 PREP (C3) readiness refresh** | ~50-150 LOC | LOW (doc-only) | Parallel to (1); the C3 PREP #18392 cascade-audit is T+4d old; a refresh against the parent file's current 1022 LOC + 10 def state would tighten the (C3) ACT plan. |
| 3 | **S6+ ACT (C3) under "build pending"** | ~80 LOC parent edit | MED-HIGH | Parent-file refactor; cascade risk on all importers of `SpernerSimplicialInstance.lean`. Defer until INFRA recovers + parent file is build-verifiable. |
| 4 | **Misplaced-dir cleanup** | — | LOW | Mechanic territory; ~6 slugs affected. Out of scope for researcher. |
| 5 | **`leanFiles[]` drift fix** | <10 lines edit | LOW | Mechanic territory; ready-to-paste numbers in this session's memo §6 OOS-6. |

---

## Session 11 (2026-05-14, researcher-8) — S4 GALLERY

Ships the long-awaited S3/S4 GALLERY ACT for the merged C1 work:

- `src/data/proofs/sperner-simplicial-instance-oq-05/meta.json`
  (~280 LOC: status `verified`, badge `original`, 3 theorems + 1 def
  + 1 example, 0 sorries, 0 axioms, lineCount 186, 5 sections keyed
  to OQ05.lean line ranges, 4 cross-references to
  `sperner-simplicial-instance`, `sperner-mathlib4`, `sperner-mathlib`,
  `brouwer-fixed-point`).
- `src/data/proofs/sperner-simplicial-instance-oq-05/annotations.json`
  (5 annotations: def + 3 theorems + 1 demo).
- `src/data/proofs/sperner-simplicial-instance-oq-05/index.ts`
  (gallery module wiring; `?raw` import on the .lean file).

**No Lean diff.** The gallery uses the auto-discovery glob in
`src/data/proofs/index.ts`, so no manual listing edit is required.
`src/data/proofs/listings.json` is gitignored and regenerated by
`scripts/annotations/build.ts`. The .lean source has been unchanged
since #18941 merged 2026-05-13.

### Files updated (Session 11)

- `src/data/proofs/sperner-simplicial-instance-oq-05/meta.json` (NEW).
- `src/data/proofs/sperner-simplicial-instance-oq-05/annotations.json` (NEW).
- `src/data/proofs/sperner-simplicial-instance-oq-05/index.ts` (NEW).
- `src/data/research/problems/sperner-simplicial-instance-oq-05.json`
  (`phase`, `currentState.{phase,since,focus,iteration,nextAction,attemptCounts}`,
  `knowledge.progressSummary`, `knowledge.builtItems`,
  `knowledge.nextSteps`, `lastUpdate`).
- `research/problems/sperner-simplicial-instance-oq-05/state.md`
  (this Session 11 entry; replaces "next ACT decision" with delivery).

### Build verification

- JSON validity: `python3 -c 'import json; json.load(open(...))'` on
  each of the three new gallery files — all valid.
- Docker build of `Proofs.SpernerSimplicialInstanceOQ05` started but
  exited at the mathlib clone stage (interrupted by Docker capacity
  from concurrent agent containers). The .lean source has been
  unchanged since #18941 merged 2026-05-13 and the gallery files are
  doc-only with no Lean coupling, so the build-pending status of
  this PR is not a regression risk introduced here — it inherits the
  build-pending status of the parent #18648 ACT chain.
- `pnpm build` skipped locally due to node-gyp `better-sqlite3` build
  failure on the host (unrelated env issue); CI / deployer will
  validate.

### What this unlocks

- Public gallery entry at `/proof/sperner-simplicial-instance-oq-05`
  showing the C1 brute-force panchromatic-cell finder with annotations,
  cross-references, and the 1-d demo on `intervalTriangulation 3`.
- A clean separator between OQ-05's shipped (C1) candidate and the
  ACT-pending (C2-1d, C3) candidates: future ACTs can ship their own
  Lean modules + gallery entries without touching the C1 metadata.

### Coordination notes

- Pre-claim probe: 0 open PRs on slug at claim time (researcher-8
  pre-claim race check 2026-05-14 ~17:55 UTC; see memory
  `feedback_researcher_pre_claim_pr_search`). Claim TTL 90 min.
- Worktree CWD: edits use worktree-rooted absolute paths
  `/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-8/...`
  to avoid silent main-repo drift (see memory
  `feedback_mechanic_edit_absolute_main_repo_path_silent_drift`). One
  early Edit to `/Users/rwalters/GitHub/lean-genius/src/data/proofs/listings.json`
  (gitignored) was accidentally directed at the main-repo path before
  the drift was detected; that file is auto-regenerated and not
  committed, so no harm done.

---

## Session 9 (2026-05-14, researcher-12) — canonical-path STATE-SYNC

The prior STATE-SYNC PR #18927 (researcher-1, 2026-05-13 23:06 UTC)
wrote `state.md` to the **non-canonical** path
`research/sperner-simplicial-instance-oq-05/state.md` rather than the
canonical `research/problems/sperner-simplicial-instance-oq-05/state.md`
(per `scripts/research/build.ts` + `.lean/scripts/archive-sessions.sh`,
which both use `research/problems/{slug}/`). The seeker pool / depth-
first claim script reads the canonical path, so the slug was visible
to claim-random as a `Phase: NEW since 2026-05-12T14:35:20Z, Iteration: 1`
**seeker-init stub** even though the active state is iter 8 with 8
merged PRs of substantive research.

**This PR** fixes the seeker-visibility issue by writing the active
state log at the **canonical** path. The misplaced
`research/sperner-simplicial-instance-oq-05/` directory (containing the
fuller 234-LOC state.md, knowledge.md, problem.md, and `sessions/`
subdirectory) is **left in place** — its cleanup (move or delete) is
a separate mechanic / gallery-cleanup class (similar misplaced flat
slug directories exist for `area-of-circle-oq-05-oq-04`, `ballot-
problem-oq-01-oq-02`, `binary-gcd-oq-02-oq-02`, `roth-theorem-oq-02`,
and others, suggesting a one-time mechanic sweep is appropriate
rather than per-slug research patches).

The canonical state.md (this file) reproduces the Session-1-through-8
log inline, references the misplaced dir's deeper content (notably
`knowledge.md`'s Mathlib API survey), and adds Session 9 + the
post-S3-ACT-cosmetic Session 10 entry.

### Files updated (Session 9)

- `research/problems/sperner-simplicial-instance-oq-05/state.md`
  (this file, NEW at canonical path; replaces the seeker-init stub).
- `src/data/research/problems/sperner-simplicial-instance-oq-05.json`
  (`currentState.{focus,nextAction}`, `knowledge.progressSummary`,
  `lastUpdate`).

**No `.lean` diff, no gallery `meta.json` touch.**

---

## Session Log (consolidated, 2026-05-12 → 2026-05-13)

### Session 1 — S1 OBSERVE (2026-05-12, researcher-11, PR #18200)

Surveyed the parent `proofs/Proofs/SpernerSimplicialInstance.lean`
(995 LOC, 28 thms, 0 sorries, 0 axioms) and the abstract framework
`proofs/Proofs/SpernerMathlib4.lean` (732 LOC). Identified the
explicit OQ-stated bottleneck at
`SpernerMathlib4.lean:367`,
`noncomputable def AbstractSimplicialData.findOppositeIdx`
(uses `Classical.choose` on a decidable existential), and the
secondary target `proofs/Proofs/BrouwerFixedPointOQ04OQ04.lean:244`,
`axiom scarf_approx_fixed_point`.

Wrote three candidate formal targets in `problem.md`:
- **(C1)** brute-force enumeration via `Finset.filter` + correctness proof.
- **(C2)** the literal Scarf door-chain walk (1-d sub-target `C2-1d`
  on `intervalTriangulation`; general sub-target `C2-gen` blocks on
  (C3)).
- **(C3)** refactor `findOppositeIdx` from `Classical.choose` to
  `Finset.filter ... .min'`.

### Session 2 — S2 PREP (C3) noncomputable cascade audit (2026-05-12, researcher-3, PR #18392)

Doc-only enumeration of the downstream `noncomputable` declarations
that would inherit computability if (C3) were attempted. Output:
`sessions/2026-05-12-s2-prep-c3-noncomputable-cascade.md` (in
misplaced dir). Independent of (C1) / (C2-1d); leaves (C3) parked.

### Session 3 — S2 PREP (C1) brute-force scaffold (2026-05-13, researcher-9, PR #18459)

Doc-only scaffolding memo for the (C1) `findPanchromaticBrute`
candidate. Pre-resolved the proof sketch
(`Finset.filter |>.toList.head?` definition + characterisation lemma
+ totality via `Triangulation.sperner`); flagged Mathlib name
dependencies as **unverified pending PREP-D**.

### Session 4 — S2 PREP (C2-1d) Scarf walk on intervalTriangulation (2026-05-13, researcher-4, PR #18489)

Doc-only design memo for the (C2-1d) literal Scarf door-chain walk
on `intervalTriangulation`. Defined the walk's termination measure
(visited cells form an injection into a finite type via `adj_symm`
+ `isDoor_iff_of_adj`, bounding walk length by `|T.Cell|`) and
committed the Lean encoding to `Fin (|T.Cell|+1)`-bounded recursion.
**Independent of (C3)** — 1-d case uses no `findOppositeIdx`.
Estimate: ~120 LOC.

### Session 5 — S2 PREP-D Mathlib API audit + C2-1d bridge discharge (2026-05-13, researcher-6, PR #18534)

Doc-only Mathlib API audit pre-resolving the load-bearing names for
both (C1) and (C2-1d) ACTs: `Finset.toList_eq_nil`,
`Finset.Nonempty.toList_ne_nil`, `Finset.nonempty_iff_ne_empty`,
`List.mem_of_head?`. Replaced (C1) PREP's fallback chain with
verified verbatim references. **Caveat** (addressed by S3 PREP):
SHAs were verified against Mathlib HEAD, not the lockfile-pinned
v4.26.0 SHA.

### Session 6 — S2 ACT (C1) findPanchromaticBrute Lean implementation (2026-05-13, researcher-9, PR #18648)

**First Lean diff on this slug.** Ships
`proofs/Proofs/SpernerSimplicialInstanceOQ05.lean` (168 LOC,
3 theorems + 1 `def` + 1 `example` smoke-test, **0 sorries,
0 axioms**):

1. `def findPanchromaticBrute : Triangulation V n → (V → Fin (n+1))
   → Option T.Cell` (`Finset.filter |>.toList.head?`).
2. `theorem findPanchromaticBrute_isSome_iff` — characterisation.
3. `theorem findPanchromaticBrute_eq_some_imp_panchromatic` —
   `some _` ⇒ panchromatic.
4. `theorem findPanchromaticBrute_isSome_of_boundary_odd` —
   totality under the parity hypothesis, via `Triangulation.sperner`.
5. `example : ∃ s, IsPanchromatic … (intervalTriangulation 3 …) s := by decide`
   — kernel-level proof.

**Gallery integration** (`src/data/proofs/sperner-simplicial-instance-oq-05/`)
deferred to a later S3 GALLERY pass — not yet shipped.

### Session 7 — S3 PREP Mathlib SHA-pin bearer audit (2026-05-13, researcher-5, PR #18712)

Doc-only audit revealing four Mathlib bearer-line citations in PREP-D
#18534 and ACT #18648 point to Mathlib HEAD (`23fc2795…`,
2026-05-13 00:45Z) rather than the lockfile-pinned v4.26.0 SHA
(`2df2f015…`, 2025-12-13 10:35Z). Lemma **names** resolve identically
at both SHAs (build risk = 0); line numbers drift −13 to +18 lines.

### Session 8 — STATE-SYNC (misplaced path) (2026-05-13, researcher-1, PR #18927)

Reconciles state.md and JSON with the seven merged PRs. **Wrote to
the non-canonical path** `research/sperner-simplicial-instance-oq-05/`,
not the canonical `research/problems/sperner-simplicial-instance-oq-05/`
— see Session 9 above.

### Session 10 — S3 ACT cosmetic (2026-05-13, researcher-?, PR #18941)

Doc-only S3 ACT cosmetic applying the four pinned-SHA bearer-line
corrections from S3 PREP #18712 to the `## References` block in
`proofs/Proofs/SpernerSimplicialInstanceOQ05.lean`. Fills the
"S3 ACT cosmetic (LOW risk, <20 LOC)" slot listed as `nextSteps[2]`
in the in-flight sibling STATE-SYNC PR #18927.

---

## Aggregate State

| Candidate | Lean status | LOC | Risk | Blocker |
|---|---|---|---|---|
| (C1) `findPanchromaticBrute` brute-force | **SHIPPED** (S2 ACT #18648, 168 LOC, 0/0) + S3 ACT cosmetic (#18941) | — | — | none |
| (C2-1d) Scarf walk on `intervalTriangulation` | PREP designed (#18489), **ACT pending** | ~120 | MEDIUM (termination measure) | none |
| (C2-gen) Scarf walk on general `Triangulation` | DEFERRED | ~250 | HIGH | (C3) must land first |
| (C3) `findOppositeIdx` Classical.choose → computable | PREP audited (#18392), **ACT pending** | ~80 | MEDIUM (verified-parent re-build) | none |
| S3 GALLERY — `src/data/proofs/sperner-simplicial-instance-oq-05/` | **Not yet shipped** | ~3 files (meta.json + index.ts + annotations.json) | LOW | none |
| Misplaced-dir cleanup (mechanic) | **Out of scope here**; ~6 slugs affected | — | LOW | — |

**Aggregate Lean delta**: 168 LOC, 5 declarations (1 `def`, 3 theorems,
1 example), **0 sorries, 0 axioms**.

**Aggregate doc delta**: 8 session memos + state.md + problem.md +
knowledge.md (most under the misplaced dir; canonical path has stub
state.md replaced here), totalling ~2,300 lines across 10+ files.

## Next Action

The natural next ACTs (in priority order):

1. **S3 GALLERY** — promote the merged C1 work to the public gallery
   at `src/data/proofs/sperner-simplicial-instance-oq-05/`. Template
   from `src/data/proofs/sperner-mathlib/` (3 files: meta.json,
   index.ts, annotations.json). LOW risk, ~30 min. **Recommended
   next**: this turns shipped Lean work into a public-facing entry.

2. **S4 ACT (C2-1d)** — Scarf walk on `intervalTriangulation`. The
   literal algorithmic content of OQ-05. ~120 LOC, MEDIUM risk
   (termination measure on visited-cell injection). Per S2 PREP #18489.

3. **S4 ACT (C3)** — refactor `findOppositeIdx` from `Classical.choose`
   to `Finset.filter ... .min'`. ~80 LOC, MEDIUM risk (verified-parent
   re-build). Per S2 PREP #18392. Unblocks (C2-gen).

4. **Misplaced-dir cleanup** — mechanic territory. The flat
   `research/<slug>/` directories for sperner-simplicial-instance-oq-05,
   area-of-circle-oq-05-oq-04, ballot-problem-oq-01-oq-02,
   binary-gcd-oq-02-oq-02, roth-theorem-oq-02, and possibly others
   should be merged into the canonical `research/problems/<slug>/`
   tree via a one-time sweep.

## Active Approach

**Approach 2** (in OQ-05's terms): three independent candidates
(C1/C2/C3) with C1 brute-force shipped, C2-1d / C3 ACT-pending,
C2-gen deferred behind C3.

## Blockers

None on (C1) / (C2-1d) / (C3). Misplaced-dir cleanup is mechanic
territory (one-time sweep, not per-slug).

## Attempt Counts

- Total attempts: 8 sessions, 9 merged PRs (#18200 / #18392 / #18459
  / #18489 / #18534 / #18648 / #18712 / #18927 / #18941).
- Current approach attempts: 9.
- Approaches tried: 1 (three-candidate decomposition C1/C2/C3, with
  C1 shipped).

## Race / coordination notes

- Pre-claim probe (~01:00 UTC, 2026-05-14): 0 open PRs on slug.
  Last merge S3 ACT cosmetic #18941 at 23:05 UTC + STATE-SYNC #18927
  at 23:06 UTC — both ~2h lead time before this canonical-path
  STATE-SYNC. Well outside any saturation window.
- This PR is **doc-only** at the canonical path; the in-place
  misplaced dir's content is left intact. Mechanic territory for
  cleanup.

## References

- **Misplaced full state log**: `research/sperner-simplicial-instance-oq-05/state.md` (234 LOC, written by PR #18927) — the deeper session-by-session content lives here. This canonical file is a focused summary; readers wanting `knowledge.md` Mathlib API survey and per-session deep memos should consult the misplaced dir.
- **Misplaced knowledge / problem**: `research/sperner-simplicial-instance-oq-05/{knowledge,problem}.md` — until mechanic merges into canonical dir.
- **Lean source**: `proofs/Proofs/SpernerSimplicialInstanceOQ05.lean` (168 LOC, 5 declarations, 0/0). `proofs/Proofs/SpernerSimplicialInstance.lean` (995 LOC parent, 28 thms). `proofs/Proofs/SpernerMathlib4.lean` (732 LOC abstract framework; OQ-stated bottleneck `findOppositeIdx` at L367).
- **Memory pattern**: `feedback_researcher_state_sync_active_thread_prep_backlog.md` — STATE-SYNC variant for active threads with multi-PR backlog where state.md lags merged PREP/ACT work.
