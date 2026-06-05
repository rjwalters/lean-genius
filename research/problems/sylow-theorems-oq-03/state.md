# Current State

**Phase**: ACT-REALIZED (S2 ACT 2026-05-15; S4 ACT 2026-05-16; S6 ACT 2026-06-05 — Candidate B build-verified)
**Since**: 2026-05-12T20:55:00Z
**Last update**: 2026-06-05 (S6 ACT — Candidate B shipped, build-verified 3066 Docker jobs; researcher-1, claim `researcher-90270`)
**Iteration**: 15 (8 PREP + S2 PREP-7 #19297 + S2 ACT #19260 + STATE-SYNC #18994 + S3 STATE-SYNC #19347 + S4 ACT #19380 + S5 STATE-SYNC #22028 + this S6 ACT)

## S6 ACT 2026-06-05 (researcher-1)

**Mode:** S6 ACT — Lean-modifying, ships Candidate B. Build-verified
`./proofs/scripts/docker-build.sh Proofs.SylowTheoremOQ03B` at 3066 jobs
(rebuild attempt 2 after a 1-LOC type fix on `Nat.coprime_pow_primes`).

### What changed (concise)

| File | Δ | Note |
|------|---|------|
| `proofs/Proofs/SylowTheoremOQ03B.lean` | +163 LOC NEW | Discharges OQ-02 axiom `sylowProP_inter_trivial` via the PREP-2 finite-quotient route, using PREP-4/5's `nhds_basis_clopen` / `exist_openNormalSubgroup_sub_open_nhds_of_one` replacement chain + `IsTopologicalGroup` typeclass bridge |
| `proofs/Proofs.lean` | +1 line | `import Proofs.SylowTheoremOQ03B` |
| `research/problems/sylow-theorems-oq-03/state.md` | this header + S6 ACT subsection | Prior STATE-SYNC content preserved verbatim |
| `src/data/research/problems/sylow-theorems-oq-03.json` | iteration 14 → 15 | `currentState.{focus,nextAction,phase,iteration,lastUpdate}` + `knowledge.{builtItems,nextSteps}` |
| `research/problems/sylow-theorems-oq-03/sessions/2026-06-05-s6-act-candidate-b.md` | NEW | This session log + plan + risk register |

### Theorem proved

```
ProfiniteSylow.sylowProP_inter_trivial_via_quotient :
  ∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G],
    ProfiniteSylow.IsProfiniteGroup G →
      ∀ (p q : ℕ) [hp : Fact (Nat.Prime p)] [hq : Fact (Nat.Prime q)],
        p ≠ q →
          ∀ (P : ProfiniteSylow.SylowProP G p) (Q : ProfiniteSylow.SylowProP G q),
            P.toSubgroup ⊓ Q.toSubgroup = ⊥
```

This signature matches the OQ-02 axiom `sylowProP_inter_trivial` at
`SylowTheoremOQ02.lean:133` exactly (modulo `[Fact (Nat.Prime _)]` vs
`(hp : Fact p.Prime)` notation, which is definitionally identical).

### Build risks realized vs predicted

PREP planning identified 4 build risks. Outcome:

| # | Predicted | Outcome |
|---|-----------|---------|
| 1 | Power coercion may need explicit `SubgroupClass.coe_pow` | **OK**: `simpa using congrArg Subtype.val ha` worked |
| 2 | `hp.out.prime` vs `hp.out` for primality coercion | **REALIZED**: First build failed; `Nat.coprime_pow_primes` wants `Nat.Prime p` (not `Prime p`) because the `Nat` namespace shadows `_root_.Prime`. Fixed by dropping `.prime`. 1-LOC delta. |
| 3 | `IsTopologicalGroup G := {}` anonymous-constructor synthesis | **OK**: Worked as-is |
| 4 | `OpenNormalSubgroup.toOpenSubgroup.toSubgroup` 2-coercion path | **OK**: Worked as-is |

Net: 1 build iteration + 1 minor type fix. Total Docker time ~50 min
(~25 min per iteration, both fresh-clone builds).

### Net axiom impact (this PR)

OQ-02 axiom count: **4 → 4 (unchanged in this PR)**. The OQ-02 axiom
`sylowProP_inter_trivial` at L133 remains, alongside the now-proved
theorem `sylowProP_inter_trivial_via_quotient` in OQ-03B. **Realizing
the 4 → 3 drop is a clean follow-on PR** (the OQ-02 axiom can be
deleted, mirroring the A* → S4 split where S2 ACT shipped A* in OQ-03
and S4 ACT removed the axiom 1 day later).

### Revised Current Focus / Next Action

- **§7a (NEW TOP)** — Realize the deferred OQ-02 axiom drop 4 → 3:
  delete `axiom sylowProP_inter_trivial` at `SylowTheoremOQ02.lean:133`
  + the corresponding `#check @sylowProP_inter_trivial` line at L372.
  Single-file edit, ~6 LOC deletion, 1 Docker iteration (~25 min).
  Update `src/data/proofs/sylow-theorems-oq-02/meta.json`:
  `axiomCount` 4 → 3 + `lineCount` 374 → 368.
- **§7b** — Mathlib upstream contribution (out-of-band; mathlib4 PR).
  Unchanged from §6b.
- **§7c** — `frattini_profinite` axiom restatement (curator/architect
  scope). Unchanged from §6c.
- **§7d (natural stopping point)** — once the §7a follow-on lands,
  OQ-03 reaches its natural stopping point with OQ-02 at 3 axioms
  (the two deep inverse-limit axioms + derivable `frattini`) and
  0 sorries.

## S5 STATE-SYNC 2026-06-01 (researcher-1)

**Mode:** STATE-SYNC — doc-only tick after 16-day elapse since S4 ACT.

**INFRA**: Docker 29.4.1 GREEN; disk 55 Gi GREEN; Mathlib pin `2df2f0150c…` (v4.26.0) stable ~20 days (no lake-manifest changes since 2026-05-12). Per PREP-7 bearer kit + S2 ACT / S3 STATE-SYNC / S4 ACT pin-checks, the 8-bearer table for `SylowTheoremOQ03.lean` carries forward verbatim — no bearer re-walk needed at S5.

**OQ-03 state on disk** (re-confirmed 2026-06-01, no drift since S4): 0 axioms / 0 sorries / 0 structure-encoded hypotheses on the OQ-03 theorem itself; OQ-02 has 4 axioms (`sylowProP_existence` L108, `sylowProP_conjugacy` L119, `frattini_profinite` L126, `sylowProP_inter_trivial` L133) per S4 ACT.

**TOP priority (unchanged)**: §6a Candidate B ACT — discharge `sylowProP_inter_trivial` in a new file `proofs/Proofs/SylowTheoremOQ03B.lean` (~25 LOC) using `nhds_basis_clopen` (PREP-4 Finding I, replacing phantom `closedSubgroup_eq_sInf_open`) + `IsTopologicalGroup` typeclass bridge (PREP-5). Expected medium build risk, 1-3 Docker iterations. Net OQ-02 axiomCount on completion: 4 → 3.

**Why deferred at S5**: S5 is a STATE-SYNC tick (single 15-min claim slot occupied alongside two heavier ACT slugs this session — `ballot-problem-oq-03-oq-01-oq-02` S84 ACT (α') (PR #22026) and `euler-polyhedral-formula-oq-02-oq-01-oq-01` S4 STATE-SYNC (PR #22027)). §6a ACT requires a dedicated session with Lean editing budget for the 25-LOC proof + Docker iterations. Reserved for the next claim cycle.

**§6b / §6c**: unchanged. §6b is Mathlib upstream contribution (mathlib4 PR scope, not this repo). §6c is curator/architect scope (`frattini_profinite` axiom restatement).

**Ship scope**: 2 files — `state.md` (this header refresh; preserves S4 ACT subsection verbatim) + `src/data/research/problems/sylow-theorems-oq-03.json` (iteration 13 → 14, lastUpdate / focus / attemptCounts refresh).

**NO**: Lean edits, sibling slug edits, `leanFiles[]` numeric touches, Mathlib pin walks, §6a ACT execution.



## S4 ACT 2026-05-16 (researcher-3)

**Mode:** S4 ACT — Lean-modifying, bundles gallery-meta + research state sync
(6 files: 2 Lean — 1 axiom-block deletion + 1 docstring-prose correction, 1
gallery meta.json, 2 research files refresh, 1 NEW session note). Realizes
the S3 STATE-SYNC §5a deferred follow-on. Build-verified by
`./proofs/scripts/docker-build.sh Proofs.SylowTheoremOQ03` at 3062 jobs (cache
hit on Mathlib v4.26.0, 7727 files unpacked) — see session note §5 +
`.loom/logs/researcher-3-sylow-s4-build.log`.

### What changed (concise)

| File | Δ | Note |
|------|---|------|
| `proofs/Proofs/SylowTheoremOQ02.lean` | −10 LOC (384 → 374) | Deleted `axiom sylowProP_projects_pgroup` block (132–140) + `#check @sylowProP_projects_pgroup` line |
| `proofs/Proofs/SylowTheoremOQ03.lean` | 0 Lean Δ (docstring prose only) | §"Effect on `SylowTheoremOQ02.lean`" rewritten to match the realized deletion |
| `src/data/proofs/sylow-theorems-oq-02/meta.json` | axiomCount 5→4 + lineCount 393→374 + assumption text + section metadata | See session note §1 table |
| `research/problems/sylow-theorems-oq-03/state.md` | this header + S4 ACT subsection | Prior STATE-SYNC content preserved verbatim |
| `src/data/research/problems/sylow-theorems-oq-03.json` | `currentState` + `knowledge.{builtItems,nextSteps}` | S3 §5a moved from nextSteps → builtItems |
| `research/problems/sylow-theorems-oq-03/sessions/2026-05-16-s4-act-oq02-axiom-drop.md` | NEW | This S4 ACT session note |

### Realized vs deferred ledger (S3 §5 decision tree)

| S3 branch | Description | Status after S4 |
|-----------|-------------|------------------|
| §5a | Realize deferred OQ-02 axiom drop 5→4 | **REALIZED** (this S4 ACT) |
| §5b | Candidate B ACT (`sylowProP_inter_trivial`) | New TOP priority, OPEN |
| §5c | Mathlib upstream contribution | Out-of-band (mathlib4 PR) |
| §5d | `frattini_profinite` axiom restatement | Curator/architect scope; no researcher action |

### Net axiom impact (now realized, per Axiom Integrity policy)

OQ-02 axiom count: **5 → 4** (verified on disk: `grep -cE "^axiom "
proofs/Proofs/SylowTheoremOQ02.lean` returns `4`; remaining axioms are
`sylowProP_existence` L108, `sylowProP_conjugacy` L119, `frattini_profinite`
L126, `sylowProP_inter_trivial` L133).

OQ-03 itself: still 0 axioms / 0 structure-encoded hypotheses / 0 sorries
(unchanged from S2 ACT).

### Mathlib pin recheck (no drift)

`proofs/lake-manifest.json` mathlib `rev` =
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) — same SHA at which
PREP-7 / S2 ACT / S3 STATE-SYNC pinned the bearer kit. PREP-7's 8-bearer
table remains authoritative for `SylowTheoremOQ03.lean`; S4 ACT does not
touch that file's theorem body.

### Caller audit (sanity-check on deletion)

Pre-S4 `proofs/Proofs/` had `sylowProP_projects_pgroup` at:

1. `SylowTheoremOQ02.lean:134` — the `axiom` (DELETED)
2. `SylowTheoremOQ02.lean:380` — `#check @sylowProP_projects_pgroup` (DELETED)
3. `SylowTheoremOQ03.lean` lines 13/17/58/62/123 — docstring prose (line 58
   rewritten; others unchanged)
4. `SylowTheoremOQ03.lean:135,162` — distinct-name
   `sylowProP_projects_pgroup_continuous` (UNCHANGED)

No theorem / definition / tactic / import in `proofs/Proofs/` referenced
the deleted axiom by name. Deletion is purely additive to the
axiom-integrity ledger.

### Build verification

`./proofs/scripts/docker-build.sh Proofs.SylowTheoremOQ03` →
`Build completed successfully (3062 jobs)` (cache hit; 7727 Mathlib files
unpacked; ~3.5 min wall). Two pre-existing warnings in
`SylowTheoremOQ03.lean` (auto-included section variable unused at L96; one
unused `simp` argument at L144) — both predate this PR (they shipped with
S2 ACT #19260) and are unaffected by S4 ACT. No build errors, no new
warnings introduced.

### Revised Current Focus / Next Action / Subsequent candidates

- **§6a (new TOP)** — Candidate B ACT (`sylowProP_inter_trivial`), ~25 LOC,
  medium build risk (PREP-2 / PREP-4 / PREP-5 bearer kit:
  `nhds_basis_clopen` + `IsTopologicalGroup` typeclass bridge). Net OQ-02
  axiom count 4 → 3.
- **§6b** — Mathlib upstream contribution (out-of-band; mathlib4 PR).
- **§6c** — `frattini_profinite` axiom restatement (curator/architect scope).
- **§6d** — Stop. Once Candidate B lands (or is declared out-of-researcher-scope),
  OQ-03 reaches a natural stopping point with OQ-02 at 3 axioms (the two
  deep inverse-limit axioms + derivable `frattini`) and 0 sorries.

## S3 STATE-SYNC 2026-05-16 (researcher-12)

**Mode:** STATE-SYNC (doc-only, 3 files: this `state.md` header + body
addition, JSON `currentState` + `knowledge.{builtItems,nextSteps}`
update, new session note `2026-05-16-s3-state-sync-post-act.md`).
Triggered because the prior STATE-SYNC (PR #18994 by researcher-4)
merged 2026-05-15T23:29:25Z but its body was authored *before* the
build-verified S2 ACT (PR #19260, merged 2026-05-15T18:02:55Z).
Result: on-disk `state.md` and JSON show `Phase: PREP` and
`nextAction = "S2 ACT — Candidate A*"` even though
`proofs/Proofs/SylowTheoremOQ03.lean` (162 LOC, 0 sorries / 0 axioms)
landed in `origin/main` ~6 h prior to this S3.

### Cascade ledger (S2 PREP-6 close → S3 open)

| # | PR | Phase | Merged (UTC) | Δ |
|---|----|-------|--------------|----|
| 9 | #19260 | **S2 ACT — Candidate A\*** | 2026-05-15T18:02:55Z | +162 / −12 Lean (3062 jobs ✓); +1 session note |
| 10 | #19297 | S2 PREP-7 (meta-audit) | 2026-05-15T18:00:51Z | +1 session note (8 bearers pin-verified at `2df2f015`) |
| 11 | #18994 | STATE-SYNC (S2 PREP-6 catch-up) | 2026-05-15T23:29:25Z | state.md + JSON + 1 session note (content predates ACT) |
| 12 | this PR | S3 STATE-SYNC (post-ACT catch-up) | (pending) | state.md + JSON + 1 session note |

### Mathlib pin recheck (no drift)

`proofs/lake-manifest.json` mathlib `rev` =
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) — **same SHA** at
which PREP-7 verified all 8 bearers used in `SylowTheoremOQ03.lean`.
PREP-7's bearer table (B1–B8) remains authoritative; see this PR's
session note § 3 for the bearer table reproduced for convenience.

### Axiom Integrity recheck (per CLAUDE.md policy)

`proofs/Proofs/SylowTheoremOQ03.lean`:

```text
$ grep -cE "^axiom " proofs/Proofs/SylowTheoremOQ03.lean
0
$ grep -E "^structure |^class " proofs/Proofs/SylowTheoremOQ03.lean
(no matches)
```

**OQ-03 contributes 0 axioms / 0 structure-encoded hypotheses /
0 sorries** to the gallery. Inherits OQ-02's 5 axioms (`existence`,
`conjugacy`, `frattini_profinite`, `projects_pgroup`, `inter_trivial`).

OQ-02 axiom inventory at current `origin/main` (verified unchanged by
S2 ACT — the merged ACT keeps OQ-02's `axiom
sylowProP_projects_pgroup` at L134 as a backward-compat thin wrapper,
see this PR's session note § 4 + the merged S2 ACT session note
§ 2.2):

```text
108:axiom sylowProP_existence
119:axiom sylowProP_conjugacy
126:axiom frattini_profinite
134:axiom sylowProP_projects_pgroup
142:axiom sylowProP_inter_trivial
```

The advertised `5 → 4` net axiom impact remains a *deferred* outcome,
not a *realized* one. To realize it: see § 5a of this PR's session
note (mechanic-grade follow-on PR, ~5 LOC, 1 Docker iteration).

### Drift recheck (PR #19260 base SHA → current `origin/main`)

0 substantive drift on Lean (`SylowTheoremOQ03.lean`,
`SylowTheoremOQ02.lean`, `Proofs.lean`) or `problem.md` /
`knowledge.md` body since S2 ACT merge. `state.md` + JSON were the
only files needing refresh.

### Net axiom impact (revised, post-S2 ACT)

OQ-02 axiom count: **5 → 5 (unchanged)**. The continuity-enhanced
*theorem* `ProfiniteSylow.sylowProP_projects_pgroup_continuous` lives
in `proofs/Proofs/SylowTheoremOQ03.lean` *alongside* (not replacing)
the OQ-02 axiom. Realizing the `5 → 4` drop is a clean follow-on PR
(see this PR's session note § 5a).

### Revised Current Focus / Next Action / Subsequent candidates

(See § 5 of this PR's session note for the full decision tree;
summary header lines below are reflected in the JSON
`currentState.{focus,nextAction}` updates.)

- **5a. Realize the deferred OQ-02 axiom drop (5 → 4)** — TOP
  priority, mechanic-grade ~5 LOC, 1 Docker iteration.
- **5b. Candidate B ACT (`sylowProP_inter_trivial`)** — secondary,
  ~25 LOC, medium-risk per PREP-2/4/5.
- **5c. Mathlib upstream contribution** — out-of-band (Mathlib4 PR,
  not lean-genius).
- **5d. `frattini_profinite` axiom restatement** — curator/architect
  scope per PREP-3 audit; researcher: no action.

## STATE-SYNC 2026-05-14 (researcher-4)

**Mode**: STATE-SYNC (doc-only). Between 2026-05-12T22:16Z (PR #18285,
S1 OBSERVE) and 2026-05-13T10:16Z (PR #18735, S2 PREP-6), **8 PRs**
merged for this slug but `state.md` was never updated past S1.
JSON `currentState.phase = "OBSERVE"` likewise lagged. This STATE-SYNC
bookends the PREP chain and pins the S2 ACT target for the picker.

### Merged-PR ledger (S1 through S2 PREP-6)

| # | PR | Phase | Date | Author | Key finding |
|---|----|-------|------|--------|-------------|
| 1 | #18285 | S1 OBSERVE | 2026-05-12 | researcher-1 | OQ-03 is a near-duplicate of completed OQ-02. Lists 3 candidates A/B/C with concrete signatures. |
| 2 | #18359 | S1b OBSERVE | 2026-05-12 | researcher-? | Audit correction — Candidate C (`normal_of_unique` sorry) is **moot** (already covered by OQ-02's recovery chain). Recommends "**Candidate A\***" — A with continuity-enhanced signature instead of bare `Fintype`. |
| 3 | #18453 | S2 PREP | 2026-05-13 | researcher-? | Candidate A\* decomposed into 5 substeps. Five Mathlib bearer names flagged "likely" pending verification at S2 ACT. |
| 4 | #18493 | S2 PREP-2 | 2026-05-13 | researcher-? | Candidate B (`sylowProP_inter_trivial`) decomposed into 5 substeps. TDS-flag (totally-disconnected) correction. |
| 5 | #18546 | S2 PREP-3 | 2026-05-13 | researcher-? | **`frattini_profinite` axiom is degenerate as stated** (+339 LOC audit). Discharges as a 1-line corollary — but the axiom may need restatement before ACT to be non-trivial. |
| 6 | #18658 | S2 PREP-4 | 2026-05-13 | researcher-? | Mathlib bearer audit for Candidate B: **PHANTOM** `closedSubgroup_eq_sInf_open` (not in Mathlib v4.26.0). Re-routes via `nhds_basis_clopen` + 6 minor findings. |
| 7 | #18722 | S2 PREP-5 | 2026-05-13 | researcher-? | `IsTopologicalGroup` typeclass-instance bridge for Candidate B5 + closure of PREP-4 §11 deferred API audit. |
| 8 | #18735 | S2 PREP-6 | 2026-05-13 | researcher-8 | **Candidate A\* Mathlib bearer audit**. Verifies the 5 PREP-1 "likely" names. **MAJOR WIN: `Subgroup.index_ker` at `Mathlib/GroupTheory/Index.lean:322`** collapses Substep 5's 3-lemma cardinality bridge to a single `rfl`-adjacent rewrite. Namespace corrections: `QuotientGroup.quotientKerEquivRange` (not `MulEquiv.*`), `IsPGroup.of_card` in `PGroup.lean` (not `Sylow.lean`), `Subgroup.index_eq_card` (not `..._quotient`). Net A* LOC budget **60 → ~50**, "medium build risk" → "negligible". |

### Candidate scope at end of PREP chain

| Candidate | Target axiom/sorry | Status | LOC | Build risk | Recommendation |
|-----------|-------------------|--------|-----|-----------|----------------|
| **A\*** | `sylowProP_projects_pgroup` (axiom L134 of `SylowTheoremOQ02.lean`) | **PREP complete, ACT-ready** | ~50 (down from PREP-1's ~60 via PREP-6 Finding I) | negligible | **Ship next** — all bearers verified, namespace paths corrected, cardinality bridge collapsed. |
| B | `sylowProP_inter_trivial` (axiom L142) | PREP complete | ~25 | medium (deferred to ACT post-PREP-5 typeclass bridge) | Deferrable — conditional on Candidate A\* not regressing the `IsTopologicalGroup` instance. |
| frattini | `frattini_profinite` (axiom) | PREP-3 audit: **degenerate as stated** | — | — | **Out of scope** — discharges trivially; suggests axiom restatement is a curator/architect concern, not researcher. |
| C | `sylowProP_normal_of_unique` (sorry L285) | S1b: **moot** | — | — | **Out of scope** — already covered by OQ-02's recovery chain per S1b correction. |

### S2 ACT Candidate A\* — Lean signature lock-in

Concrete target (per PREP-1 + PREP-6 corrections):

```lean
-- New file: proofs/Proofs/SylowTheoremOQ03.lean (~50 LOC)
theorem sylowProP_projects_pgroup
    {G : Type*} [Group G] [TopologicalSpace G]
    {p : ℕ} [Fact (Nat.Prime p)] (P : SylowProP p G)
    {H : Type*} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Fintype H] (φ : G →* H) (hφ : Continuous φ) :
    IsPGroup p (φ.range) := by
  -- 5 substeps per PREP-1 §3 + PREP-6 §2 simplification
  sorry  -- targets discharged at ACT
```

(Replaces OQ-02's `axiom sylowProP_projects_pgroup` at
`proofs/Proofs/SylowTheoremOQ02.lean:134` — `+0/–3 LOC` in OQ-02.)

### Net axiom impact

After S2 ACT (Candidate A\*) lands: OQ-02 axiom count **5 → 4**, no
change to gallery status or main theorem signatures. The remaining 4
OQ-02 axioms (`sylowProP_existence`, `sylowProP_conjugacy`,
`sylowProP_inter_trivial`, `frattini_profinite`) split into deep
(2 — out of OQ-03 scope) + adjacent (1 = Candidate B, deferrable)
+ degenerate (1 = `frattini_profinite`, curator/architect concern
per PREP-3 audit).

## Current Focus

S1 OBSERVE — duplicate detection against completed sibling
`sylow-theorems-oq-02` + audit of OQ-02's actual gaps (5 axioms + 1
sorry in `proofs/Proofs/SylowTheoremOQ02.lean`, 393 lines) + three
narrow adjacent S2 candidates.

## Active Approach

**Doc-only S1 OBSERVE.** No Lean changes. Deliverable is three
markdown files + one JSON gallery entry:

- `problem.md` — duplicate-detection note, OQ-02 audit table, three
  narrow S2 candidates (A: project_pgroup axiom; B: inter_trivial
  axiom; C: normal_of_unique sorry) with concrete Lean signatures.
- `knowledge.md` — § 1 duplicate detection, § 2 OQ-02 audit (5
  axioms + 1 sorry classified), § 3-5 detailed proof sketches for
  Candidates A/B/C with Lean skeletons, § 6 recommended S2 scope,
  § 8 risk register, § 10 cost estimate.
- `state.md` (this file).
- `src/data/research/problems/sylow-theorems-oq-03.json` — gallery
  entry, status `in-progress`, knowledge payload.

## S1 Summary

### Duplicate detection

`sylow-theorems-oq-03` ("pro-p Sylow recovered as inverse limit") is
a near-duplicate of completed `sylow-theorems-oq-02` ("Pro-p Sylow
Theory for Profinite Groups"). Memory pattern (researcher-12 PR
#18235, 2026-05-12): for duplicate Millennium / Hilbert / completed-
sibling slugs, S1 OBSERVE = duplicate-detection + parent audit +
shortlist 2-3 narrow adjacent S2 targets.

### Three S2 candidates locked

| ID | Target item | Type | Effort  | Notes |
|----|-------------|------|---------|-------|
| A  | `sylowProP_projects_pgroup` | axiom (line 134) | ~50 LOC | Most clearly dischargable; uses existing `proP_subgroup_card_ppow` (line 332) |
| B  | `sylowProP_inter_trivial`   | axiom (line 142) | ~25 LOC | Requires `IsProfiniteGroup` to expose totally-disconnected; **conditional** |
| C  | `sylowProP_normal_of_unique` | sorry (line 285) | ~40 LOC | Uses `isProP_conj_map` (line 226); rebundling care needed |

### Recommended S2 ACT (Candidate A)

Ship `proofs/Proofs/SylowTheoremOQ03.lean` (~50 LOC) discharging
`sylowProP_projects_pgroup` using `proP_subgroup_card_ppow`. Update
OQ-02's file by replacing the axiom with the new theorem.

Net: **OQ-02 axiom count 5 → 4** with no change to its gallery
status (`completed`) or main theorem signatures.

### Out of scope

The two **deep** axioms (`sylowProP_existence`,
`sylowProP_conjugacy`) require the full inverse-limit construction
and remain out of OQ-03 scope; they are OQ-02's own long-term
`nextSteps`.

## Blockers

None mathematical. Candidate B is **conditional** on
`IsProfiniteGroup`'s API exposing totally-disconnected — if it does
not, B requires a small augmentation that can either piggyback on B
or be split out.

**Operational:** worktree `proofs/.lake` is recursive
(`feedback_researcher_lake_symlink_broken.md`); local docker build
~25–45 min. S1 OBSERVE doc-only — no build needed.

## Next Action

**S2 ACT (Candidate A\*) — any researcher.** Create
`proofs/Proofs/SylowTheoremOQ03.lean` (~50 LOC, **down from PREP-1's
~60** via PREP-6 Finding I's `Subgroup.index_ker` collapse) with
`sylowProP_projects_pgroup` discharged at the continuity-enhanced
signature locked in the STATE-SYNC section above. Use:

- PREP-1 (#18453) §3 — 5-substep decomposition
- PREP-6 (#18735) §2 — `Subgroup.index_ker` cardinality bridge
  (collapses Substep 5 from 3 lemmas / "medium risk" to 1 `rw`)
- PREP-6 (#18735) §3 — namespace corrections
  (`QuotientGroup.quotientKerEquivRange`, `IsPGroup.of_card` in
  `PGroup.lean`, `Subgroup.index_eq_card`)

Bundle the OQ-02 axiom replacement (`+0/–3 LOC`) into the same PR.
OQ-02 axiom count after merge: **5 → 4**.

Carries the established "build pending" convention while the
`proofs/.lake` recursive-symlink issue (PREP-1 § "Operational
notes") gates the Docker build chain.

### Subsequent candidates (post-A\* ACT, in priority order)

1. **Candidate B ACT** (~25 LOC, conditional). Apply PREP-2 / PREP-4 /
   PREP-5's findings — `nhds_basis_clopen` (replacing phantom
   `closedSubgroup_eq_sInf_open`) + `IsTopologicalGroup` instance
   bridge. Deferrable until A\* lands cleanly.
2. **frattini_profinite restatement** (curator/architect, not
   researcher). PREP-3 audit found the axiom degenerate as stated;
   restate or remove as an axiom-cleanup PR.
3. **Candidate C** (~40 LOC). PREP-1 nominated, but S1b correction
   marked **moot** — already covered by OQ-02's recovery chain. No
   action needed.

## Attempt Counts

- Total attempts: 8 (S1, S1b, S2 PREP, S2 PREP-2, S2 PREP-3, S2
  PREP-4, S2 PREP-5, S2 PREP-6)
- Current approach attempts: 7 (S2 PREP chain — all doc-only)
- Approaches tried: 1 (duplicate-detection + Candidate A* +
  exhaustive Mathlib bearer audit; Candidate A* unblocked for ACT)

## Open files

- `problem.md` — OQ-02 audit + S2 candidate signatures (this PR).
- `knowledge.md` — detailed candidate proof sketches (this PR).
- `state.md` (this file).
- (downstream) `proofs/Proofs/SylowTheoremOQ02.lean` — audit target;
  **not touched** in S1.

## Race awareness

OQ-03 has zero open PRs and zero recent merges at push time
(verified 2026-05-12 ~20:55 UTC via `gh pr list --search "sylow-
theorems-oq-03 in:title"`). Sister slugs (oq-01, oq-02, oq-04,
oq-05) target different aspects; no concurrent S1 OBSERVE risk.
The completed parent `oq-02` is in `completed` state — no concurrent
research activity expected.
