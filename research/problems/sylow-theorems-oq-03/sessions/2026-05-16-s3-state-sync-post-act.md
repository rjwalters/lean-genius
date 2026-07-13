# 2026-05-16 — S3 STATE-SYNC: post-S2-ACT catch-up + Mathlib pin recheck

**Author:** researcher-12
**Phase:** S3 STATE-SYNC (doc-only)
**Iteration:** 12 (8 PREP + S2 PREP-7 + S2 ACT + STATE-SYNC + this)
**Trigger:** `state.md` and `src/data/research/problems/sylow-theorems-oq-03.json`
both reflect a snapshot frozen at the close of the S2 PREP-6 chain
(researcher-4's STATE-SYNC, PR #18994 content). PR #18994 itself merged
2026-05-15T23:29:25Z but its body was authored before the build-verified
S2 ACT (PR #19260, merged 2026-05-15T18:02:55Z) shipped. The S2 ACT
session note (`2026-05-15-s2-act-candidate-a-star-projects-pgroup.md` § 2)
expressly defers `state.md`/JSON updates: *"STATE-SYNC PR #18994 owns
those updates; bumping iter from 8 → 9 will land separately once #18994
merges."* Now that #18994 has merged with content predating the ACT, the
ACT itself remains unrepresented in `state.md` / JSON. This S3
STATE-SYNC closes that gap.

**Strict conflict-free:** new session file + `state.md` § rewrite +
JSON `currentState` + `knowledge.{builtItems,nextSteps}` updates. No
edits to `problem.md`, `knowledge.md` body, or any Lean / parent file.

---

## § 1 — Cascade timeline (S1 OBSERVE → S3 STATE-SYNC)

| # | PR | Phase | Merged (UTC) | Author | Lean Δ | Doc Δ | Build verified |
|---|----|-------|--------------|--------|--------|-------|----------------|
| 1 | #18285 | S1 OBSERVE | 2026-05-12T22:16:42Z | researcher-1 | — | +problem/knowledge/state | — |
| 2 | #18359 | S1b OBSERVE | 2026-05-12T23:17:17Z | (researcher-?) | — | doc-only correction | — |
| 3 | #18453 | S2 PREP | 2026-05-13T00:51Z | (researcher-?) | — | A* substep decomposition | — |
| 4 | #18493 | S2 PREP-2 | 2026-05-13T03:07:10Z | (researcher-?) | — | B substep decomposition + TDS-flag | — |
| 5 | #18546 | S2 PREP-3 | 2026-05-13T04:39Z | (researcher-?) | — | `frattini_profinite` degeneracy audit | — |
| 6 | #18658 | S2 PREP-4 | 2026-05-13T08:43Z | (researcher-?) | — | bearer audit B (phantom `closedSubgroup_eq_sInf_open`) | — |
| 7 | #18722 | S2 PREP-5 | 2026-05-13T09:46Z | (researcher-?) | — | `IsTopologicalGroup` typeclass bridge | — |
| 8 | #18735 | S2 PREP-6 | 2026-05-13T10:16Z | researcher-8 | — | bearer audit A* — `Subgroup.index_ker` collapses substep 5 | — |
| 9 | **#19260** | **S2 ACT** | **2026-05-15T18:02:55Z** | **researcher-9** | **+162 / −12** (`SylowTheoremOQ03.lean` NEW; `SylowTheoremOQ02.lean` 3-cluster mechanic fix; `Proofs.lean` 1-line import) | +1 session | **✓ 3062 jobs** |
| 10 | #19297 | S2 PREP-7 | 2026-05-15T18:00:51Z | researcher-9 | — | meta-audit of #18994 + #19260; pin-verifies 8 bearers at `2df2f015` | — |
| 11 | #18994 | STATE-SYNC | 2026-05-15T23:29:25Z | researcher-4 (rjwalters in body) | — | catches `state.md` + JSON up to S2 PREP-6 (content predates ACT) | — |
| 12 | **this PR** | **S3 STATE-SYNC** | (pending) | researcher-12 | — | catches `state.md` + JSON to post-S2-ACT/post-PREP-7/post-#18994 state | — |

**Build verification anchor.** PR #19260 was the *only* Lean-modifying
commit in the chain. Build attempt #1 surfaced 6 OQ-02 errors at v4.26.0
(none in OQ-03 itself); the 3-cluster mechanic fix bundled into #19260's
body lands the ACT clean at 3062 Docker jobs (per the merged session
note's § 0).

## § 2 — What `state.md` / JSON were claiming pre-S3 vs reality

| Field | Pre-S3 claim (post-#18994 disk content) | Reality (post-#19260) |
|-------|----------------------------------------|------------------------|
| `phase` | `PREP` ("S2 PREP chain complete; S2 ACT for Candidate A* nominated") | `ACT-MERGED` (S2 ACT shipped + build-verified) |
| `iteration` | 8 | 11 (8 PREP + S2 PREP-7 + S2 ACT + STATE-SYNC) |
| `since` | 2026-05-12T20:55:00Z (S1 OBSERVE start) | unchanged (slug origin) |
| `lastUpdate` (state.md prose) | "2026-05-14 (STATE-SYNC by researcher-4)" | 2026-05-16 (this S3) |
| `nextAction` | "S2 ACT — Candidate A*: ship `SylowTheoremOQ03.lean`…" | post-S2-ACT options (see § 5) |
| `leanFiles` (JSON) | `[]` | `["proofs/Proofs/SylowTheoremOQ03.lean"]` |
| `builtItems` (JSON `knowledge`) | doc-only entries (problem/knowledge/state) | + `proofs/Proofs/SylowTheoremOQ03.lean` (1 def + 4 theorems, 0 sorries / 0 axioms) |
| `nextSteps[0]` (JSON `knowledge`) | "S2 ACT — Candidate A: discharge sylowProP_projects_pgroup. Drops OQ-02 axiom 5 → 4." | **(amend)** S2 ACT shipped; OQ-02 axiom **unchanged at 5** because the merged ACT introduces a continuity-enhanced replacement in OQ-03 *without* deleting the OQ-02 axiom (per `2026-05-15-s2-act-candidate-a-star-projects-pgroup.md` § 2.2). The `5 → 4` drop remains a future iteration. |

## § 3 — Mathlib pin recheck (no drift since PREP-7's audit)

`proofs/lake-manifest.json` mathlib `rev`:

```
2df2f0150c275ad53cb3c90f7c98ec15a56a1a67   (inputRev: v4.26.0)
```

This is the same SHA at which PR #19297 (S2 PREP-7 meta-audit) verified
all 8 bearers used in the S2 ACT file. **No drift.** PREP-7's bearer
verification table (B1–B8) remains authoritative for `SylowTheoremOQ03.lean`.

| # | Bearer | File @ SHA | Line | Used in OQ-03 file at |
|---|--------|------------|------|------------------------|
| B1 | `Subgroup.index_ker` | `Mathlib/GroupTheory/Index.lean` | 322 | docstring L66, body L143–147 |
| B2 | `IsPGroup.of_card` | `Mathlib/GroupTheory/PGroup.lean` | 40 | docstring L68, body L152 |
| B3 | `MonoidHom.normal_ker` | `Mathlib/Algebra/Group/Subgroup/Ker.lean` | 314 | docstring L70, body L119 |
| B4 | `isOpen_discrete` | `Mathlib/Topology/Order.lean` | 255 | docstring L72, body L110 |
| B5 | `continuous_subtype_val` | `Mathlib/Topology/Constructions.lean` | 367 | body L96, L111 |
| B6 | `Subgroup.mem_map` | `Mathlib/Algebra/Group/Subgroup/Map.lean` | 128 | body L141 (implicit via `simp`) |
| B7 | `MonoidHom.mem_range` | `Mathlib/Algebra/Group/Subgroup/Ker.lean` | 73 | body L141 (implicit via `simp`) |
| B8 | `Subgroup.coe_subtype` | `Mathlib/Algebra/Group/Subgroup/Defs.lean` | 579 | body L142 (implicit via `simp`) |

**S2 ACT body LOC counts** (against on-disk `proofs/Proofs/SylowTheoremOQ03.lean`):

| Span | Lines | Content |
|------|-------|---------|
| L1–11 | 11 | 9 Mathlib imports + `Proofs.SylowTheoremOQ02` import |
| L12–74 | 63 | Module docstring (mathematical content, proof outline, OQ-02 effect, references) |
| L76–86 | 11 | `namespace ProfiniteSylow` + `set_option linter.unusedVariables false` + 5 `variable` lines |
| L88–91 | 4 | `def restrictToSylowProP` |
| L93–96 | 4 | `theorem continuous_restrictToSylowProP` |
| L98–111 | 14 | `theorem isOpen_ker_restrictToSylowProP` |
| L113–120 | 8 | `theorem exists_pow_index_ker_restrictToSylowProP` |
| L122–152 | 31 | `theorem sylowProP_projects_pgroup_continuous` (the **headline result**) |
| L154–161 | 8 | `end` × 2 + 4 `#check` lines |
| **Total** | **162** | 1 def + 4 theorems + 0 sorries + 0 axioms |

## § 4 — Axiom Integrity check (per CLAUDE.md policy)

```text
$ grep -cE "^axiom " proofs/Proofs/SylowTheoremOQ03.lean
0
$ grep -E "^structure |^class " proofs/Proofs/SylowTheoremOQ03.lean
(no matches)
```

**OQ-03 itself contributes 0 axioms / 0 structure-encoded hypotheses /
0 sorries** to the gallery. The dependency chain (`import
Proofs.SylowTheoremOQ02`) inherits OQ-02's 5 axioms (which OQ-03 was
*designed not to delete* — see § 5).

OQ-02 axiom inventory at current `origin/main` (unchanged by S2 ACT):

```text
$ grep -nE "^axiom " proofs/Proofs/SylowTheoremOQ02.lean
108:axiom sylowProP_existence
119:axiom sylowProP_conjugacy
126:axiom frattini_profinite
134:axiom sylowProP_projects_pgroup
142:axiom sylowProP_inter_trivial
```

OQ-02's `axiom sylowProP_projects_pgroup` at L134 is **untouched** by S2
ACT. The continuity-enhanced *theorem*
`ProfiniteSylow.sylowProP_projects_pgroup_continuous` lives in OQ-03
alongside (not replacing) the OQ-02 axiom — this is intentional
backward-compat; see the merged S2 ACT session note § 2.2.

**Reading for the picker.** The advertised `5 → 4` net axiom impact in
the pre-S3 `state.md` § "Net axiom impact" and JSON `knowledge.goal`
remains a *deferred* outcome, not a *realized* one. To realize it, a
follow-up Lean-modifying PR would (a) delete `axiom
sylowProP_projects_pgroup` from `SylowTheoremOQ02.lean:134`, (b)
re-route any callers (currently none in the gallery, per the OQ-03 file
docstring L60–62), and (c) update OQ-02's gallery JSON
(`src/data/proofs/sylow-theorems-oq-02/meta.json` `axiomCount` 5 → 4).

## § 5 — Next-action decision tree (post-S2 ACT)

Three orthogonal next-action branches in priority order:

### 5a. Realize the deferred OQ-02 axiom drop (`5 → 4`)

**Scope.** Lean-modifying mechanic-grade PR:
- Delete L134 `axiom sylowProP_projects_pgroup …` from `SylowTheoremOQ02.lean`
- Optional: rename / re-export `ProfiniteSylow.sylowProP_projects_pgroup_continuous`
  as `ProfiniteSylow.sylowProP_projects_pgroup` for callers (currently
  none in gallery; `grep -rn "sylowProP_projects_pgroup" proofs/Proofs/
  --include='*.lean'` confirms only OQ-02's axiom + OQ-03's continuity
  theorem)
- Update `src/data/proofs/sylow-theorems-oq-02/meta.json` `axiomCount` 5 → 4

**Risk.** Negligible (OQ-03 already builds clean at 3062 jobs;
deletion is a removal, not an addition; no callers anywhere in the
gallery). **Build budget:** 1 Docker iteration.

**Why deferred at S2 ACT.** Per the merged session note's § 2.2 +
§ 5.5, the author chose backward-compat over net axiom drop to keep the
ACT scope small and avoid coupling to OQ-02's call sites. The drop is
now a clean follow-on.

### 5b. Candidate B ACT (`sylowProP_inter_trivial`)

**Scope.** New file `proofs/Proofs/SylowTheoremOQ03B.lean` (~25 LOC)
following PREP-2 / PREP-4 / PREP-5 findings. Bearer kit:
- `nhds_basis_clopen` (replaces phantom `closedSubgroup_eq_sInf_open` per
  PREP-4 Finding I)
- `IsTopologicalGroup` typeclass bridge per PREP-5 (verifies
  `B5: IsTopologicalGroup G → IsTopologicalGroup P.toSubgroup`)

**Risk.** Medium — PREP-2 estimated "medium build risk" pending
PREP-5's typeclass bridge resolution. PREP-5's bridge is now in the
record but un-tested at v4.26.0 in a Lean file. **Build budget:** 1–3
Docker iterations.

**Net.** OQ-02 axiom count 5 → 4 (or 5 → 3 if 5a also lands first).

### 5c. Mathlib upstream contribution (`sylowProP_projects_pgroup_continuous`)

**Scope.** Push the continuity-enhanced theorem upstream as
`Mathlib.GroupTheory.Sylow.image_isPGroup_of_continuous` (or a
similarly-named bearer). The proof uses only Mathlib lemmas (per § 3's
B1–B8 table) + the **local** `IsProP` typeclass. Upstream-fitness
requires either (i) generalizing the statement to drop `IsProP`
(plausible — the cardinality argument only needs that `P` has
p-power-index open subgroups), or (ii) Mathlib accepting a profinite-
specific instance.

**Risk.** Out of scope for OQ-03 directly — Mathlib contribution would
land as a `mathlib4` PR, not a `lean-genius` PR. Documented here for
completeness; route via Mathlib Zulip if pursued.

### 5d. `frattini_profinite` axiom restatement

**Status.** PREP-3 (`#18546`) flagged this axiom as **degenerate as
stated** — discharges in 1 line as a corollary, but the axiom may need
restatement to be non-trivial. Per PREP-3's recommendation, this is a
**curator/architect concern, not researcher**. No action here.

## § 6 — Drift recheck (PR #19260's base SHA → current `origin/main`)

PR #19260 was created against `origin/main` at SHA
`d35a6f0f2ac` (per § 1's pre-#19260 main commit). Current
`origin/main` at S3 STATE-SYNC open: `032929ba76c`. Window: ~52
intermediate merges (per `git log --oneline d35a6f0f2ac..origin/main |
wc -l` ≈ 52 from sampling — see deployer drain wave 22:55:21Z–22:56:14Z
for the bulk).

**Drift on slug-touched files** (`proofs/Proofs/SylowTheoremOQ03.lean`,
`proofs/Proofs/SylowTheoremOQ02.lean`, `proofs/Proofs.lean`,
`research/problems/sylow-theorems-oq-03/{state,problem,knowledge}.md`,
`src/data/research/problems/sylow-theorems-oq-03.json`):

| File | Commits since ACT base | Latest commit | Substantive drift on slug-relevant content? |
|------|------------------------|----------------|-----------------------------------------------|
| `proofs/Proofs/SylowTheoremOQ03.lean` | 1 (#19274 unrelated `--diff-filter=A` ghost — Git's rename detection across the merge commit) | `97e6765b648` | **0** |
| `proofs/Proofs/SylowTheoremOQ02.lean` | 0 since ACT (#19260's own changes) | (ACT) | **0** |
| `proofs/Proofs.lean` | (typically updated by other slugs adding imports) | varies | **0 on the OQ-03 import line** |
| `research/problems/sylow-theorems-oq-03/state.md` | 1 (#18994) | `b95a6428e96` | content snapshot is pre-ACT (this S3 closes that) |
| `src/data/research/problems/sylow-theorems-oq-03.json` | 1 (#18994) | `b95a6428e96` | same |
| `research/problems/sylow-theorems-oq-03/{problem,knowledge}.md` | 0 since #18285 (S1 OBSERVE) | `3d045af8571` | **0** — these stay frozen (no S3 edits) |

**Net:** 0 substantive drift on Lean / parent / Mathlib surface.
`state.md` + JSON are the only files that need a refresh.

## § 7 — Conflict-free guarantees

This S3 STATE-SYNC PR touches **3 files**:

1. `research/problems/sylow-theorems-oq-03/state.md` — append S3 STATE-SYNC
   section + update Phase / Iteration / Last-update / Current Focus / Next
   Action header lines. Preserves all prior STATE-SYNC content verbatim
   (researcher-4's S2 PREP-6 catch-up section is appended-to, not
   replaced).
2. `src/data/research/problems/sylow-theorems-oq-03.json` — update
   `currentState.{phase, iteration, focus, lastUpdate, nextAction,
   blockers, attemptCounts}` and `currentState.leanFiles`; update
   `knowledge.{builtItems, nextSteps}` to reflect the post-ACT reality.
   `knowledge.{progressSummary, insights, mathlibGaps,
   historicalContext}` and the top-level `problemStatement` /
   `knownResults` blocks are preserved verbatim.
3. `research/problems/sylow-theorems-oq-03/sessions/2026-05-16-s3-state-sync-post-act.md`
   — this file (NEW).

**Not touched by this PR:**
- `problem.md`, `knowledge.md` body — the existing prose remains
  accurate (the PREP-6 substep decomposition, the OQ-02 audit, the
  three S2 candidates A/B/C are all still the load-bearing context).
- Any Lean file in `proofs/Proofs/`.
- Any other slug's data, including OQ-02's gallery JSON
  (`src/data/proofs/sylow-theorems-oq-02/meta.json` axiomCount 5 →
  4 is § 5a's deferred follow-on, not S3's scope).
- The lake manifest (`proofs/lake-manifest.json`).

**Race awareness.** At S3 PREP open: `gh pr list --search
"sylow-theorems-oq-03 in:title" --state open --repo
rjwalters/lean-genius --limit 50` returned `[]` — **0 open PRs** for
this slug. No concurrency risk.

## § 8 — Summary for the picker

**OQ-03 status as of 2026-05-16T00:25Z:**

- ✓ S2 ACT MERGED (#19260, build-verified 3062 Docker jobs)
- ✓ `proofs/Proofs/SylowTheoremOQ03.lean` lives in `origin/main`:
  162 LOC, 1 def + 4 theorems, **0 sorries / 0 axioms**
- ✓ All 8 Mathlib bearers pin-verified at v4.26.0 (PREP-7); no drift
- ✗ OQ-02 axiom drop NOT realized (deferred — see § 5a)

**Top-priority next action:** § 5a (delete OQ-02 axiom L134 +
gallery-meta sync, mechanic-grade ~5-LOC PR, 1 Docker iteration).
**Secondary:** § 5b (Candidate B ACT, ~25 LOC, medium-risk).
**Out-of-band:** § 5c (Mathlib upstream), § 5d (frattini restatement).

---

**Net of this PR.** 3 files touched (1 NEW session, 1 state.md update,
1 JSON update). 0 Lean. 0 build risk. Strictly orthogonal to all
other open work in the repo (0 sibling open PRs).
