# S11 STATE-SYNC — axiomatized-final canonical JSON catchup

**Date**: 2026-05-16T22:48Z
**Researcher**: researcher-12 (claim-random landed here at 22:46Z, post-ship pivot from sqrt2-minpoly-oq-03 S6 STATE-SYNC PR #19901)
**Slug**: `sperner-ndim-oq-04` (Tier A, RICH 71, MODERATE+)
**Phase**: COMPLETED — axiomatized-final
**Type**: doc-only STATE-SYNC (3 files: state.md + JSON + this NEW memo)
**Predecessor terminal-state merge**: PR #14937 (S10 re-axiomatization, merged 2026-05-02, T-14d)

---

## §1 Why this STATE-SYNC fires

Claim-random landed researcher-12 on `sperner-ndim-oq-04` at 2026-05-16T22:46Z.
Inspection found a three-way drift between the three sources of truth for the slug:

| Source                                                          | Asserts                                              | Status |
|-----------------------------------------------------------------|------------------------------------------------------|--------|
| `proofs/Proofs/SpernerNDimOQ04.lean` (Lean file)                | 0 sorries, 1 axiom, 948 LOC, 23 theorems, 5 defs    | terminal-state |
| `src/data/proofs/sperner-ndim-oq-04/meta.json` (gallery)        | `status: axiomatized`, `badge: axiom`, `lineCount: 948`, `axiomCount: 1`, `theoremCount: 23`, `sorries: 0` | **CANONICAL** (matches Lean) |
| `research/problems/sperner-ndim-oq-04/state.md` (state head)    | `Phase: COMPLETED`, `Since: 2026-05-02 (Session 10)`, `Iteration: 10` | **CANONICAL** (matches Lean) |
| `src/data/research/problems/sperner-ndim-oq-04.json` (research JSON) | `phase: BLOCKED`, `status: blocked`, `currentState.phase: BLOCKED`, `currentState.iteration: 9`, `currentState.nextAction: "Future session: implement kuhnWalkSeq..."`, `leanFiles[0]: {lineCount: 734, theoremCount: 13, defCount: 6}`, `lastUpdate: 2026-04-27T17:24:06Z` | **STALE** (frozen 2026-04-27, never updated after S10 2026-05-02) |

Three concurrent surfaces are correct (gallery + Lean + state.md); the research-JSON
is the lone outlier. S11 catches it up.

This is **structurally similar** to the memory pattern
`_long_completed_slug_with_statemd_phase_drift_vs_canonical_json_and_resolved_nextaction_item_still_listed_ship_3file_statesync_bootstrap_sessions_dir`,
but **inverted in direction**: the memory pattern has state.md stale and JSON canonical;
here state.md is canonical and JSON is stale. The 3-file STATE-SYNC + sessions-bootstrap
remedy is the same.

---

## §2 Drift inventory (research JSON pre- vs post-S11)

| Field path                                | Pre-S11 (stale 2026-04-27)                          | Post-S11 (canonical 2026-05-16) |
|-------------------------------------------|-----------------------------------------------------|----------------------------------|
| top-level `phase`                         | `BLOCKED`                                           | `COMPLETED`                      |
| top-level `status`                        | `blocked`                                           | `axiomatized`                    |
| `currentState.phase`                      | `BLOCKED`                                           | `DONE`                           |
| `currentState.since`                      | `2026-04-27T18:30:00.000Z`                          | `2026-05-02T00:00:00.000Z`       |
| `currentState.iteration`                  | `9`                                                 | `11`                             |
| `currentState.focus`                      | "BLOCKED on walkTrace_reversal — needs ~150 lines..." | "S11 STATE-SYNC ... canonical JSON catchup to S10 axiomatized-final reality ..." |
| `currentState.blockers[0]`                | active prose                                        | prepended `[RESOLVED in S10 ... reconciled by S11 STATE-SYNC 2026-05-16]` marker; body retained verbatim |
| `currentState.nextAction`                 | "Future session: implement kuhnWalkSeq..."          | "**None** — entry is axiomatized-final ... Optional follow-up Path A or B ... (knowledge.md §Two Concrete Unblock Paths)" |
| `currentState.attemptCounts.total`        | `9`                                                 | `11`                             |
| `knowledge.progressSummary`               | tail-only "Re-axiomatized: ..."                     | prepended S11 reconcile note; existing S10 prose preserved verbatim |
| `knowledge.nextSteps[0..2]`               | 3-item active-work plan (walkTrace_reversal etc.)   | 3-item optional-follow-up plan (Path A / Path B / axiom-accept) |
| `lastUpdate`                              | `2026-04-27T17:24:06Z`                              | `2026-05-16T22:48:00.000Z`       |
| `leanFiles[0].lineCount`                  | `734`                                               | `948`                            |
| `leanFiles[0].theoremCount`               | `13`                                                | `23`                             |
| `leanFiles[0].defCount`                   | `6`                                                 | `5`                              |
| `leanFiles[0].axiomCount`                 | `1`                                                 | `1` (unchanged)                  |
| `leanFiles[0].sorryCount`                 | `0`                                                 | `0` (unchanged)                  |

**Total**: 15 fields edited (12 currentState/knowledge/lastUpdate + 3 leanFiles numerics + 2 top-level).

Reformatted: 1 blockers entry preserved-with-prefix (not removed; retained as historical record per memory pattern §"What to NOT do" guidance to preserve blockers unless verifiably resolved — here resolved-by-axiomatization, but the underlying mathematical observation about kuhnPathStart forgetting the walk path remains TRUE, just no-longer-blocking-after-acceptance).

---

## §3 Verification commands

### Canonical counts (per `feedback_mechanic_batch_sync_conventions_canonical_counts_and_python_json_dump_unicode_trap`)

```bash
F=proofs/Proofs/SpernerNDimOQ04.lean
echo "LOC (wc -l raw): $(wc -l < $F)"
# → 948
echo "theorems: $(grep -cE '^(protected |private |noncomputable )*(theorem|lemma) ' $F)"
# → 23
echo "defs: $(grep -cE '^(def|noncomputable def|opaque def) ' $F)"
# → 5
echo "sorries (raw \\bsorry\\b): $(grep -cE '\bsorry\b' $F)"
# → 0
echo "axioms (^axiom ): $(grep -cE '^axiom ' $F)"
# → 1
```

### Gallery cross-check (read-only, NOT touched in S11)

```bash
$ jq '.meta | {status, badge, sorries, axiomCount, theoremCount, lineCount}' \
    src/data/proofs/sperner-ndim-oq-04/meta.json
{
  "status": "axiomatized",
  "badge": "axiom",
  "sorries": 0,
  "axiomCount": 1,
  "theoremCount": 23,
  "lineCount": 948
}
```

Gallery `definitionCount: 8` (broader convention than research-JSON `defCount: 5`) —
NOT reconciled here; gallery meta.json is mechanic territory per CLAUDE.md "Axiom
Integrity Policy" + memory convention. Different regex conventions are deliberate and
not a defect.

### Most recent activity verification

```bash
$ git log --all --oneline -3 -- src/data/research/problems/sperner-ndim-oq-04.json
ecb47b35601 research(sperner-ndim-mathlib-oq-01-oq-04): S2-A ACT — ... (#19454)  # SIBLING slug
2ace1c84053 research(angle-trisection-oq-05-oq-04): S7 — ... (#18059)            # unrelated drive-by
0f85e861f72 Research: hilbert-20-oq-01 (-1 sorry), erdos-1018 (-1 sorry), \
            sperner-ndim-oq-04 (re-axiomatize to 0 sorries/1 axiom) (#14937)     # S10 terminal-state
```

PR #14937 (2026-05-02) was the last edit to the research-JSON — it touched the file
to re-axiomatize the Lean side but did not refresh `phase` / `status` / `leanFiles`.
14 days of drift accumulated.

### Validation post-edit

```bash
$ python3 -c "import json; d=json.load(open('src/data/research/problems/sperner-ndim-oq-04.json')); \
              print('phase:', d['phase'], 'status:', d['status'], \
                    'cs.phase:', d['currentState']['phase'], \
                    'cs.iter:', d['currentState']['iteration'], \
                    'lineCount:', d['leanFiles'][0]['lineCount'])"
phase: COMPLETED status: axiomatized cs.phase: DONE cs.iter: 11 lineCount: 948
```

JSON parses cleanly; all top-level + currentState + leanFiles fields canonical.

---

## §4 Sessions directory bootstrap

Pre-S11 directory listing:

```bash
$ ls research/problems/sperner-ndim-oq-04/
knowledge.md
literature
problem.md
selection-report.md
state.md
# (no sessions/ dir)
```

S11 creates `sessions/` via this memo. Future doc-only STATE-SYNCs or session notes
land cleanly here without needing to inline-embed in state.md head.

---

## §5 What S11 STATE-SYNC does NOT do (explicit non-actions)

To preserve scope and avoid creep into adjacent territory, S11 deliberately abstains
from each of:

1. **`proofs/Proofs/SpernerNDimOQ04.lean`** — terminal-state, 0 sorries, 1 axiom-final.
   Optional Path A / Path B discharge is documented in knowledge.md §"Two Concrete
   Unblock Paths" but lies outside STATE-SYNC scope.
2. **`research/problems/sperner-ndim-oq-04/problem.md`** — formal statement is
   canonical; "Why matters" is evergreen.
3. **`research/problems/sperner-ndim-oq-04/knowledge.md`** body (~469 LOC) — the
   `## Two Concrete Unblock Paths` section + builtItems + insights are already
   accurate. Only the JSON's mirror was stale.
4. **`src/data/proofs/sperner-ndim-oq-04/meta.json`** (gallery) — already canonical
   per §3 verification; mechanic territory per CLAUDE.md "Axiom Integrity Policy".
5. **`proofs/lake-manifest.json`** — Mathlib pin unchanged (slug at terminal state, no
   bearer-resolution work pending).
6. **Sibling slugs** (`sperner-ndim-mathlib-oq-01-oq-04` etc.) — those have their own
   state and recent activity (PR #19454, 2026-05-12).
7. **Re-spot-check of Mathlib bearers** — terminal-state, busywork per
   `feedback_sha_stable_busywork` memory.
8. **`research/problems/sperner-ndim-oq-04/literature/`** + `selection-report.md` —
   evergreen archival.

---

## §6 Acceptance criteria

- [x] `python3 -c "import json; json.load(...)"` validates `src/data/research/problems/sperner-ndim-oq-04.json`
- [x] state.md head shows `Phase: COMPLETED — axiomatized-final`, `Iteration: 11`, `Last Updated: 2026-05-16T22:48Z`
- [x] research-JSON `phase: COMPLETED`, `status: axiomatized`, `currentState.phase: DONE`, `currentState.iteration: 11`, `currentState.attemptCounts.total: 11`
- [x] `leanFiles[0]`: `lineCount: 948`, `theoremCount: 23`, `defCount: 5`, `axiomCount: 1`, `sorryCount: 0` (matches canonical regex on `proofs/Proofs/SpernerNDimOQ04.lean`)
- [x] `lastUpdate: 2026-05-16T22:48:00.000Z`
- [x] sessions/ directory exists (bootstrapped by this memo)
- [x] 0 Lean / problem.md / knowledge.md body / gallery / lake-manifest edits
- [x] 0 sibling-slug touches
- [x] No `pnpm build` invocation (per `feedback_mechanic_pnpm_build_regenerates_all_research_jsons` memory — would clobber ~1047 research JSONs)

---

## §7 Host context (informational, irrelevant for doc-only)

- **G7 disk**: `/dev/disk3s5` 926 Gi, 885 Gi used, 4.4 Gi avail (100% capacity) — **RED** but doc-only
- **G8 Docker**: `docker info` returns empty `Server:` section (daemon hung ≥6h based on same-day sibling reports in sqrt2-minpoly-oq-03 S6 STATE-SYNC PR #19901 + abel-ruffini-oq-04-oq-09 S7 STATE-SYNC PR #19755) — **RED** but doc-only
- **G9 `proofs/.lake`** → `/Users/rwalters/GitHub/lean-genius/proofs/.lake` (circular self-symlink, NOT containing actual lake build artifacts) — **RED** but doc-only

All 3 RED but immaterial: this is a doc-only STATE-SYNC on a terminal-state slug, no
build verification needed, no bearer reverify needed (Mathlib pin unchanged + terminal-state).

This is the **third** STATE-SYNC researcher-12 has shipped today (other two: sqrt2-minpoly-oq-03
S6 PR #19901 and abel-ruffini-oq-04-oq-09 S7 PR #19755). All three slugs report the
same 3-RED host-side INFRA; defensible carry-forward of host evidence on same wall-clock day.

---

## §8 Honesty calibration

What S11 actually accomplishes:
- ✅ Removes navigation hazard: a future claim-random landing here will not be misled
  by a JSON saying "BLOCKED, ~150-line future work needed" when state.md + Lean +
  gallery agree the slug has been axiomatized-final for 14 days.
- ✅ Closes 14-day-old numeric drift on `leanFiles[0]` (+214 LOC, +10 theorems, -1 def
  out-of-band changes between 2026-04-27 and 2026-05-02).
- ✅ Bootstraps `sessions/` directory.

What S11 does NOT claim:
- ❌ This does NOT discharge the `bdry_all_even_of_no_fc_walks` axiom (Path A / Path B
  remain optional future work; estimated 150-200+ LOC each).
- ❌ This does NOT alter the slug's terminal-state status — the slug was already
  axiomatized-final per state.md / gallery / Lean; S11 only catches up the research-JSON
  mirror.
- ❌ This does NOT verify a build (Docker hung; not relevant since 0 Lean edits).
- ❌ This does NOT close out optional future kuhnWalkSeq discharge work — it's now
  tracked correctly in `currentState.nextAction` + `knowledge.nextSteps` as **optional,
  not blocking**.

---

## §9 References

- **Terminal-state PR**: [#14937](https://github.com/rjwalters/lean-genius/pull/14937) "Research: hilbert-20-oq-01 (-1 sorry), erdos-1018 (-1 sorry), sperner-ndim-oq-04 (re-axiomatize to 0 sorries/1 axiom)" (merged 2026-05-02)
- **Lean file**: [`proofs/Proofs/SpernerNDimOQ04.lean`](../../../../proofs/Proofs/SpernerNDimOQ04.lean) — 948 LOC, 23 theorems, 1 axiom, 0 sorries
- **Research-JSON canonical**: [`src/data/research/problems/sperner-ndim-oq-04.json`](../../../../src/data/research/problems/sperner-ndim-oq-04.json)
- **Gallery meta**: [`src/data/proofs/sperner-ndim-oq-04/meta.json`](../../../../src/data/proofs/sperner-ndim-oq-04/meta.json)
- **State.md**: [`../state.md`](../state.md) (S11 head)
- **Knowledge.md** §"Two Concrete Unblock Paths": [`../knowledge.md`](../knowledge.md)

### Memory pattern cross-refs

- `feedback_researcher_long_completed_slug_with_statemd_phase_drift_vs_canonical_json_and_resolved_nextaction_item_still_listed_ship_3file_statesync_bootstrap_sessions_dir` — closest pattern match, **inverted** (memory has state.md stale + JSON canonical; here JSON stale + state.md canonical). Same 3-file remedy.
- `feedback_researcher_postship_pivot_to_long_completed_slug_with_recent_observe_audit_updated_4_of_5_surfaces_canonical_json_materially_contradicts_observe_findings_ship_13_field_state_sync` — closer in spirit (canonical JSON contradicts other surface), here JSON contradicts gallery+state.md+Lean rather than OBSERVE memo.
- `feedback_mechanic_batch_sync_conventions_canonical_counts_and_python_json_dump_unicode_trap` — used for canonical-counts regex (LOC=wc -l, thm=`^(protected|private|noncomputable )*(theorem|lemma) `, def=`^(def|noncomputable def|opaque def) `, sorry=raw `\bsorry\b`, axiom=`^axiom `).
- `feedback_mechanic_pnpm_build_regenerates_all_research_jsons` — explicit reason for skipping `pnpm build` (would clobber ~1047 research JSONs); validated with python json.load instead.
- `feedback_sha_stable_busywork` — explicit reason for not re-spot-checking Mathlib bearers (terminal-state, no future bearer work).

### Sibling slugs (informational, not touched)

- `sperner-ndim` — parent gallery slug
- `sperner-ndim-mathlib-oq-01`, `-oq-02`, `-oq-01-oq-04` — Mathlib-formalization siblings
- `sperner-ndim-oq-01`, `-oq-02`, `-oq-03`, `-oq-03-oq-01`, `-oq-05` — research-problem siblings

---

**End of S11 STATE-SYNC memo.**
