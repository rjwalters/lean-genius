# Session 7 — S7 STATE-SYNC (JSON catch-up, 2026-06-10)

**Researcher**: researcher-1 (claim `researcher-81997`)
**Mode**: STATE-SYNC (doc-only). No Lean edits, no axiom/sorry change, no gallery-meta change.
**Trigger**: `src/data/research/problems/cayley-hamilton-minpoly-oq-03-oq-02.json` is 11 days stale. Two substantive iterations have shipped to `main` since the JSON was last touched:
  * **S5 ACT** PR #22531 (`e0523965e2b`, merged 2026-06-05): matvec-count bound + Layer 3 ω-axioms.
  * **S6 ACT** PR #22595 (`fa34cb8cbaf`, merged 2026-06-06): gallery promotion (`src/data/proofs/cayley-hamilton-minpoly-oq-03-oq-02/meta.json` + `annotations.json` created).

Both PRs updated `state.md` and shipped Lean / gallery content, but **did not update** the research-pool JSON's `currentState`, `attemptCounts`, `leanFiles[9]`, or top-level `lastUpdate`. The S7 STATE-SYNC catches up the JSON so any picker reading it sees the on-disk reality.

## §1 Drift detected at S7 start

| Surface | On-disk reality (2026-06-10) | Stale JSON read | Δ |
|---------|------------------------------|-----------------|----|
| `proofs/Proofs/CayleyHamiltonMinpolyOQ03OQ02.lean` | 333 LOC / 11 theorems / 3 axioms / 0 sorries | (no on-disk Δ — JSON is the lagging surface) | — |
| `src/data/proofs/cayley-hamilton-minpoly-oq-03-oq-02/meta.json` (gallery) | `leanFile.lineCount: 333`, `axiomCount: 3`, `theoremCount: 11`, `definitionCount: 2`, `sorries: 0` | (no on-disk Δ) | — |
| `research/problems/cayley-hamilton-minpoly-oq-03-oq-02/state.md` header | `Phase: ACT`, `Since: 2026-06-06`, `Iteration: 6` | (no on-disk Δ) | — |
| `src/data/research/problems/cayley-hamilton-minpoly-oq-03-oq-02.json` `currentState.phase` | `ACT` | `ACT` | — |
| `..."currentState.iteration"` | should be 7 (6 prior + this S7) | `4` | **+3** |
| `..."currentState.since"` | S7 2026-06-10 | `2026-05-14T19:30:00.000Z` | bump |
| `..."currentState.focus"` | should reflect S5 + S6 + S7 catch-up | `S4 ACT (build verified, researcher-1, 2026-05-30) — Layer 2 vector form shipped…` | rewrite |
| `..."currentState.blockers"` | Layer 3 / Mathlib infra only (carryforward) | same content (unchanged in substance) | unchanged |
| `..."currentState.nextAction"` | "Problem at completion-ready state…" | `S5 — matvec-count bound + axiomatized Layer 3 placeholder…` | rewrite |
| `..."currentState.attemptCounts.total"` | should be 7 | `4` | **+3** |
| `..."knowledge.progressSummary"` | prepend S5 + S6 + S7 | starts at S3 ACT | prepend |
| `..."knowledge.nextSteps"` | re-order: optional follow-ups + Mathlib upstream | starts with S5 matvec-count (now done) | rewrite |
| `..."knowledge.builtItems"` | append S5 (axioms / factor-count) + S6 (gallery entry) | ends at S4 ACT vector-level | append 2 |
| `..."leanFiles[9].lineCount"` | 333 | `200` | **+133** |
| `..."leanFiles[9].theoremCount"` | 11 | `7` | **+4** |
| `..."leanFiles[9].axiomCount"` | 3 | `0` | **+3** |
| `..."leanFiles[9].sorryCount"` | 0 | `0` | — |
| `..."leanFiles[9].defCount"` | 2 | `2` | — |
| top-level `"lastUpdate"` | 2026-06-10 | `2026-05-30` | bump |
| top-level `"status"` | (per state.md: "Problem can be marked `completed` in the research pool") | `active` | left as-is in this S7; pool status update is via `claim-problem.sh` after this PR lands |

## §2 Axiom Integrity recheck (per CLAUDE.md policy)

```text
$ grep -nE "^axiom " proofs/Proofs/CayleyHamiltonMinpolyOQ03OQ02.lean
240:axiom omegaMM : ℝ
247:axiom omegaMM_two_le : (2 : ℝ) ≤ omegaMM
253:axiom omegaMM_lt_three : omegaMM < (3 : ℝ)

$ grep -nE "^structure |^class " proofs/Proofs/CayleyHamiltonMinpolyOQ03OQ02.lean
(no matches)

$ grep -nE ":= by sorry|:= sorry|^[[:space:]]+sorry$" proofs/Proofs/CayleyHamiltonMinpolyOQ03OQ02.lean
(no matches)
```

Three axiom declarations, no structure/class definitions, no `sorry` tactics. Gallery `meta.json` correctly reports `leanFile.axiomCount: 3` and `sorries: 0`. Status field per state.md: `axiomatized` (with `badge: axiom`) — matches the CLAUDE.md policy ("Status field definitions": `axiomatized` for "Formalized with stated assumptions").

## §3 Mathlib pin recheck (no drift)

```text
$ python3 -c "import json; m=json.load(open('proofs/lake-manifest.json')); print([p['rev'] for p in m['packages'] if p.get('name')=='mathlib'][0])"
2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
```

Same SHA as S4 / S5 / S6 (Mathlib v4.26.0). 28-day byte-identical pin since 2026-05-13. No bearer recheck needed for this S7 (doc-only).

## §4 What changed (concise)

| File | Δ | Note |
|------|---|------|
| `src/data/research/problems/cayley-hamilton-minpoly-oq-03-oq-02.json` | currentState.{iteration 4→7, since, focus, nextAction} + attemptCounts.total 4→7 + currentApproach 4→6 + knowledge.{progressSummary,builtItems,nextSteps} + leanFiles[9].{lineCount 200→333, theoremCount 7→11, axiomCount 0→3} + top-level lastUpdate | S5 + S6 + S7 catch-up |
| `research/problems/cayley-hamilton-minpoly-oq-03-oq-02/state.md` | S7 header prepend + drift table | Prior S6 / S5 / S4 / earlier content preserved verbatim below |
| `research/problems/cayley-hamilton-minpoly-oq-03-oq-02/sessions/2026-06-10-s7-state-sync-json-catchup.md` | NEW | This session log |

**No Lean files modified. No gallery `meta.json` / `annotations.json` modified. No axiom / sorry / line-count delta in the Lean source.**

## §5 Race-safety probe

`gh pr list --state=open` (no `--json`, since GH GraphQL auth is unavailable in this session) at 2026-06-10 ~16:40Z:

* PR #22824 (`feature/researcher-1`, euler-identity ACT-3, OPEN) — not touching this slug.
* PR #22831 (`research/greens-oq01010201-s11-docker-recovery`, this session's earlier ship) — orthogonal.
* No in-flight researcher PR for `cayley-hamilton-minpoly-oq-03-oq-02`. Most recent merged PR on the slug is #22595 (S6 gallery promotion) 4 days ago.

`git log --all --oneline -- src/data/research/problems/cayley-hamilton-minpoly-oq-03-oq-02.json`: most recent modification is `1859c4739de fix(meta): erdos-29 lineCount 523→524 align with Erdos29Problem.lean` — that touched the JSON in passing (likely a bulk meta-sync), not a slug-specific edit. Last meaningful currentState refresh was at S4 (2026-05-30 via PR #21352).

S7 is doc-only / strictly orthogonal to any concurrent Lean edit. Push will not conflict.

## §6 Revised next action (per state.md S6 §"Next Action")

State.md S6 already declared the next action: **"Problem can be marked `completed` in the research pool."** S7 STATE-SYNC carries this forward verbatim.

Why this S7 ships without doing the status promotion in the JSON: top-level `status` field in the research JSON is one of `{active, in-progress, completed, mature, blocked, graduated, progressed}`. Moving from `active` to `completed` is a pool-state transition, conventionally driven by `scripts/research/claim-problem.sh update <slug> completed` (which writes the pool state in `claims.json`), not directly in the research JSON. After this S7 PR lands, the next picker (or this session) can issue that script call to formally drop the slug into the completed bucket.

Optional follow-ups (carry from state.md S6, not started here):

* `annotations.json` — already shipped in S6 (16,850 bytes), but inline annotations could be refined; not blocking.
* `Nat.size j` factor-count sharpening — pending Mathlib `Nat.bitIndices` length API.
* Layer 3 full operation-count theorem — pending Mathlib complexity-monad infrastructure (not a single-problem target).

## §7 Honesty check

Per the researcher role's "Honesty Standards":

* This S7 is **doc-only JSON catch-up**. No Lean delta, no axiom delta, no gallery `meta.json` change.
* The "ready for completion" finding is real-state evidence (gallery meta lineCount/axiomCount/theoremCount match the on-disk Lean source; state.md §"Next Action" explicitly says "Problem can be marked completed"), not inferred.
* The catch-up scope is larger than the greens-S11 tick (which was a single-field blocker clear) because two iterations (S5 + S6) shipped without research-JSON updates. The JSON refresh has the form documented in §1's drift table.

## §8 Comparison to today's earlier S11 STATE-SYNC

Earlier this session I shipped an analogous JSON-catch-up for `greens-theorem-oq-01-oq-01-oq-02-oq-01` (PR #22831). That S11 cleared a stale RED INFRA `blockers` field after a 7-day-expired Docker condition. This S7 is heavier (S5 + S6 worth of currentState / focus / nextAction / leanFiles drift), but the principle is the same: research JSON is the canonical signal that triage / seeker / picker logic reads programmatically; stale entries route pickers wrong. The doc-only catch-up is the correct minimal action.
