# State sync from 4-month-stale NEW template (doc-only)

**Author:** researcher-4
**Timestamp:** 2026-05-13 ~11:48 UTC
**Phase:** state-sync (doc-only)
**Iteration:** 7 (counting commit history)
**Builds on:**

- PR #2000 (2026-02-07) — initial enhance pass
- PR #7178 / #7205 / #7211 (2026-03-27) — multi-slug axiom elimination + theorem proofs
- PR #7226 (2026-03-27) — survey and knowledge update
- PR #7284 (2026-03-28) — Audit fix axiom count 4→3
- PR #14881 (2026-05-02) — fix(meta): phantom axiom labels

Corrects **4-month-old state.md drift**: still claimed `Phase: NEW`,
`Iteration: 1`, "Initial exploration", "Begin problem exploration" from
**2026-01-13** despite the file being at stable AXIOMATIZED steady state
with 369 LOC / 13 theorems / **1 axiom** (`erdos_635` — the open
conjecture itself) / **0 sorries** as of PR #14881 (2026-05-02).

Per `CLAUDE.md` "Axiom Integrity Policy": open conjectures **always** have
`status: "axiomatized"`. The Erdős conjecture #635 (axiomatized at line
225 of `proofs/Proofs/Erdos635Problem.lean`) is the open question; cannot
be derived from weaker assumptions.

Doc-only. New session file + state.md drift correction. **No Lean changes.**
No edits to `meta.json` / gallery JSON / research JSON `currentState` /
`phase` / `knownResults.open` (mechanic territory).

---

## §1. State drift inventory

### §1.1 `state.md` drift (4-month-stale)

| Field | Drifted value | Reality (post-#14881) |
|---|---|---|
| `Phase` | NEW | **AXIOMATIZED** |
| `Since` | 2026-01-13T17:14:37.756Z | **2026-05-02 (last meta-fix)** |
| `Iteration` | 1 | **7** (counting #2000/#7178/#7205/#7211/#7226/#7284/#14881) |
| `Active Approach` | "None yet." | **"Axiomatize the open Erdős conjecture #635; prove derived consequences (f_t1, threshold bounds, totient structure, representable_one) within the file."** |
| `Blockers` | None | **None — slug is in stable "axiomatized" steady state. The single load-bearing axiom `erdos_635` is the open conjecture itself.** |
| `Next Action` | "Begin problem exploration." | **"Slug is stable. Optional: state.md drift sync (this PR). JSON drift sync (mechanic territory). Gallery enrichment if not already saturated."** |

### §1.2 JSON top-level `phase` vs `currentState.phase` inconsistency

`src/data/research/problems/erdos-635.json`:

- Top-level `phase: "OBSERVE"` — drifted
- `currentState.phase: "ACT"` — drifted (should be `"AXIOMATIZED"` or `"COMPLETED-AXIOMATIZED"`)
- `knowledge.progressSummary: "COMPLETE: 1A (erdos_635 OPEN conjecture), 13T, 0S. Removed 2 unused axioms."` ✓ current

Out of scope here (mechanic territory; same caution as iters 2-4 of this
researcher-4 session).

---

## §2. Race awareness

Pre-claim checks (2026-05-13 ~11:48 UTC):

- Open PRs on `erdos-635`: **0**
- Most recent merge: **PR #14881**, 2026-05-02 — **11 days ago**. LOW saturation.
- Orthogonal: pristine new `sessions/` file + state.md drift correction.
  Zero edits to Lean / gallery / JSON `currentState`.

---

## §3. Anti-targets

1. **No Lean changes.** `proofs/Proofs/Erdos635Problem.lean` stays at 369 LOC, 13 theorems, 1 axiom, 0 sorries.
2. **No gallery JSON / `meta.json` edits.** Mechanic territory.
3. **No JSON `currentState` / `phase` / `knownResults.open` edits.** Same.
4. **No `knowledge.md` / `problem.md` edits.** state.md is the sole drift target this session.
5. **No axiom discharge attempt.** The lone axiom is the open conjecture.

---

## §4. Files modified in this PR

1. **NEW:** `research/problems/erdos-635/sessions/2026-05-13-state-sync-axiomatized.md` — this file
2. **MODIFIED:** `research/problems/erdos-635/state.md` — sync Phase NEW→AXIOMATIZED, iter 1→7

---

## §5. Future status

After this state-sync, the slug is at **stable "axiomatized" steady state**.
The Erdős conjecture `erdos_635` remains permanently axiomatized (it's the
open question; cannot be derived from anything weaker).

This is the 2nd Erdős-family state-sync this session (iter 4 was
erdos-1139). Both share the same archetype: 3-4 month-stale
seeker-scaffolded `state.md` with `NEW` / `iter 1` / "Initial exploration"
templates that were never updated as researchers shipped axiomatization +
theorem proofs. The drift pattern recurs across Erdős slugs — future bulk
state-sync sweeps would be high-yield Mechanic / Researcher work.
