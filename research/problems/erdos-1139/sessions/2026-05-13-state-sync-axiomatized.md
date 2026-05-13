# State sync from 3-month-stale NEW template (doc-only)

**Author:** researcher-4
**Timestamp:** 2026-05-13 ~11:45 UTC
**Phase:** state-sync (doc-only)
**Iteration:** 6 (counting commit history on `proofs/Proofs/Erdos1139Problem.lean`)
**Builds on:**

- PR #6336 (2026-03-24) — "Research: erdos-1139 — define almostPrimeGap, eliminate last sorry"
- PR #6247, #6421 (2026-03-24) — meta drift fixes
- PR #8475 (2026-03-30) — "Research: erdos-1139 axiom restore + erdos-687 prove Y(3)=3"
- PR #14978 (2026-05-03) — "fix(erdos-1139): restore missing axioms `erdos_1139` and `hardy_ramanujan_asymptotic`"

This session corrects **3-month-old state.md drift**: state.md is the
unmodified seeker scaffold from **2026-02-08T00:55:03.568Z**, still claiming
`Phase: NEW`, `Iteration: 1`, "Initial exploration", "Next Action: Begin
problem exploration" — despite the file being **AXIOMATIZED phase** with 5+
merged Lean PRs (#6247/#6336/#6421/#8475/#14978) and 16 theorems / 2 axioms
/ 0 sorries on the current main.

The Erdős problem (#1139) — "are the gaps between successive almost-primes
unbounded relative to log k?" — is an **open conjecture**. Per
`CLAUDE.md` "Axiom Integrity Policy": open conjectures **always** have
`status: "axiomatized"`. The two axioms are:

1. **`erdos_1139`** — the Erdős conjecture statement itself
   (unprovable by definition: it's the open question)
2. **`hardy_ramanujan_asymptotic`** — Hardy-Ramanujan's classical
   distribution result for the almost-prime counting function π_k(N)
   (provable in principle but requires substantial PNT/sieve infrastructure
   not in Mathlib v4.26.0)

Doc-only. New session file + state.md drift correction. **No Lean changes.**
No edits to `meta.json` / gallery JSON / research JSON `currentState` /
`knownResults.open` (mechanic territory per prior PRs' anti-target lists).

---

## §1. State drift inventory

### §1.1 `state.md` drift (5 fields, 3-month-stale)

| Field | Drifted value | Reality (post-#14978) |
|---|---|---|
| `Phase` | NEW | **AXIOMATIZED** (axiom restoration completed 2026-05-03) |
| `Since` | 2026-02-08T00:55:03.568Z | **2026-05-03 (last axiom restoration)** |
| `Iteration` | 1 | **6** (counting #6247/#6336/#6421/#8475/#14978 + state-sync) |
| `Active Approach` | "None yet." | **"Axiomatize the open Erdős conjecture + Hardy-Ramanujan asymptotic; prove derived consequences (`almostPrimeGap` definitions, axiom-form theorems) within the file."** |
| `Blockers` | None | **None — slug is in stable "axiomatized" steady state. Future work = optional Mathlib bearer audit for `hardy_ramanujan_asymptotic` if PNT/sieve infrastructure lands in Mathlib upstream.** |
| `Next Action` | "Begin problem exploration." | **"Slug is stable. Optional: state.md drift sync (this PR). Gallery entry update to reflect 2-axiom status. Mathlib upstream watch for any Hardy-Ramanujan-class results."** |

### §1.2 JSON top-level `phase` vs `currentState.phase` inconsistency

`src/data/research/problems/erdos-1139.json` has:

- Top-level `phase: "OBSERVE"` — drifted
- `currentState.phase: "ACT"` — drifted (should be `"AXIOMATIZED"` or `"COMPLETED-AXIOMATIZED"`)
- `knowledge.progressSummary: "RESTORED: axioms erdos_1139 and hardy_ramanujan_asymptotic re-added. 16T, 2A, 0S. Status: axiomatized."` ✓ current

Inconsistency: top-level `phase` ≠ `currentState.phase`. Both wrong (one says OBSERVE, the other ACT; reality is AXIOMATIZED).

**Out of scope:** Updating JSON top-level `phase` / `currentState.phase` /
`knownResults.open`. This is mechanic territory (gallery-rebuild side
effects). A future mechanic PR can sync state.md ↔ JSON in one commit.

---

## §2. Mathlib gap audit at lake-pinned SHA

Verified at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (= `v4.26.0` tag,
= `proofs/lake-manifest.json` pin):

| Search query | Hits in `Mathlib/` | Verdict |
|---|---|---|
| `hardy_ramanujan` | 0 | Not in Mathlib |
| `ArithmeticFunction.cardDistinctFactors` | 2 (`Antidiag/Nat.lean`, `ArithmeticFunction/Misc.lean`) | The ω function exists but **NOT** the asymptotic distribution result for π_k(N) |
| `almostPrime` | 0 | The "almost-prime counting function π_k" is not in Mathlib |

**Confirmed Mathlib gap.** The `hardy_ramanujan_asymptotic` axiom remains
load-bearing at v4.26.0. The slug's "axiomatized" status is honest.

### §2.1 Why these axioms are appropriate

Per `CLAUDE.md` "Axiom Integrity Policy":

> Millennium Prize problems, Clay problems, and open conjectures: always `"axiomatized"`. Never use `"conditional"` — use `"axiomatized"` and describe the conditions in the `assumptions` field

Erdős problem #1139 is an **open conjecture** (cited in the Erdős problems
database; status: unsolved). Axiomatizing the conjecture statement is the
correct formalization choice — the slug **derives consequences** of the
conjecture (if the conjecture is true, then various related properties
follow), without claiming to prove the conjecture itself.

`hardy_ramanujan_asymptotic` is a **classical proved result** (Hardy and
Ramanujan, 1917) but not in Mathlib. Axiomatizing it as a stated assumption
is honest until Mathlib upstream lands the PNT/sieve infrastructure
(probably part of the long-running `Mathlib.NumberTheory.LSeries` and
`Mathlib.NumberTheory.PrimeCounting` modernization).

---

## §3. Race awareness

Pre-claim checks (2026-05-13 ~11:45 UTC):

- Open PRs on `erdos-1139`: **0** (verified via
  `gh pr list --repo rjwalters/lean-genius --search "erdos-1139 in:title" --state open`)
- Most recent merge: **PR #14978**, 2026-05-03 — **10 days ago**. LOW saturation.
- This session is **orthogonal by construction**: pristine new
  `sessions/2026-05-13-state-sync-axiomatized.md` + state.md drift
  correction. **Zero edits** to Lean files, JSON `currentState` / `phase` /
  `knownResults.open`, gallery JSON, `meta.json`, or `knowledge.md`.

### §3.1 PR history grid

| PR # | Title | Status | Date |
|---|---|---|---|
| #6247 | Audit: fix sorry counts | merged | 2026-03-24 |
| #6336 | Define almostPrimeGap, eliminate last sorry | merged | 2026-03-24 |
| #6421 | Mechanic lineCount fix | merged | 2026-03-24 |
| #8475 | Axiom restore + erdos-687 Y(3)=3 | merged | 2026-03-30 |
| #14978 | **Restore missing axioms** `erdos_1139` + `hardy_ramanujan_asymptotic` | merged | 2026-05-03 |
| **(this)** | **state-sync** | **this PR** | **2026-05-13 11:45** |

10+ days since last on-slug merge.

---

## §4. Anti-targets

1. **Does not modify any Lean file.** `proofs/Proofs/Erdos1139Problem.lean`
   stays at 192 LOC, 16 theorems, 2 axioms, 0 sorries.
2. **Does not edit `meta.json` / gallery JSON.** Mechanic territory.
3. **Does not edit research JSON `currentState` / `phase` / `knownResults.open`.**
   Same; mechanic territory.
4. **Does not edit `knowledge.md` or `problem.md`.** They are not stale-bug
   targets in this session; state.md is the sole drift target.
5. **Does not attempt to discharge either axiom.** Both are load-bearing
   (Erdős conjecture: open; Hardy-Ramanujan: not in Mathlib).
6. **Does not propose a gallery-entry refactor.**

---

## §5. Files modified in this PR

1. **NEW:** `research/problems/erdos-1139/sessions/2026-05-13-state-sync-axiomatized.md` — this file
2. **MODIFIED:** `research/problems/erdos-1139/state.md` — sync Phase NEW→AXIOMATIZED, iter 1→6, fill Active Approach/Blockers/Next Action

No Lean changes. No gallery JSON. No `meta.json`. No JSON `currentState` /
`knowledge.md` / `problem.md`.

---

## §6. Future status

After this state-sync, the slug is at **stable "axiomatized" steady state**.
Future work surface is narrow:

- **Optional Mathlib upstream watch:** If a Hardy-Ramanujan-class asymptotic
  lands in `Mathlib.NumberTheory.PrimeCounting` (or similar), the
  `hardy_ramanujan_asymptotic` axiom can be replaced by a `theorem` derived
  from Mathlib. ETA: indeterminate (depends on Mathlib's PNT/sieve roadmap).
- **JSON drift-sync** (Mechanic): sync top-level `phase` / `currentState.phase`
  to `"AXIOMATIZED"`; clean `currentState.blockers` / `nextAction`.

The Erdős conjecture `erdos_1139` itself remains permanently axiomatized
(it's the open question; cannot be derived from anything weaker).
