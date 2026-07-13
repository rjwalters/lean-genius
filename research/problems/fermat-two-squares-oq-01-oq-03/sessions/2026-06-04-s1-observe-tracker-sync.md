# S1 OBSERVE tracker-sync 2026-06-04 — bring tracker into alignment with reality

**Researcher**: researcher-1 (claim `researcher-1752`, this cycle)
**Mode**: S1 OBSERVE — tracker-sync only; doc-only
**Phase target**: RESEARCH-COMPLETE
**Elapsed since previous tracker update**: 29 days (JSON
`lastUpdate: 2026-05-05T02:57:44.801Z` → today)

## What this iteration is, and what it isn't

This is **NOT** new research. The slug's Lean ship is from
2026-05-06 (PR #16124, 357 LOC, 15 theorems, 1 axiom
`hurwitz_euclidean`, 0 sorries) and the gallery entry has been
fully populated since then with multiple mechanic/auditor/enricher
PRs (full list in `problem.md` References).

This iteration is a **tracker-sync** — it creates the missing
`problem.md` and `state.md` so the slug's research-pool entry
reflects reality. The discrepancy made the claim system keep
selecting this slug as a "fresh" research target when in fact the
work is done.

## Drift inventory at claim time

| Surface | Tracker said | Reality |
|:---|:---|:---|
| `currentState.phase` | `NEW` | shipped (since 2026-05-06) |
| `currentState.iteration` | `1` | `2` (original ship + this) |
| `lastUpdate` | `2026-05-05T02:57:44.801Z` | `2026-06-04T18:00Z` |
| `currentState.focus` | "Initial exploration of the problem." | RESEARCH-COMPLETE |
| `problem.md` | not present | created in S1 OBSERVE |
| `state.md` | not present | created in S1 OBSERVE (this file's sibling) |
| `sessions/` | empty | this memo |
| Lean source | n/a | 357 LOC, 15 theorems, 1 axiom, 0 sorries |
| Gallery `meta.json` | n/a | `status: axiomatized`, `badge: axiom` |

(The meta.json `theoremCount: 18` vs. file's `15` is a separate
meta drift — mechanic/auditor scope, not addressed here.)

## What changed in this iteration

**Created:**

- `research/problems/fermat-two-squares-oq-01-oq-03/problem.md`
- `research/problems/fermat-two-squares-oq-01-oq-03/state.md`
- `research/problems/fermat-two-squares-oq-01-oq-03/sessions/2026-06-04-s1-observe-tracker-sync.md`
  (this file)

**Modified:**

- `src/data/research/problems/fermat-two-squares-oq-01-oq-03.json`
  — phase NEW → ACT (top-level); currentState.phase NEW →
  RESEARCH-COMPLETE; iteration 1 → 2; lastUpdate refreshed; focus
  / nextAction / attemptCounts rewritten; knowledge.progressSummary
  populated; knowledge.builtItems[] populated;
  knowledge.nextSteps[] populated with the single forward item
  (axiom discharge routed as fresh sibling slug).

**NOT touched (and why):**

- Lean source `proofs/Proofs/FermatTwoSquaresOQ01OQ03.lean` — no
  semantic change; the file is unchanged in this iteration.
- Gallery `meta.json` / `annotations.json` — mechanic/auditor
  scope; the theoremCount 18 vs. 15 drift is documented in
  state.md § Key Risks but not addressed here.
- `knowledge.md` (this dir) — accurate at its 2026-05-06 ship
  time; the new `problem.md` and `state.md` provide the
  forward-looking layer.
- Sibling slugs — out-of-scope.

## Forward item

**Discharge `hurwitz_euclidean` axiom.** The covering-radius
argument for `D₄` (`√2/2 < 1`) is classical (Hurwitz 1896) but
requires Mathlib infrastructure that doesn't currently exist at
the convenience level needed. The proper routing is a **fresh
sibling slug**, not a continuation of this slug. Suggested next-id:
`fermat-two-squares-oq-01-oq-03-oq-02` (the `-oq-01`
great-grandchild slot is already in use).

## When (if ever) to ship S2

A thin S2 STATE-SYNC tick on this slug would be appropriate when:

- A mechanic PR fixes the `meta.json` `theoremCount` 18 vs. file
  `15` drift (S2 absorbs the cleared drift); or
- Someone creates the fresh sibling slug for axiom discharge (S2
  cross-references it); or
- A material build-drift event affects this file.

Absent any of the above, the slug should be allowed to remain at
S1's RESEARCH-COMPLETE posture indefinitely.
