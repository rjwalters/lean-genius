# Current State

**Phase**: RESEARCH-COMPLETE — S1 OBSERVE tracker-sync 2026-06-04
(researcher-1, claim `researcher-1752`); brings the slug's tracker
into alignment with reality after a 29-day quiet window since
PR #16124 (original 2026-05-06 ship); only forward item is
`hurwitz_euclidean` axiom discharge, which is out-of-scope for
this slug and best routed as a fresh sibling slug.
**Since**: 2026-05-06 (PR #16124 merge; original research ship time)
**Last Updated**: 2026-06-04 (S1 OBSERVE tracker-sync; doc-only;
creates `problem.md` + `state.md` + session memo; refreshes JSON
phase NEW (iter 1, 2026-05-05) → RESEARCH-COMPLETE (iter 2,
2026-06-04))
**Iteration**: 2 (original 2026-05-06 ship counted as iter 1 per
JSON; this S1 OBSERVE-sync increments to 2)

## S1 OBSERVE tracker-sync 2026-06-04 (researcher-1)

**Mode:** S1 OBSERVE — tracker-sync only; doc-only.

**Why this iteration is needed.** Claiming this slug surfaced a
significant tracker / reality drift:

- `knowledge.md` (2026-05-06) declares the slug COMPLETE with the
  Lean file shipped at 265 LOC.
- Lean file `proofs/Proofs/FermatTwoSquaresOQ01OQ03.lean` exists
  today at 357 LOC, 15 theorems (`grep -cE '^(theorem|lemma) '`),
  1 axiom (`hurwitz_euclidean` at line 206), 0 sorries.
- Gallery entry `src/data/proofs/fermat-two-squares-oq-01-oq-03/`
  is fully populated (meta.json + annotations.json), status
  `axiomatized` / badge `axiom`.
- Multiple meta-fix PRs and an enrichment PR have shipped against
  this slug since 2026-05-06 (full list in `problem.md`
  References).
- BUT the research tracker JSON
  `src/data/research/problems/fermat-two-squares-oq-01-oq-03.json`
  still records `phase: NEW`, `status: active`, `iteration: 1`,
  `lastUpdate: 2026-05-05T02:57:44.801Z`, and
  `currentState.focus: "Initial exploration of the problem."` —
  i.e., the tracker was created before the original 2026-05-06
  research ship and never refreshed.
- AND no `problem.md` or `state.md` existed in this dir — only
  `knowledge.md`.

This tracker-reality drift causes the claim system to keep
selecting this slug as a "fresh" research target, when in fact the
substantive work is done and the only forward item (axiom
discharge) is a significantly larger secondary project.

S1 OBSERVE fixes this by:

1. **Creating `problem.md`** with a clean formal-statement-+-
   decomposition layout. The decomposition reflects reality
   (single S1 OBSERVE tracker-sync now; future `hurwitz_euclidean`
   discharge explicitly enumerated as out-of-scope).
2. **Creating `state.md`** (this file) so future researcher claims
   land on the RESEARCH-COMPLETE phase rather than re-doing the
   work.
3. **Creating session memo** at
   `sessions/2026-06-04-s1-observe-tracker-sync.md`.
4. **Refreshing the JSON tracker**:
   - `phase`: `NEW` → `ACT` (top-level — the slug shipped its
     act); `currentState.phase`: `NEW` → `RESEARCH-COMPLETE`;
   - `currentState.iteration`: 1 → 2;
   - `currentState.focus`: rewritten to describe slug-shipped
     status and forward `hurwitz_euclidean` axiom-discharge item;
   - `currentState.nextAction`: rewritten to declare no further
     researcher session anticipated and route axiom-discharge as a
     fresh sibling slug;
   - `currentState.attemptCounts`: total 1 → 2; currentApproach 1
     → 1 (unchanged — same approach); approachesTried 0 → 1;
   - `lastUpdate`: 2026-05-05T02:57:44.801Z → 2026-06-04T18:00Z;
   - `knowledge.progressSummary` rewritten;
   - `knowledge.builtItems[]` populated;
   - `knowledge.nextSteps[]` populated with the single forward
     item.

**Negative confirmations:**

- Lean file unchanged today vs. its last semantic touch (the
  cross-slug commit `ecb47b35601` only ran a barrel-import sweep,
  not a semantic edit).
- Gallery `meta.json` reports 18 theorems vs. file content `15` —
  meta.json drift is mechanic/auditor scope, not researcher-tracker
  scope; not touched in this iteration.
- Build status: PR #21983 (2026-06-01) shipped 3062/3062 jobs
  clean against the same Mathlib pin (sibling
  `infinitude-primes-4k1-oq-01`); this slug's file builds against
  the same pin chain. No build-pending flag carried.

**Forward item (out-of-scope for this slug):**

Discharge `hurwitz_euclidean` axiom via the `D₄` root-lattice
covering-radius argument. Requires Mathlib infrastructure
(`EuclideanLattice` / covering-radius lemmas for root lattices)
that does not currently exist at the convenience level needed.
The right routing is a **fresh sibling slug**, not a continuation
of this one — the scope is multi-session and qualitatively
different (lattice geometry vs. quaternion algebra).

**S1 OBSERVE ship scope (4 files):**

1. `research/problems/fermat-two-squares-oq-01-oq-03/problem.md`
   (NEW)
2. `research/problems/fermat-two-squares-oq-01-oq-03/state.md`
   (NEW — this file)
3. `research/problems/fermat-two-squares-oq-01-oq-03/sessions/2026-06-04-s1-observe-tracker-sync.md`
   (NEW)
4. `src/data/research/problems/fermat-two-squares-oq-01-oq-03.json`
   (MODIFIED — see refresh list above)

**NOT touched:** Lean source, gallery `meta.json` /
`annotations.json` (mechanic/auditor scope), sibling slugs,
`knowledge.md` (already accurate at its 2026-05-06 ship time;
prepending an S1 OBSERVE note would be the next-thinner-still
motion if subsequent confusion arises, but is unnecessary now).

## Current Focus

S1 OBSERVE tracker-sync only. No active research.

## Active Approach

N/A — slug is RESEARCH-COMPLETE for this OQ. The original approach
shipped via PR #16124 was: define `HurwitzQuat` as a structure with
the equal-parity condition, prove norm multiplicativity via
embedding into Mathlib's `Quaternion ℚ`, prove
`hurwitzOmega_normSq` (`ω` is a unit), prove
`lipschitzToHurwitz_normSq` (norm-preserving Lipschitz → Hurwitz
embedding), and use the `hurwitz_euclidean` axiom to obtain the
four-square representation for Lipschitz-type Hurwitz elements.

## Blockers

None for this slug's RESEARCH-COMPLETE posture. The
`hurwitz_euclidean` axiom-discharge is a forward project requiring
fresh slug creation, not a slug-level blocker.

## Next Action

**No further researcher session anticipated for this slug.** The
appropriate motion at next claim is either:

1. **Thin S2 STATE-SYNC tick** absorbing any subsequent
   mechanic/auditor/enricher PR (e.g., the meta.json `theoremCount`
   18 vs. file `15` drift, when fixed); or
2. **No action** — the slug should not be re-claimed for further
   work unless a material event occurs.

The `hurwitz_euclidean` axiom-discharge forward item should be
routed as a **fresh sibling slug** (suggested id:
`fermat-two-squares-oq-01-oq-03-oq-02` or similar — the existing
`-oq-01` great-grandchild is already taken). That fresh slug would
need its own S1 OBSERVE / problem.md decomposition for the `D₄`
covering-radius argument and `EuclideanLattice` Mathlib
infrastructure.

## Decomposition Plan

| Session | Phase | Deliverable | Lines | Status |
|---|---|---|---|---|
| (Original) | OBSERVE → ACT | Full slug ship: `HurwitzQuat`, 15 theorems, 1 axiom, gallery entry | 357 Lean + meta.json + annotations | **MERGED #16124 (researcher-4, 2026-05-06)** |
| S1 OBSERVE tracker-sync | OBSERVE-SYNC | `problem.md` + `state.md` + session memo + JSON refresh | 0 Lean (~600 MD) | **this PR (researcher-1)** |
| (Out-of-scope) Future axiom discharge | — | Discharge `hurwitz_euclidean` via `D₄` covering-radius — routed as fresh sibling slug | TBD | not planned here |

## Attempt Counts

- Total attempts: 2 (Original 2026-05-06 ACT ship; this S1 OBSERVE
  tracker-sync)
- Current approach attempts: 1 (Hurwitz / `D₄*` lattice route via
  axiom — single approach across all attempts)
- Approaches tried:
  - Hurwitz quaternion route with `hurwitz_euclidean` axiomatized
    (Original 2026-05-06; researcher-4 per branch
    `feature/researcher-4-fermat-hurwitz-oq03`)

## Key Risks

1. **`hurwitz_euclidean` axiom discharge perceived as in-scope.**
   Future researchers may claim this slug expecting to discharge
   the axiom. Mitigation: state.md and problem.md both explicitly
   route this as a fresh sibling slug.
2. **Meta.json `theoremCount` drift (18 in meta vs. 15 in file).**
   Mechanic/auditor scope; documented here for completeness but not
   addressed in this iteration. Any researcher claim should not
   waste effort on meta.json counters — that's mechanic territory.
3. **Mathlib pin drift.** The Lean file imports against the
   project's Mathlib pin. The sibling slug `infinitude-primes-4k1-
   oq-01` shipped 3062/3062 jobs clean on the same pin as recently
   as 2026-06-01 (PR #21983), so chain-build is verified GREEN for
   this surface as of S1 OBSERVE entry.

## References

- See `problem.md` § References for the full PR / Mathlib / cross-slug catalog.
- Session memo for this iteration:
  `sessions/2026-06-04-s1-observe-tracker-sync.md`.
- Knowledge base at original ship time: `knowledge.md` (this dir).
