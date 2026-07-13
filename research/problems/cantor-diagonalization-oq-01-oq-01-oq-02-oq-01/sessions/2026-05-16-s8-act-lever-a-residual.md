# S8 ACT — Lever A residual: delete parent's vacuous `True`-codomain axioms (slug axiom count 6 → 4)

**Slug**: `cantor-diagonalization-oq-01-oq-01-oq-02-oq-01` (Easton 1970
converse: which cardinals can realize 2^ℵ₀?).
**Researcher**: researcher-5.
**Date**: 2026-05-16 ~04:30 UTC.
**Mode**: ACT (executes the doc-only plan from S7 PREP / PR #19174).
**Purpose**: Discharge the Lever A residual explicitly scoped by
PR #19112 ("Lever A residual — refactor parent's True-codomain axioms
to use ConsistencyOf* directly, eliminating redundant True-codomain
forms (would bring slug axiom count 6 → 4)") and re-scoped at file
level by S7 PREP. Concretely: delete `axiom easton_permitted_realizable`
and `axiom easton_consistency` from the parent file, remove their two
`#check` directives, rewrite Part III docstring as a pointer to the
Phase3b companion.

## §1 Pre-claim state

- S6 ACT (PR #19112) merged 2026-05-15T22:58:47Z. Phase3b sibling
  shipped with `_strong` axioms carrying genuine `ConsistencyOf*`
  codomain.
- S7 PREP (PR #19174) merged earlier (doc-only scoping for S8 ACT).
- State.md iter 6, currentState.nextAction names "Lever A residual"
  as the first deferred item.
- Parent file at SHA-pre-S8: 257 LOC, 7 theorems, 2 defs, 2 axioms
  (both `True`-codomain), 0 sorries.
- Phase3b sibling: 173 LOC, 5 theorems, 4 axioms (2 abstract preds +
  2 strong-Easton claims), 0 sorries.
- Slug-level axiom count pre-S8: 2 (parent) + 4 (Phase3b) = 6.

S7 PREP §3 verified at pre-S8 time that:
- `rg "easton_permitted_realizable|easton_consistency" proofs/Proofs/`
  returns only the parent file (definitions + `#check`) and
  the sibling OQ-02-OQ-03 file (its own theorem in a different
  namespace with a different signature). 0 functional Lean callers
  outside the parent file itself.
- Gallery / research JSON references are documentation strings, not
  proof obligations.
- Verdict: deletion is fully safe.

## §2 What S8 ACT changed

### 2.1 Parent file (`CantorDiagonalizationOQ01OQ01OQ02OQ01.lean`)

| Lines (pre-S8) | Content | Action |
|---------------|---------|--------|
| 193–215 | Part III docstring (intro to the 2 axioms) | Rewrote to 12-line pointer to Phase3b |
| 217–224 | `easton_permitted_realizable` axiom docstring | **Deleted** |
| 225–226 | `axiom easton_permitted_realizable : ∀ κ, IsPermittedValue κ → True` | **Deleted** |
| 228–236 | `easton_consistency` axiom docstring | **Deleted** |
| 237–238 | `axiom easton_consistency : ∀ F, IsEastonFunction F → True` | **Deleted** |
| 254 | `#check @easton_permitted_realizable` | **Deleted** |
| 255 | `#check @easton_consistency` | **Deleted** |

**Net delta**: 257 LOC → 230 LOC (−27 LOC). Theorems: 7 (unchanged).
Definitions: 2 (unchanged). Axioms: 2 → 0. Sorries: 0 (unchanged).

### 2.2 Gallery `meta.json`

`src/data/proofs/cantor-diagonalization-oq-01-oq-01-oq-02-oq-01/meta.json`:

- `meta.axiomCount`: 2 → 0
- `meta.lineCount`: 257 → 230
- `meta.assumptions`: rewrote to reflect the parent-file refactor
  (parent now axiom-free; the 4 axioms live in the Phase3b companion).
- `sections[easton-axioms].id`: renamed to `easton-axioms-pointer`,
  title updated, summary rewritten to describe the pointer narrative.
- `sections[verification].startLine`/`endLine`: 234/251 → 213/230;
  summary updated to remove mention of the deleted axioms / #check.
- `leanFile.lineCount`: 257 → 230, `leanFile.axiomCount`: 2 → 0.

Note: did NOT add an `additionalFiles` field for the Phase3b
companion this PR. The S7 PREP §6.2 raised this as a possible
addition for gallery completeness; deferred to a future cosmetic-PR
so this PR stays narrowly scoped.

### 2.3 Slug research JSON

`src/data/research/problems/cantor-diagonalization-oq-01-oq-01-oq-02-oq-01.json`:

- `currentState.iteration`: 6 → 7
- `currentState.since`: 2026-05-16T04:30:00.000Z
- `currentState.focus` + `currentState.nextAction`: rewrote to reflect
  S8 ACT shipped (parent file axiom-free; Lever B/C remain).
- `knowledge.progressSummary`: prepended S8 paragraph (parent refactor,
  slug axiom count 6 → 4).
- `knowledge.builtItems`: appended 5 S8 entries (each deletion + the
  docstring rewrite + the file-metric summary).
- `knowledge.insights`: appended 3 S8 entries (S7 PREP audit confirmed
  at exec time; slug axiom-content quality improvement; Lever A
  two-step pattern).
- `knowledge.nextSteps`: replaced (Lever B, Lever C, optional OQ-03
  sorry-investigation as the residual frontier).

### 2.4 state.md

- Phase header: AXIOMATIZED — Lever A residual SHIPPED.
- Iteration: 6 → 7. (S7 PREP doc-only is included in the session
  history table as part of the audit trail; per role convention, PREP
  iterations bump only narratively, and the ACT after PREP gets the
  next integer.)
- Status Summary table: parent file axiomCount 2 → 0, lineCount
  257 → 230; added note "Slug-level axiom count: 4 (all in Phase3b;
  parent is now axiom-free)".
- "What is axiomatized" parent block: replaced two-axiom table with
  a one-line NONE note.
- Current Focus / Active Approach: rewrote to reflect S8 shipped.
- Research Levers: added "Lever A residual SHIPPED S8 (2026-05-16)"
  subsection alongside the prior "Lever A SHIPPED S6".
- Next Action: rewrote.
- Attempt Counts: 6 → 7 iterations, 2 → 3 approaches.
- Session History table: appended S7 PREP row + S8 ACT row.

### 2.5 Files NOT touched

- `proofs/Proofs.lean` (no import-table change; the parent file is
  already in the import list).
- `proofs/Proofs/CantorDiagonalizationOQ01OQ01OQ02OQ01Phase3b.lean`
  (unchanged; PR #19112 is the only authority on this file's content).
- `proofs/Proofs/CantorDiagonalizationOQ01OQ01OQ02OQ03.lean` (sibling,
  unrelated namespace + signature; per S7 PREP §3 audit).
- `src/data/proofs/cantor-diagonalization-oq-01-oq-01-oq-02-oq-01/annotations.json`
  + `index.ts` (annotation line ranges may need a cosmetic refresh,
  but that's a mechanic-style sync, not part of this slim refactor PR).
- Sibling slug files (OQ-02-OQ-03, OQ-02-OQ-01-OQ-01 etc.).
- Candidate pool file (`.lean/state/candidate-pool.json`); status
  remains `in-progress` — claim release happens via the standard script.
- `research/problems/cantor-diagonalization-oq-01-oq-01-oq-02-oq-01/knowledge.md`
  (relies on existing summary; the slug research JSON's
  `knowledge.progressSummary` is the authoritative changelog).

## §3 Mathlib API verification — N/A

This refactor introduces no new Mathlib dependencies. The deletions
remove imports of `True` (built-in propositional truth) which has no
Mathlib dependency. The Phase3b file (unchanged by this PR) carries
the only remaining Mathlib usage relevant to the axiomatization.

No `gh api` SHA-pin verification needed.

## §4 Build verification — DEFERRED (host-level Docker daemon I/O error)

```bash
./proofs/scripts/docker-build.sh Proofs.CantorDiagonalizationOQ01OQ01OQ02OQ01
```

Expected outcome: clean. The deletions remove elaboration obligations;
the rewritten docstring is a pure comment block. The Phase3b file's
build remains untouched.

**Attempted 4 times** (2026-05-16 ~04:48–05:03 UTC, builds bm1wd499v,
b9jhcq3wu, b1amhd0eo, b5zsyn2bm). Each failed at the Docker image
setup step (BEFORE any Lean compilation) due to a host-level Docker
daemon I/O error:

```
ERROR: failed to build: failed to solve: write
  /var/lib/desktop-containerd/daemon/io.containerd.metadata.v1.bolt/meta.db:
  input/output error
```

Root cause: host disk is at **100% capacity** (`df -h /System/Volumes/Data`
shows 890Gi used / 140Mi available on a 926Gi disk), corrupting
Docker's containerd metadata DB. Confirmed via `docker system df`
returning blob-fetch I/O errors. This affects ALL concurrent
researcher agents on this host (researcher-1, researcher-3 builds
were running in parallel and also affected).

**Safety justification for shipping with build-pending caveat**:

1. S8 is **pure deletion** — removes 2 axioms (no proof obligations),
   2 `#check` directives (no proof obligations), and rewrites a
   docstring (parser-only). No new theorems, no new tactic blocks,
   no new imports.
2. S6 ACT (#19112) verified the parent file structure was Lean-clean
   at 3061 jobs **before** the deletions. Deletions cannot break the
   non-deleted portion.
3. Phase3b companion file (which now carries all 4 slug-level axioms)
   was Docker-verified clean at S6 ACT and is **unchanged** by S8.
4. No callers of the deleted symbols exist in `proofs/Proofs/`
   (S7 PREP §3 audit confirmed via `rg`, re-confirmed at S8 exec time).
5. The slug research JSON / gallery `meta.json` updates are
   data-only; they don't affect Lean compilation.

**Follow-up**: A subsequent BUILD-VERIFY iteration (S9) can run the
Docker build once the host recovers (free up disk + restart Docker).
This pattern is consistent with the slug's existing "build pending"
PRs (#17137, #17169 from 2026-05-08) and the auditor's standard
process for catching deferred BUILD-VERIFY items.

## §5 Honest scope

What this PR **does**:

- Discharges the Lever A residual explicitly scoped by PR #19112 and
  PR #19174 (S7 PREP).
- Brings slug axiom count from 6 to 4 by deleting 2 vacuous
  `True`-codomain axioms.
- Leaves the slug in a clean axiomatized rest state with all 4
  remaining axioms carrying non-trivial mathematical content.

What this PR **does NOT** do:

- Does not attempt to discharge the Phase3b `_strong` axioms
  themselves (those require class forcing — Phase-4 / flypitch port).
- Does not bridge the slug with sibling OQ-02-OQ-03 (Lever B).
- Does not write the flypitch-port scoping doc (Lever C).
- Does not touch annotations.json line ranges (mechanic-style cleanup).
- Does not address the three stale CONFLICTING PRs from 2026-05-08
  (#16936, #17137, #17169 — maintainer cleanup deferred).

## §6 Acceptance criteria

- [x] Parent file `axiom easton_permitted_realizable` removed.
- [x] Parent file `axiom easton_consistency` removed.
- [x] Parent file `#check @easton_permitted_realizable` removed.
- [x] Parent file `#check @easton_consistency` removed.
- [x] Parent file Part III docstring rewritten as pointer to Phase3b.
- [x] Parent file `axiomCount` (per `grep -c "^axiom "`): 0.
- [x] Gallery `meta.json` `axiomCount` / `lineCount` synced.
- [x] Slug research JSON `currentState.iteration` bumped 6 → 7.
- [x] State.md session history table appended with S7 + S8 rows.
- [x] Session memo (this file).
- [ ] Build verification (Docker — DEFERRED to S9, host disk full + Docker containerd meta.db I/O corrupt; see §4).

## §7 Next action after S8 merges

- **Lever B** (bridge with sibling OQ-02-OQ-03): single-session
  effort to add a `…Bridge.lean` file proving the two-sided
  characterization `easton_iff_permitted`. Risk: low (Lean-internal
  cross-reference). Forward direction from sibling-OQ-03's exclusions;
  reverse from Phase3b's `easton_permitted_realizable_strong`.
  Expected delta: +~50 LOC new file; no parent file edits.
- **Lever C** (flypitch-port scoping doc): research-track multi-session.
  Write `research/phase-4-flypitch-scoping.md` listing the Mathlib
  gaps a Lean-4 flypitch port would need to fill. Closer to literature
  review than research output, but would unblock the entire
  "discharge by genuine forcing" path.
