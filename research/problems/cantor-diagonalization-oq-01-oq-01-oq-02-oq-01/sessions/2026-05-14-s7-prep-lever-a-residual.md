# S7 PREP — Lever A residual: delete parent's vacuous `True`-codomain axioms (axiom-reduction 6 → 4)

**Slug**: `cantor-diagonalization-oq-01-oq-01-oq-02-oq-01` (Easton 1970
converse: which cardinals can realize 2^ℵ₀?).
**Researcher**: researcher-8.
**Date**: 2026-05-14 ~23:25 UTC.
**Mode**: doc-only PREP (no Lean, no gallery JSON, no candidate-pool, no
`state.md`, no `meta.json`, no `knowledge.md` touch — only adds one new
session doc).
**Purpose**: Scope the "Lever A residual" refactor explicitly flagged in
PR #19112's body ("Followup Work Available" item 1). Bring slug axiom
count from 6 → 4 by deleting the parent file's two vacuous
`True`-codomain axioms `easton_permitted_realizable` and
`easton_consistency`, after PR #19112 lands their `_strong` siblings in
the Phase3b companion file with `ConsistencyOfContinuumValue` /
`ConsistencyOfContinuumFunction` codomains.

## §1 Pre-claim survey

### 1.1 PR landscape (slug-scoped)

`gh pr list -R rjwalters/lean-genius --search
"cantor-diagonalization-oq-01-oq-01-oq-02-oq-01 in:title" --state open`
returns four OPEN PRs at session start (2026-05-14 ~23:25 UTC):

| PR | Title | Created | Mergeable | Notes |
|---|---|---|---|---|
| #19112 | `S6 ACT — Phase-3b Lever A: ConsistencyOf predicates + strong-Easton axioms (build verified)` | 2026-05-14T19:50Z | MERGEABLE | researcher-8 (my prior session); +307/-49; new Phase3b file (173 LOC, 4 axioms + 5 theorems); Docker 3061 jobs clean. |
| #17169 | `S7 — not_permitted_aleph_zero (Part V, build pending)` | 2026-05-08 | CONFLICTING | Stale 6 days; superseded by Phase-3a-fix iteration. |
| #17137 | `S6 — Easton-function closure under pointwise binary max (build pending)` | 2026-05-08 | CONFLICTING | Stale 6 days. |
| #16936 | `S5 — Easton non-examples + lt_apply corollary` | 2026-05-08 | CONFLICTING | Stale 6 days. |

Only PR #19112 is active. The three stale CONFLICTING PRs from
2026-05-08 are pre-existing and unrelated to this PREP. (Cleanup
deferred to maintainer per state.md "Race note" convention used
elsewhere in this slug.)

### 1.2 PR #19112 summary (Phase-3b Lever A discharge)

Adds new file `proofs/Proofs/CantorDiagonalizationOQ01OQ01OQ02OQ01Phase3b.lean`
(173 LOC, namespace `CantorDiagOQ01OQ01OQ02OQ01`) containing:

- **2 new abstract predicates** (axioms with non-trivial codomain):
  - `ConsistencyOfContinuumValue : Cardinal.{0} → Prop`
  - `ConsistencyOfContinuumFunction : (Cardinal.{0} → Cardinal.{0}) → Prop`
- **2 new strong-Easton axioms** (the genuine mathematical content):
  - `easton_permitted_realizable_strong : ∀ κ, IsPermittedValue κ → ConsistencyOfContinuumValue κ`
  - `easton_consistency_strong : ∀ F, IsEastonFunction F → ConsistencyOfContinuumFunction F`
- **5 derived theorems** with non-trivial output type (callable content):
  - `consistencyOfContinuumFunction_continuum`
  - `consistencyOfContinuumValue_aleph_one` (CH model)
  - `consistencyOfContinuumValue_aleph_two` (PFA model)
  - `consistencyOfContinuumValue_aleph_succ`
  - `consistencyOfContinuumValue_unbounded`

The parent file `CantorDiagonalizationOQ01OQ01OQ02OQ01.lean` is
**unchanged by PR #19112** — only `proofs/Proofs.lean` gets a 1-line
import added.

**Net slug axiom count delta from PR #19112**: 2 → 6.

PR #19112's body honestly labels this as "deeper axiomatization, not
axiom reduction" and explicitly schedules the residual refactor as a
separate PR:

> "Lever A residual — refactor the parent's `easton_consistency` /
> `easton_permitted_realizable` to use the new predicates as codomain
> directly, eliminating the redundant `True`-codomain forms (would
> bring slug axiom count 6 → 4). Deferred from S6 to keep the parent's
> verified rest state untouched; should be a separate dedicated PR."

This PREP is that "separate dedicated PR" plan, doc-only stage.

### 1.3 Role doc priority alignment

`/.lean/roles/researcher.md` §"Axiom Elimination Priority":

> "Reducing axiom counts is more valuable than adding new theorems. A
> file with 100 theorems and 50 axioms is weaker than a file with 20
> theorems and 2 axioms. … Target: On any RICH problem, aim to
> eliminate at least 1 axiom per session."

This slug is RICH (knowledge score 43). The proposed Lever A residual
**eliminates 2 axioms** (slug 6 → 4) by recognizing that the parent's
2 vacuous `True`-codomain axioms have no mathematical content beyond
what their Phase3b `_strong` siblings carry. Deletion is the
zero-mathematical-content refactor; nothing is lost.

## §2 Parent-file analysis: current axiom locations

`proofs/Proofs/CantorDiagonalizationOQ01OQ01OQ02OQ01.lean` at
`origin/main` (HEAD `2afb1b79c0a`, 257 LOC, 7 theorems, 2 axioms, 2
defs, 0 sorries):

| Line range | Content | Refactor action |
|---|---|---|
| 193–215 | Part III header docstring (Easton consistency narrative) | **Retain** with minor rewrite: redirect reader to Phase3b file. |
| 217–224 | `easton_permitted_realizable` docstring | **Delete**. |
| 225–226 | `axiom easton_permitted_realizable : ∀ κ, IsPermittedValue κ → True` | **Delete**. |
| 228–236 | `easton_consistency` docstring | **Delete**. |
| 237–238 | `axiom easton_consistency : ∀ F, IsEastonFunction F → True` | **Delete**. |
| 240–243 | Part IV header (VERIFICATION) | **Retain**. |
| 245–253 | `#check @IsPermittedValue` etc. (9 checks for theorems/defs) | **Retain**. |
| 254 | `#check @easton_permitted_realizable` | **Delete** (the symbol no longer exists). |
| 255 | `#check @easton_consistency` | **Delete** (the symbol no longer exists). |

**Estimated parent-file delta**: −23 LOC (8 + 9 + 2 = 19 + the 4 LOC
of axiom-declaration headers and trailing blank lines).

The Part III header docstring (lines 193–215) currently introduces the
two vacuous axioms. A rewrite redirects the reader to Phase3b:

```
PART III: EASTON CONSISTENCY — AXIOMATIZED (PROOF NEEDS CLASS FORCING)
==========================================================================
Easton's 1970 consistency theorem is axiomatized in the Phase3b
companion file `CantorDiagonalizationOQ01OQ01OQ02OQ01Phase3b.lean`
under namespace `CantorDiagOQ01OQ01OQ02OQ01.{...}_strong`, with
non-trivial codomain `ConsistencyOfContinuumValue` /
`ConsistencyOfContinuumFunction`.

The two earlier vacuous `True`-codomain axioms in this file
(`easton_permitted_realizable`, `easton_consistency`, deleted in S7
Lever A residual) had no mathematical content beyond what the
Phase3b `_strong` siblings carry; they have been retired.

(Class-forcing infrastructure to discharge the strong axioms is a
future Phase-4 effort; see Phase3b file's docstring for the flypitch
roadmap.)
```

Net Part III shrinks from 23 LOC of intro + 22 LOC of axiom material
(45 LOC total) to ~12 LOC of intro pointing to Phase3b. Net parent
file: 257 LOC → ~234 LOC.

## §3 External-caller audit

Verified at session start via:

```bash
$ rg "easton_permitted_realizable|easton_consistency" \
      proofs/Proofs/ src/data/
```

**Lean callers**: 2 files match.

- `proofs/Proofs/CantorDiagonalizationOQ01OQ01OQ02OQ01.lean` — the
  definitions themselves (lines 225–226 and 237–238), and their
  `#check` directives (lines 254–255). All deletable.
- `proofs/Proofs/CantorDiagonalizationOQ01OQ01OQ02OQ03.lean:109` — has
  its **own** `theorem easton_consistency` in a *different namespace*
  (`CantorDiagOQ01OQ01OQ02OQ03`) with a different signature
  (`Ordinal.{0} → Cardinal.{0}` not `Cardinal.{0} → Cardinal.{0}`). Not
  a caller of `OQ01OQ01OQ02OQ01.easton_consistency`. No name collision
  because the namespaces are disjoint. Untouched by this refactor.

**Gallery / research JSON references** (5 files): all are documentation
strings naming the axioms, not Lean tactic calls. No proof obligations
break under deletion. Concrete locations:

- `src/data/research/problems/cantor-diagonalization-oq-01-oq-01-oq-02-oq-01.json`
  — `knownResults.proven` / `openQuestions` reference axiom names as
  narrative. The S7 ACT (post-refactor) updates these to refer to the
  Phase3b `_strong` versions instead.
- `src/data/proofs/cantor-diagonalization-oq-01-oq-01-oq-02-oq-03/meta.json`
  + `annotations.json` — reference the sibling slug's own
  `easton_consistency` theorem (in OQ-02-OQ-03 namespace), not
  the deleted OQ-02-OQ-01 axioms. Untouched.
- `src/data/proofs/cantor-diagonalization-oq-01-oq-01-oq-02-oq-01/meta.json`
  + `annotations.json` — currently documents `axiomCount: 2` and
  references the parent's two axioms. S7 ACT updates: `axiomCount: 0`
  (parent), with full slug axiom count moving from 6 → 4 via the
  Phase3b file.

**Verdict**: **0 functional callers** of the two parent axioms exist
outside the parent file itself. Deletion is fully safe; the only
follow-up edits are: parent file (S7 ACT direct edit), slug research
JSON (narrative rewrite), and gallery `meta.json` (`axiomCount` field
+ `assumptions` narrative).

## §4 Mathlib API verification — N/A

This refactor introduces no new Mathlib dependencies. The deleted
axioms have no Mathlib usage; the Phase3b `_strong` axioms (already
shipped by PR #19112, Docker-verified) carry their own narrow Mathlib
surface (`Cardinal.{0}`, `Cardinal.aleph`, `Cardinal.power`,
`Ordinal.{0}`, `Order.succ`).

No `gh api` SHA-pin verification is needed for this PREP.

## §5 Conflict-free certification

This PREP adds exactly one new file:

```
research/problems/cantor-diagonalization-oq-01-oq-01-oq-02-oq-01/sessions/2026-05-14-s7-prep-lever-a-residual.md
```

It does **not** touch:

- Any Lean file (no `proofs/Proofs/**`, no `proofs/Proofs.lean`).
- The parent file's `meta.json` or `annotations.json`.
- The slug research JSON (PR #19112 modifies `state.md` and
  `knowledge.md` and the JSON; refresh here would race).
- The slug `state.md` or `knowledge.md`.
- The sibling slug (`OQ-02-OQ-03`) files.
- Any candidate-pool file.

A git diff after this PREP should show exactly one new untracked file.

**Cross-check against PR #19112's file list** (per `gh pr view 19112
--json files`):

| Path | PR #19112 | This PREP | Overlap? |
|---|---|---|---|
| `proofs/Proofs.lean` | +1 import | — | No. |
| `proofs/Proofs/CantorDiagonalizationOQ01OQ01OQ02OQ01Phase3b.lean` (new) | +173 LOC | — | No. |
| `proofs/Proofs/CantorDiagonalizationOQ01OQ01OQ02OQ01.lean` (parent) | unchanged | — | No (this PREP touches no Lean). |
| `research/problems/cantor-diagonalization-oq-01-oq-01-oq-02-oq-01/state.md` | +64/-33 | — | No. |
| `research/problems/cantor-diagonalization-oq-01-oq-01-oq-02-oq-01/knowledge.md` | +55/-1 | — | No. |
| `src/data/research/problems/cantor-diagonalization-oq-01-oq-01-oq-02-oq-01.json` | +14/-15 | — | No. |
| `research/problems/.../sessions/2026-05-14-s7-prep-lever-a-residual.md` | — | new file | No (filename unique). |

Zero overlap. Both PRs can land in any order without conflict.

## §6 S7 ACT plan (post-#19112-merge)

### 6.1 Parent file edits (`CantorDiagonalizationOQ01OQ01OQ02OQ01.lean`)

1. **Lines 193–215** (Part III docstring): rewrite per §2 above — point
   to Phase3b for the genuine consistency axioms. ~12 LOC retained
   from the original 23.
2. **Lines 217–238** (the 2 axiom declarations + docstrings): delete
   entirely. ~22 LOC removed.
3. **Lines 254–255** (the 2 `#check` directives): delete. 2 LOC
   removed.

**Net parent file delta**: 257 LOC → ~234 LOC (−23 LOC).
Theorem count unchanged (7). Definition count unchanged (2).
**Axiom count: 2 → 0**. Sorries unchanged (0).

### 6.2 Gallery `meta.json` updates

```jsonc
// src/data/proofs/cantor-diagonalization-oq-01-oq-01-oq-02-oq-01/meta.json
{
  // ... unchanged fields ...
  "lineCount": 234,           // was 257
  "axiomCount": 0,            // was 2 — parent file is now axiom-free
  "theoremCount": 7,          // unchanged
  "status": "axiomatized",    // unchanged (Phase3b file carries 4 axioms)
  "badge": "axiom",           // unchanged
  // assumptions: rewrite to point to Phase3b's _strong axioms
}
```

**Important**: slug-level axiom count (which includes the Phase3b
companion file) is **4** post-refactor, not 0. The gallery
`additionalFiles` mechanism (used by `laws-of-large-numbers-oq-04`
for its bracketing companion) should be applied here too, so the
gallery entry reports the *full* slug-level count: parent 0 +
Phase3b 4 = **4 total**. Current `meta.json` does **not** yet have
an `additionalFiles` field for this slug; S7 ACT should add one
referencing the Phase3b file.

### 6.3 Slug research JSON updates

`src/data/research/problems/cantor-diagonalization-oq-01-oq-01-oq-02-oq-01.json`:

- `knownResults.proven`: rewrite entries referencing the deleted
  `easton_permitted_realizable` / `easton_consistency` axioms to
  reference the Phase3b `_strong` siblings.
- `knowledge.progressSummary`: append a paragraph documenting the S7
  Lever A residual refactor (parent file now axiom-free; Phase3b
  carries the 4 axioms; slug axiom count 6 → 4).
- `leanFiles`: update `axiomCount` for the parent file (2 → 0) and
  confirm the Phase3b file entry (added by PR #19112) reports
  `axiomCount: 4`.

### 6.4 state.md update

- Phase: `AXIOMATIZED — Phase-3a-fix COMPLETE; Phase-3b Lever A
  shipped (#19112); Lever A residual shipped (this PR)` (or similar).
- Iteration: 6 → 7.
- New session log entry: S7 Lever A residual.
- Update "What is axiomatized" table to remove the 2 parent vacuous
  axioms and report the 4 Phase3b axioms instead.

### 6.5 Build verification

Re-build the parent file after deletion:

```bash
./proofs/scripts/docker-build.sh Proofs.CantorDiagonalizationOQ01OQ01OQ02OQ01
```

Expected outcome: clean (the deletions are pure removals; no new
elaboration obligations introduced). PR #19112's Phase3b file
Docker-verified at 3061 jobs; the parent file refactor should add
~10 jobs (the removed `#check` directives skipped) and remain clean.

## §7 Sequencing

### Option A: Wait for PR #19112 to merge, then S7 ACT off `main`

- **Pros**: cleanest. Phase3b file is on `main` so the parent's Part
  III docstring rewrite can confidently reference it. No overlay
  bookkeeping.
- **Cons**: serialization delay.
- **Recommended**: yes — PR #19112 is MERGEABLE and Docker-clean.

### Option B: Mechanic-PR overlay (apply #19112 transiently for build verification)

Per `feedback_researcher_mechanic_pr_overlay_build_verify_pattern.md`:
overlay #19112's diff, apply parent edits, Docker-build, revert
overlay, commit only the parent edits + this PREP.

- **Pros**: same-day S7 ACT.
- **Cons**: re-rebase needed if #19112 is modified during review.
  Build of the parent file (which transitively imports OQ01,
  OQ01OQ01, OQ01OQ01OQ02) is expensive (~3061+ jobs).
- **Recommended**: only if Option A stalls > 24h.

### Option C: Refactor parent axioms as theorems (instead of deletion)

Alternative: keep `easton_permitted_realizable` / `easton_consistency`
as named symbols, but prove them as theorems with body `trivial`
(since the `True` codomain is trivially inhabited). Slug axiom count
delta: still 6 → 4 (parent's 2 become theorems, Phase3b's 4 unchanged).

- **Pros**: backward-compatible — any future code that names the
  parent's symbols still resolves.
- **Cons**: introduces 2 trivially-`trivial` theorems that have no
  callers (per §3 audit, current callers are 0). Cosmetic dead code.
- **Recommended**: no. The audit confirms 0 callers; deletion is
  cleaner.

**Selection**: **Option A** for S7 ACT. ETA: ≤ 30 minutes once
#19112 merges (~−23 LOC parent + meta.json + slug JSON + state.md).

## §8 Honest contribution boundary

What this PREP **does**:

- Verifies (§3) that the parent file's 2 vacuous `True`-codomain
  axioms have **0 external callers** in the Lean source tree at HEAD.
- Specifies (§2) the exact line ranges to delete (217–238 and
  254–255) and the docstring lines to rewrite (193–215).
- Specifies (§6) the gallery / JSON / state.md updates that S7 ACT
  needs to bundle with the Lean edit.
- Confirms (§5) full conflict-freedom with PR #19112 — both PRs can
  land in any order; the cross-file path table shows zero overlap.
- Documents (§1.3) alignment with the role doc's axiom-elimination
  priority (slug axiom count 6 → 4).

What this PREP **does NOT** do:

- It does not modify any Lean, JSON, state.md, knowledge.md,
  meta.json, or candidate-pool file.
- It does not attempt to discharge the Phase3b `_strong` axioms
  (`easton_permitted_realizable_strong` / `easton_consistency_strong`)
  themselves — those discharge requires class-forcing infrastructure
  not yet in Mathlib (deferred to Phase-4 flypitch port).
- It does not bridge the slug with the sibling
  `cantor-diagonalization-oq-01-oq-01-oq-02-oq-03` (Lever B). That
  remains a separate Phase-3b-extension session.
- It does not address the three stale CONFLICTING PRs from 2026-05-08
  (#16936, #17137, #17169). Maintainer cleanup deferred.

## §9 Acceptance criteria for the PREP doc itself

- [x] Pre-claim survey + PR landscape table (§1.1).
- [x] PR #19112 summary recapped (§1.2).
- [x] Parent-file line-range plan with retain/delete verdicts (§2).
- [x] External-caller audit with concrete `rg` query and 0-functional-
      caller verdict (§3).
- [x] Conflict-free certification with cross-file path table vs
      PR #19112 (§5).
- [x] S7 ACT plan: parent Lean edit + meta.json + slug JSON + state.md
      updates (§6).
- [x] Sequencing options + recommendation (§7).
- [x] Honest scope boundary explicit (§8): refactor is axiom-count
      cosmetics, not mathematical discharge of class forcing.

## §10 Next action

**S7 ACT — Lever A residual**, post-#19112-merge. Estimated session
length: ~30 minutes. Estimated PR delta:

- `proofs/Proofs/CantorDiagonalizationOQ01OQ01OQ02OQ01.lean`: −23 LOC
  (delete 2 axioms + 2 `#check` + rewrite Part III docstring).
- `src/data/proofs/cantor-diagonalization-oq-01-oq-01-oq-02-oq-01/meta.json`:
  `lineCount` 257 → 234; `axiomCount` 2 → 0 (parent file);
  `assumptions` rewrite; add `additionalFiles` field if not present.
- `src/data/research/problems/cantor-diagonalization-oq-01-oq-01-oq-02-oq-01.json`:
  `knownResults` + `knowledge.progressSummary` rewrites.
- `research/problems/cantor-diagonalization-oq-01-oq-01-oq-02-oq-01/state.md`:
  S7 session log + iteration bump + axiomatized-table refresh.

**Slug axiom count after S7 ACT**: parent 0 + Phase3b 4 = **4 total**
(down from the 6 introduced by PR #19112 merge, and ultimately back to
the original parent-file count of 2 having been re-allocated +
strengthened, per S6 PR #19112's "deeper axiomatization" framing).

The slug enters a **stable axiomatized rest state** with all
axiomatization having non-trivial mathematical content (no `True`
codomains remain anywhere in the slug). Future Phase-4 (flypitch
class-forcing port) is the only path to genuine discharge.
