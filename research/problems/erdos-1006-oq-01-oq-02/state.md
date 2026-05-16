# Research State: erdos-1006-oq-01-oq-02

## Current State
**Phase**: OBSERVE (S1 OBSERVE bootstrap; slug previously instrumented only via JSON and knowledge.md; file at 0 sorries / 2 axioms / 256 LOC)
**Path**: full
**Since**: 2026-05-16T22:05:00Z
**Iteration**: 1
**Last Updated**: 2026-05-16T22:05:00Z

## Current Focus (S1 OBSERVE, 2026-05-16, researcher-3)

S1 OBSERVE (researcher-3, 2026-05-16, this PR — doc-only bootstrap +
drift fix): The slug previously lacked state.md, problem.md, and a
sessions/ directory entirely. The canonical research JSON was missing
top-level `slug`, `title`, `phase`, `status`, `currentState`, `started`,
`tags`, and `lastUpdate` fields. This S1 OBSERVE creates the missing
infrastructure (NEW state.md + problem.md + sessions/ + 8 missing
top-level JSON fields) and fixes drift in the existing JSON `knowledge`
and `leanFiles[]` subsets:

1. **`leanFiles[1].lineCount`** 257 → **256** (matches host
   `wc -l proofs/Proofs/Erdos1006OQ01OQ02.lean`).
2. **`knowledge.progressSummary`** said "10 theorems (was 7) ... 261
   lines"; both numbers are pre-#15112 stale. Refreshed to "9 theorems
   ... 256 lines".
3. **`knowledge.builtItems[6/7/8]`** line refs `213/224/256` →
   **`208/219/251`** (shifted by 5 lines after #15112 removed the
   `True` stub).
4. **`knowledge.nextSteps[0]`** "Run docker build to verify Lean file
   compiles with 0 sorries" — preserved, but a clarifying note added
   that the parent gallery slug `erdos-1006` is the build-bearing entry.

**File status verified at session start (`wc -l` + `grep -cE` host-side)**:

| Path | LOC | thm | axiom | def | sorry |
|---|---|---|---|---|---|
| `proofs/Proofs/Erdos1006OQ01OQ02.lean` | 256 | 9 | 2 | 4 | 0 |

The 2 axioms are intentional:
- `comparability_recognition_in_p` (line 159) — Golumbic-classical
  "comparability graph recognition is in P", stated as axiom for
  compactness.
- `cover_graph_recognition_in_p` (line 176) — **the open question**
  itself, stated as axiom so the file type-checks while the
  mathematical question remains open. **Not a defect**; this is the
  load-bearing problem statement.

**Mathlib pin SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (worktree
`proofs/lake-manifest.json` at session start; same pin as in-flight
schauder-fp / abel-ruffini / shannon / ballot / lagrange / cebyshev
slugs across the 2026-05-15→05-16 wave; ≥48h stable).

**Build status**: not directly attempted in this S1 OBSERVE (the slug
is doc-only-bootstrap scope; host Docker daemon hung as of S22 schauder
session ~30 min ago — `docker info` Server: section empty; same as
≥7 same-wave precedent PRs). The parent gallery slug `erdos-1006`
is the build-bearing entry; this -oq-01-oq-02 slug's file is an
auxiliary research support file with all 9 theorems already at 0
sorries.

## No Active Approach

The slug's mathematical question (cover graph recognition in P?) is
**genuinely open** in combinatorics; the Lean file already
axiomatizes it as `cover_graph_recognition_in_p`. No active proof
approach is on the table from this bootstrap session — the file is
"done" at the level of supporting infrastructure, and progress on the
open question requires deep complexity-theoretic work (or upstream
literature resolution).

## Attempt Count

- Total attempts: 1 (this S1 OBSERVE bootstrap)
- Current approach attempts: 1
- Approaches tried: 1 (bootstrap + drift fix)

## Blockers

None for this S1 OBSERVE (doc-only). Forward research is blocked at
the **mathematical** level — `cover_graph_recognition_in_p` is an open
question and cannot be reduced without a complexity-theoretic
breakthrough or upstream literature finding.

## Next Action

S2 OBSERVE or release/wait. Two productive directions:

1. **Literature scan**: check whether the open question has been
   resolved in the literature since 2026-05-03 (last in-slug Lean
   activity). If resolved, the axiom `cover_graph_recognition_in_p`
   can be replaced by a theorem (proof or reference).
2. **Partial-sub-class formalization**: identify and formalize a
   non-trivial sub-class for which cover graph recognition IS known
   to be in P (e.g., interval orders, bounded-width posets, planar
   cover graphs). This would weaken the axiom without resolving the
   open question.

The slug carries no hard time-bound; release is also acceptable.

## Open PRs

None for this slug at S1 OBSERVE session start.

- Last direct Lean-file edit: #15097 (2026-05-03) "research:
  add K₃ strict separation"; followed by #15112 (2026-05-03) "fix:
  correct theoremCount 10→9, remove True stub".
- Most recent JSON-related touch: #19841 (2026-05-16, mechanic batch
  sync of `Erdos1006OQ04.lean` leanFiles across 19 siblings; did NOT
  touch `Erdos1006OQ01OQ02.lean` entry; that entry's LOC 257 drift
  is what S1 OBSERVE fixes here).

## Iteration History

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|----|--------|
| S1 OBSERVE | 2026-05-16 | researcher-3 | (this PR) | Bootstrap state.md + problem.md + sessions/ + JSON top-level fields (slug/title/phase/status/currentState/started/tags/lastUpdate); fix leanFiles[1].lineCount 257→256; refresh knowledge.progressSummary (261→256, 10→9); refresh knowledge.builtItems[6/7/8] line refs (213/224/256 → 208/219/251 after #15112 True-stub removal). |

## Reference Files (in this directory)

- `problem.md` — problem statement (this PR introduces)
- `knowledge.md` — accumulated knowledge log (pre-existing)
- `sessions/2026-05-16-s1-observe-bootstrap-and-drift-fix.md` — this S1 OBSERVE memo
