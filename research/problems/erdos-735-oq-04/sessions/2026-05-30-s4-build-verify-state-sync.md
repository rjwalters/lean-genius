# S4 BUILD-VERIFY STATE-SYNC (researcher-1, 2026-05-30T22:35Z, doc-only)

## TL;DR

Syncs the slug tracker (`state.md` + JSON + this new session file) to
the post-#20882 reality.  S3 ACT #19687 (2026-05-16) shipped under
`(build pending — Docker daemon hung)` qualifier.  PR #20882
(2026-05-28T21:32Z) repaired the Mathlib v4.26.0 API drift and
Docker-verified `Proofs.Erdos735OQ04` on the pinned Mathlib SHA.
The slug tracker has been out-of-sync with main since that landing
(~2 days).  This STATE-SYNC flips the qualifier to `build-verified`.

## What PR #20882 fixed

| Drift | Pre-#20882 | Post-#20882 |
|---|---|---|
| Module finrank | `finrank_eq_of_rank_eq` | `Module.finrank_eq_of_rank_eq` |
| `Set.Nonempty F` | element type inferred | element type explicit |
| `AffineSubspace.mem_top` | implicit field | explicit field `ℝ` |

No mathematical content changed.  Both
`zero_flat_magic_trivial` and `ambient_flat_magic_trivial` remain
discharged with constant-1 weighting witnesses (S3 PREP-2 recipe
preserved verbatim modulo the v4.26.0 API renames).

## Subsequent meta-only PRs

- **#19717** (2026-05-16, post S3 ACT): added the missing
  `leanFiles[Erdos735OQ04.lean]` entry to the JSON.
- **#19929** (2026-05-16): corrected `defCount 5→4, sorryCount 0→1`
  (the `5→4` was correct; the `0→1` was a transient regression that
  #20882 later cleared back to `0`).
- **#20882** (2026-05-28): repaired the v4.26.0 API drift and
  Docker-build-verified, reducing `sorryCount` back to 0 and stabilising
  the file metadata.
- **#20896** (2026-05-29, parent-side AXIOM HUNT, researcher-1):
  corrected the long-standing stale claim that
  `Proofs/Erdos735Problem.lean` was broken on `origin/main` — it
  builds clean against Mathlib v4.26.0 (3061 jobs); two example axioms
  (`three_collinear_card`, `triangle_card`) eliminated; parent
  axiomCount 7 → 5.

## File counts (post-#20882, current main)

```
Proofs/Erdos735OQ04.lean
- lineCount: 154
- theoremCount: 2  (zero_flat_magic_trivial, ambient_flat_magic_trivial)
- defCount:     4  (5 in S3 PREP-2; one auxiliary helper collapsed during build-verify)
- axiomCount:   0
- sorryCount:   0
- Docker:       build-verified on Mathlib v4.26.0 (PR #20882)
```

## What this STATE-SYNC modifies

1. **`research/problems/erdos-735-oq-04/state.md`**:
   - Phase header: `ACT — build pending …` → `ACT BUILD-VERIFIED`.
   - Since: `2026-05-16` → `2026-05-28` (matches PR #20882 land time).
   - Iteration: `6` → `7` (adds S4 BUILD-VERIFY).
   - Last Updated: `2026-05-16T15:55Z` → `2026-05-30T22:35Z`.
   - Adds new `## S4 BUILD-VERIFY ACT-VERIFIED` subsection documenting
     the three API repairs and the meta-sync chain.
   - Rewrites `## Next Action` to drop the obsolete
     `build-verify via docker-build.sh` instruction (already done by
     #20882) and reframe forward-looking options.
2. **`src/data/research/problems/erdos-735-oq-04.json`**:
   - Top-level `phase`: `ACT` → `ACT BUILD-VERIFIED`.
   - `currentState.phase`: same.
   - `currentState.since`: `2026-05-16T15:55Z` → `2026-05-28T21:32Z`.
   - `currentState.iteration`: `6` → `7`.
   - `currentState.focus` + `currentState.nextAction` rewritten to
     S4 BUILD-VERIFY narrative + post-sync forward path.
   - `currentState.blockers`: S4 (parent reduction) moved from
     "blocked on parent repair" to "no longer blocked — parent builds
     clean per #20896 AXIOM HUNT"; S5 axiom remains genuinely open.
   - `lastUpdate` / `lastUpdated`: bumped to 2026-05-30.
   - `leanFiles[Erdos735OQ04.lean]`: `lineCount` 153 → 154,
     `sorryCount` 1 → 0 (re-syncing to the actual post-#20882 file
     content; the `1` was a transient #19929 artefact already
     corrected on disk).
3. **`research/problems/erdos-735-oq-04/sessions/2026-05-30-s4-build-verify-state-sync.md`** (this file, new).

No Lean / gallery / sibling / problem.md / knowledge.md / lake-manifest
edits.

## Forward-looking options (post-S4 BUILD-VERIFY)

Four independently shippable substantive sub-steps remain:

1. **S4-ACT parent reduction `oneflat_eq_parent`** (now UNBLOCKED
   per #20896): `IsKFlatMagic 1 P ↔ Erdos735.IsMagic P` at `d = 2`,
   almost-definitional but not bare `rfl` — needs `Nat.cast_one`
   transport across the `Module.rank` coercion.
2. **S6a-ACT tetrahedron certificate** (paste-ready PREP at #18486):
   2-flat magic with uniform constant-1 weights, magic constant 3.
3. **S6b/c-ACT octa+cube refutations** (paste-ready PREP at #18541):
   `¬ IsKFlatMagic 2 {octa-vertices}` + same for cube, via O_h symmetry
   + 2-flat-size split argument.
4. **S5 axiom-design PREP**: refine the higher-dim conjecture to the
   narrow regular-polytope subfamily (excludes octa+cube; admits
   tetrahedron; dodec/icosa untested).

## Pre-flight gate for the next ACT

- ✅ Docker: recovered (v29.4.1, sub-5s response).
- ✅ Disk: 61 Gi avail at 2026-05-30T22:35Z (vs 5.3 Gi at S3 ACT-time).
- ✅ Mathlib: lake-pinned SHA stable at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
- ✅ Parent: `Erdos735Problem.lean` builds clean per #20896
  (3061 jobs, axiomCount 5, sorryCount 0).
- ✅ Sub-file: `Erdos735OQ04.lean` builds clean per #20882
  (sorryCount 0, axiomCount 0).

No infra blockers remain.  Any of the four forward options is
shippable in a single ACT iteration.
