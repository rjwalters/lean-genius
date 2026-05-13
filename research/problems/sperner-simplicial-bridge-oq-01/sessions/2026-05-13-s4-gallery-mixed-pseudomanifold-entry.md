# S4 GALLERY — `sperner-simplicial-bridge-oq-01` gallery entry

**Researcher**: researcher-3
**Date**: 2026-05-13
**Phase**: ACT (GALLERY)
**Iteration**: 5
**Predecessors**: PR #18234 (S1 OBSERVE), #18363 (S2 SCAFFOLD), #18434 (S2b OBSERVE), #18451 (S2c PREP), #18537 (S3 ACT — `sperner_mixed_panchromatic_at_dim` lands, build pending), #18564 (S3b PREP — cross-stratum design + S4 GALLERY pre-flight recipe).
**Build status**: not applicable — gallery files only, no Lean changes.

## Scope

Executes the S4 GALLERY recipe pre-flighted in PR #18564 (S3b PREP, Component C). Creates the three gallery files for the OQ-01 closure:

- `src/data/proofs/sperner-simplicial-bridge-oq-01/meta.json`
- `src/data/proofs/sperner-simplicial-bridge-oq-01/annotations.json`
- `src/data/proofs/sperner-simplicial-bridge-oq-01/index.ts`

No edits to existing files. No edits to the Lean source `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean` (post-S3-ACT state on origin/main; 184 LOC, 7 theorems, 3 defs, 0 sorries, 0 axioms). No edits to `state.md` / `knowledge.md` / `problem.md` / `src/data/research/problems/sperner-simplicial-bridge-oq-01.json` (drift sync remains auditor/mechanic).

## Honest status — build-pending caveat

S3 ACT (PR #18537) merged 2026-05-13T03:32:39Z with a `build pending` qualifier in its title. No subsequent Doctor/Mechanic PR has confirmed `./proofs/scripts/docker-build.sh Proofs.SpernerSimplicialBridgeOQ01` succeeds, and the local worktree's `proofs/.lake` symlink is in the self-referential loop documented in memory `feedback_researcher_lake_symlink_loop_and_wipe.md`, so a local build is not feasible from this session.

The gallery entry therefore ships with:

- `status: "formalized"`
- `badge: "wip"`
- `axiomCount: 0`
- `sorries: 0`
- `theoremCount: 7`
- `definitionCount: 3`
- `lineCount: 184`

The `assumptions` field carries an explicit note that the formalisation is mathematically complete (0 sorries, 0 axioms) but build verification is pending. Once Doctor/Mechanic confirms the build, the entry can be promoted to `status: "verified"` / `badge: "verified"`.

This conservative posture follows the CLAUDE.md "Axiom Integrity Policy" rule *"When in doubt, use 'axiomatized' — overclaiming 'verified' damages credibility"*, here weakened from `axiomatized` (which would falsely imply assumption-bearing axioms) to `formalized` with a `wip` badge, which is the precedent set by `src/data/proofs/algebraic-numbers-countable-oq-02-oq-04/meta.json` (also 0 sorries, 0 axioms, `formalized`+`wip`).

## Field values vs. S3b PREP recipe

The S3b PREP (PR #18564 §C) pre-computed:

| Field | S3b PREP value | This PR's value | Match |
|---|---|---|---|
| `lineCount` | 184 | 184 | ✓ |
| `theoremCount` | 7 | 7 | ✓ |
| `definitionCount` | 3 | 3 | ✓ |
| `axiomCount` | 0 | 0 | ✓ |
| `sorries` | 0 | 0 | ✓ |
| `status` (if build passes) | `verified` | `formalized` (build unverified) | downgraded |
| `badge` (if build passes) | `verified` | `wip` (build unverified) | downgraded |
| `imports` | `["Proofs.SpernerSimplicialBridge"]` | same | ✓ |
| `mathlib_version` | `4.26.0` | `4.26.0` | ✓ |

The only deltas vs. the recipe are `status` and `badge`, downgraded to reflect the unverified build state. Recipe Component A (cross-stratum existential wrapper) was *not* bundled — Option α from the recipe would have required a Lean-file edit and a fresh build, both blocked by the symlink trap.

## Three sections (matches S3b PREP Component C)

| Section | Line range | Headline declaration | Annotation type |
|---|---|---|---|
| Stratification | 54-68 | `MixedPseudomanifold` | definition |
| Pure → Mixed Coercion | 70-109 | `MixedPseudomanifold.of_pure` | theorem |
| Per-Stratum Sperner | 111-180 | `sperner_mixed_panchromatic_at_dim` | theorem |

Each section gets one annotation in `annotations.json` (3 total — keeping the entry well-sized for a derived extension; the parent's 7 sections / 7 annotations is unnecessary for a 184-LOC file).

## Cross-references

Three entries in `meta.crossReferences`:

1. `generalisation-of` → `sperner-simplicial-bridge` (the parent OQ-01 strictly generalises).
2. `uses` → `sperner-simplicial-bridge` (the per-stratum proof is a single application of the parent's `exists_panchromatic`).
3. `sibling-of` → `sperner-simplicial-instance` (both build on the parent; sibling tackles concrete Kuhn-style triangulations).

The `sperner-simplicial-instance` cross-reference is documented even though both slugs are sibling derivations — this entry's `MixedPseudomanifold` framework and the sibling's `findPanchromaticBrute` algorithm are complementary, not overlapping.

## Three open questions in `meta.conclusion.openQuestions`

Per the research methodology's "follow-up question generation" guidance (CLAUDE.md §researcher.md), three strong follow-ups:

1. **Cross-stratum existential wrapper** — a 3-line `obtain`-then-`exact` convenience corollary. Pre-designed in S3b PREP Component A (PR #18564). Low priority (convenience, not new mathematical content).
2. **`Mathlib.Geometry.SimplicialComplex.facets` bridge** — the natural Mathlib entry point for non-pure simplicial complexes. The translation layer between Mathlib's affine-set encoding and this file's `Finset (Finset E)` encoding is the open work. This is the parent's OQ-02, advanced by the mixed-pseudomanifold framework now in place.
3. **Global boundary-door count** — replace the cross-stratum disjunction with a sum `globalBoundaryDoors K c := Σ d, boundaryDoorCount (d := d) K c`. Parity reasoning over a sum requires exactly one stratum has odd boundary count, non-trivial in multi-dimensional settings.

## Orthogonality

| Touched file | Status | Conflict |
|---|---|---|
| `src/data/proofs/sperner-simplicial-bridge-oq-01/meta.json` | new | none (path does not exist on origin/main) |
| `src/data/proofs/sperner-simplicial-bridge-oq-01/annotations.json` | new | none |
| `src/data/proofs/sperner-simplicial-bridge-oq-01/index.ts` | new | none |
| `research/problems/sperner-simplicial-bridge-oq-01/sessions/2026-05-13-s4-gallery-mixed-pseudomanifold-entry.md` | new | none (this file) |
| `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean` | unchanged | n/a |
| `proofs/Proofs.lean` | unchanged | n/a |
| `src/data/listings.json` | regenerated at deploy via `scripts/annotations/build.ts` | n/a |

Per the gallery-clean-task memory `feedback_researcher_s3_gallery_clean_task_pattern.md`, this is a clean S4 GALLERY task: build-verified or build-pending Lean already on main, gallery dir missing, ship 3 files + 1 session note. No race risk (no open PR on this slug, none in flight on the parent or sibling slugs as of claim time).

## Pre-flight checklist

| Item | Verified by |
|---|---|
| Lean source on origin/main at 184 LOC, 7 theorems, 3 defs, 0 sorries, 0 axioms | direct `grep -nE "^(noncomputable )?(def|theorem|lemma)"` |
| Lean source imported in `proofs/Proofs.lean` | direct grep |
| No `sperner-simplicial-bridge-oq-01` gallery dir on disk | `ls src/data/proofs/sperner-simplicial-bridge-oq-01/` → not found |
| Parent slug `sperner-simplicial-bridge` exists and is `verified` | direct meta.json read |
| No open same-slug PR | `gh pr list --repo rjwalters/lean-genius --search "sperner-simplicial-bridge-oq-01 in:title is:open"` → empty |
| Parent's `index.ts` shape | direct file read; standard `proof + annotations + getProofSource` pattern |
| Parent's annotations.json schema (10 keys per entry) | direct file read |
| JSON validates | `jq .` on both meta.json and annotations.json |
| Worktree-local file paths (no Write-tool main-repo trap) | `ls -la` on both worktree and main-repo paths |

## Post-merge follow-ups (deferred)

1. **Build verification**. Doctor or Mechanic should run `./proofs/scripts/docker-build.sh Proofs.SpernerSimplicialBridgeOQ01` from a clean worktree (no `.lake` symlink loop) and, if successful, promote this gallery entry to `status: "verified"` / `badge: "verified"`.
2. **Cross-stratum existential wrapper** (S3b PREP Option α). Add `sperner_mixed_panchromatic_exists` (~8-12 LOC) to the Lean file post-build-verify. Promote the `theoremCount` to 8 and `lineCount` to ~192-196.
3. **Drift-sync** of `state.md` / `knowledge.md` / `problem.md` / `src/data/research/problems/sperner-simplicial-bridge-oq-01.json` to reflect Phase: GALLERY landed. Auditor/Mechanic's domain.
4. **Parent slug's `openQuestions` list** in `src/data/proofs/sperner-simplicial-bridge/meta.json` — the OQ-01 entry can be marked closed/answered. Enricher/Mechanic's domain.

## Honesty

- **This entry does not prove the build is correct.** The Lean source is on origin/main but unverified by docker-build. Promotion to `verified` is deferred to Doctor/Mechanic.
- **The mathematical content is unchanged from PR #18537.** This PR is *gallery integration only* — no new theorems, no new sorries, no new mathematical work. The gallery entry exposes the per-stratum theorem and the three supporting helpers in human-readable form.
- **The annotations are derived from the file's docstrings and the S3b PREP recipe.** No new insights; the keyInsights and overview fields are distilled from the merged session notes.
- **The cross-stratum existential wrapper (S3b PREP Option α) is *not* shipped here.** It would require a Lean-file edit, an additional theorem, and a fresh build, all blocked by the symlink trap. It is pre-designed and listed as a deferred follow-up.

## References

- **S3b PREP (recipe)**: `research/problems/sperner-simplicial-bridge-oq-01/sessions/2026-05-13-s3b-prep-cross-stratum-and-post-s3-build-risk-audit.md`, Component C (PR #18564).
- **S3 ACT (Lean source)**: `research/problems/sperner-simplicial-bridge-oq-01/sessions/2026-05-13-s3-act-stratum-d-implementation.md` (PR #18537).
- **Parent gallery slug**: `src/data/proofs/sperner-simplicial-bridge/{meta.json, annotations.json, index.ts}`.
- **Formalised/wip precedent**: `src/data/proofs/algebraic-numbers-countable-oq-02-oq-04/meta.json` (status `formalized`, badge `wip`, 0 sorries, 0 axioms).
- **Build trap**: memory `feedback_researcher_lake_symlink_loop_and_wipe.md`.
- **Gallery-clean-task pattern**: memory `feedback_researcher_s3_gallery_clean_task_pattern.md`.
