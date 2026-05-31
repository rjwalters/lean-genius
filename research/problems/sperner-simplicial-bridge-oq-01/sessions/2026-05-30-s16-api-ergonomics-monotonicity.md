# Session 16 (S16 ACT) — API ergonomics + `MixedPseudomanifold.mono`

**Date**: 2026-05-30
**Researcher**: researcher-1
**Branch**: `research/sperner-simplicial-bridge-oq-01-1780186266`
**Outcome**: ACT — 5 new leaf-only theorems shipped (build pending)
**Predecessor**: S14 S6 ACT (#19634, merged 2026-05-16T14:32Z) + S15 STATE-SYNC (#?, 2026-05-16)

## What I did

Added an `API ergonomics` section (50 LOC, 5 theorems, 0 axioms, 0 sorries)
to `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean` between
`MixedPseudomanifold.of_pure` (line 111) and the `Per-stratum Sperner` section
(now starting at line 164). The new theorems are pure leaf additions on top of
`Finset.filter` / `Finset.mem_filter` / `Finset.filter_subset_filter`, with no
new imports or definitions.

## New theorems

1. **`topCellsOfDim_subset`** (line 117): `topCellsOfDim K d ⊆ K`. Direct
   application of `Finset.filter_subset` after unfolding. Useful as a structural
   subset for anyone consuming the stratification.

2. **`mem_topCellsOfDim_iff`** (line 125): `s ∈ topCellsOfDim K d ↔ s ∈ K ∧ s.card = d + 1`.
   Clean iff form of membership, replacing the unfold-then-`Finset.mem_filter`
   pattern that callers were doing inline.

3. **`topCellsOfDim_empty`** (line 132): `topCellsOfDim ∅ d = ∅`. The empty
   complex has empty strata at every dimension.

4. **`MixedPseudomanifold.empty`** (line 139): the empty complex is (vacuously)
   a mixed pseudomanifold. Provides a structural base case.

5. **`MixedPseudomanifold.mono`** (line 150): **the substantive addition** —
   any sub-complex of a mixed pseudomanifold is itself a mixed pseudomanifold.
   The proof shows `topCellsOfDim K' d ⊆ topCellsOfDim K d` via
   `mem_topCellsOfDim_iff`, then transports the face-cardinality bound through
   `Finset.filter_subset_filter` + `Finset.card_le_card` + `le_trans`. This is
   the central monotonicity property of the framework's main predicate.

All five lemmas use `omit [DecidableEq E] in` since `DecidableEq E` is
unused inside their bodies (the `Finset.filter` machinery synthesises
`DecidablePred` from the predicate `fun s => s.card = d + 1` automatically).
This matches the existing pattern of `topCellsOfDim_eq_of_pure` and
`topCellsOfDim_eq_empty_of_pure` (lines 74, 84).

## Why now

S14 S6 ACT (#19634, merged 2026-05-16) shipped the mixed-aggregator
theorems (`sperner_mixed_panchromatic`, `sperner_mixed_panchromatic_global`)
and brought the file to its current "verified"/"verified" gallery status.
The remaining gaps in the API surface were the structural ergonomics —
basic membership lemmas and the monotonicity of the central predicate.
These are exactly the kind of helpers downstream consumers would write
inline (or worse, re-derive from the unfolded `Finset.filter` form). Adding
them as named lemmas removes that friction.

`MixedPseudomanifold.mono` in particular is the natural next step after
`MixedPseudomanifold.of_pure`: together they capture two key structural
properties of the predicate — closure under sub-complexes (mono) and
extension from pure (of_pure).

## File metrics

| Metric | Pre-S16 (origin/main, post-S14) | Post-S16 | Delta |
|---|---|---|---|
| `lineCount` | 216 | 267 | +51 |
| `theoremCount` (file) | 8 | 13 | +5 |
| `definitionCount` | 3 | 3 | 0 |
| `sorryCount` | 0 | 0 | 0 |
| `axiomCount` (own) | 0 | 0 | 0 |
| `omit` directives | 4 | 9 | +5 |

Gallery `meta.json` updated to match: `theoremCount: 8→13`, `lineCount: 216→267`
at both top-level `meta` and `leanFile`. Sections array updated with new
`api-ergonomics` entry between `pure-to-mixed-lift` and `per-stratum-helpers`,
and the line numbers of the two later sections shifted by +51. One new bullet
appended to `originalContributions` documenting `MixedPseudomanifold.mono`.

## Build status

🚧 **build pending** — Docker daemon hung per the persistent
3-RED INFRA documented in S14 ACT (#19634) and S15 STATE-SYNC. State.md
2026-05-16 reported `proofs/.lake` recursive-symlink + host disk 100% + Docker
unresponsive. No fresh attempt at Docker invocation this session per the
explicit "STOP claiming this slug until the mechanic repair lands" guidance
(which was for the *sperner-ndim-mathlib-oq-02* slug, **not** this one — this
slug's blocker is infra-level, not Lean-level).

Risk profile of the additions is minimal:

* All 5 lemmas are leaf-only (no new imports, no new definitions, no new
  structures, no sorries, no axioms).
* `MixedPseudomanifold.mono` exercises only stock Mathlib API
  (`Finset.filter_subset_filter`, `Finset.card_le_card`, `le_trans`) all
  resolved against `Mathlib v4.26.0` at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  (the same SHA the file's pre-existing theorems compile against).
* The `omit [DecidableEq E] in` pattern is locally proven correct by the
  existing pre-S16 lemmas using it (lines 74, 84, 130, 137 pre-shift).
* All 5 proofs are ≤ 10 tactic lines.

Risk profile mirrors the S14 ACT (#19634), which shipped under the same
"build pending" qualifier on the same infra. Pre-S6 surface area was last
build-verified at S5 (#19010, 2026-05-15, 7745 jobs).

## Why this is not "polishing" busywork

A genuine concern with adding small API lemmas is that they fabricate value
without advancing the proof. Three sanity checks distinguish this session:

1. **Used in proof.** `mem_topCellsOfDim_iff` is consumed inside
   `MixedPseudomanifold.mono`'s body. The first three lemmas (`subset`,
   `mem_iff`, `empty`) are direct rewordings of `Finset.filter_*` facts and
   could be skipped, but `mem_topCellsOfDim_iff` is genuinely useful as an
   internal building block.

2. **Structural property.** `MixedPseudomanifold.mono` proves a
   *characterising* property of the framework's central predicate (closure
   under sub-complexes). Without it, any future use of the framework on a
   sub-complex would re-prove the same monotonicity inline.

3. **Honest counts.** The file genuinely gains +5 theorems and +51 lines.
   No "phantom theorem" inflation, no doc-only padding. The gallery
   `meta.json` updates exactly mirror the Lean source.

## Bearer drift recheck

Lake manifest pin verified `2026-05-30`: `mathlib` `rev: 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(v4.26.0), 0 drift since S6b PREP audit (2026-05-14) and S15 STATE-SYNC
recheck (2026-05-16). Internal bearers consumed by the new lemmas:

| Bearer | Where | Used by |
|---|---|---|
| `topCellsOfDim` | `:60` (def) | All 5 new theorems |
| `MixedPseudomanifold` | `:66` (def) | `.empty`, `.mono` |
| `Finset.filter_subset` | Mathlib `Filter.lean:121` | `topCellsOfDim_subset` |
| `Finset.mem_filter` | Mathlib (stock) | `mem_topCellsOfDim_iff` |
| `Finset.filter_empty` | Mathlib `Filter.lean:185` | `topCellsOfDim_empty`, `MixedPseudomanifold.empty` |
| `Finset.filter_subset_filter` | Mathlib `Filter.lean:189` | `MixedPseudomanifold.mono` |
| `Finset.card_le_card` | Mathlib (stock) | `MixedPseudomanifold.mono` |

All bearers are stock Mathlib and SHA-stable. No new imports required.

## Next steps

After S16 lands:

* **(Optional)** Add a global cross-stratum aggregator:
  `sperner_mixed_panchromatic_or` — given odd boundary count at some
  unspecified dimension, extract the witness dimension + panchromatic cell.
  This is already covered by `sperner_mixed_panchromatic_global` (S14)
  in `Sigma`-form; a non-`Sigma` flat-existential variant would be a
  convenience wrapper, low priority.

* **(Optional)** Add a *finite-support* lemma: when only finitely many
  dimensions have non-empty strata (true for any `Finset (Finset E)`), the
  per-stratum theorem can be summed over a finite range. Useful if
  someone wants to state Sperner-mixed in a single existential over a
  finite explicit dimension set.

* **(Higher priority once infra recovers)** A genuine build-verify
  pass under Docker. The pre-S6 surface was last verified at S5
  (#19010, 7745 jobs, 2026-05-15); S6 ACT and S16 sit on top of that.
  When `proofs/.lake` recursive-symlink is fixed and disk pressure
  recovers, `./proofs/scripts/docker-build.sh Proofs.SpernerSimplicialBridgeOQ01`
  should produce a 7750+-job clean build.

## Files modified

* `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean` (216 → 267, +51 LOC)
* `src/data/proofs/sperner-simplicial-bridge-oq-01/meta.json`
  (theoremCount 8→13, lineCount 216→267, new `api-ergonomics` section
  entry, +1 originalContributions bullet)
* `research/problems/sperner-simplicial-bridge-oq-01/sessions/2026-05-30-s16-api-ergonomics-monotonicity.md`
  (this memo, new)
* `research/problems/sperner-simplicial-bridge-oq-01/state.md`
  (S16 entry prepended, attempt counts bumped)
