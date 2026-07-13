# Mathlib PR: Granular Imports Analysis

**Session**: 2026-04-22
**Purpose**: Identify the minimal correct import set for a Mathlib PR submission.

---

## Current State (as of 2026-04-22)

Both files in our project are complete (0 sorries):

| File | Lines | maxHeartbeats | Status |
|------|-------|---------------|--------|
| `proofs/Proofs/SpernerMathlib4.lean` | 730 | 400000 | ✅ Mathlib-ready (heartbeats OK) |
| `proofs/Proofs/SpernerSimplicialInstance.lean` | 1019 | 1600000 | ⚠️ Needs heartbeat reduction |

The Mathlib issue (#25231) is OPEN and waiting for a PR submission.
YaelDillies asked for Part 2 (SimplicialComplex bridge) — it exists but hasn't been
highlighted to the reviewer yet.

---

## Granular Imports for `SpernerMathlib4.lean`

### Lemmas and Their Source Modules

| Lemma | Module |
|-------|--------|
| `Finset.sum_involution` | `Mathlib.Algebra.BigOperators.Group.Finset` |
| `Finset.card_biUnion` | `Mathlib.Algebra.BigOperators.Group.Finset` |
| `Fintype.sum_prod_type'` | `Mathlib.Algebra.BigOperators.Group.Finset` |
| `ZMod.natCast_eq_zero_iff` | `Mathlib.Data.ZMod.Basic` |
| `Finite.injective_iff_surjective` | `Mathlib.Data.Fintype.Card` |
| `Fintype.card_fin` | `Mathlib.Data.Fintype.Card` |
| `Finset.card_pair` | `Mathlib.Data.Finset.Card` |
| `Finset.card_eq_one`, `card_eq_two` | `Mathlib.Data.Finset.Card` |
| `Finset.card_pos`, `card_singleton` | `Mathlib.Data.Finset.Card` |
| `Finset.single_le_sum`, `add_sum_erase` | `Mathlib.Data.Finset.Card` |
| `even_two` | `Mathlib.Algebra.Ring.Parity` (via ZMod.Basic) |
| `Nat.even_iff` | (via ZMod.Basic or BigOperators) |

### Proposed Minimal Import Set

```lean
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
```

**Reasoning**:
- `BigOperators.Group.Finset` transitively imports `Finset.Basic`, `Finset.Card`,
  `Finset.Image`, `Finset.Lattice`, and all BigOperators primitives. This covers
  most `Finset.*` lemmas used in the file.
- `ZMod.Basic` covers `natCast_eq_zero_iff` and transitively brings in
  `Algebra.Ring.Parity` (for `even_two`) and `Nat.Cast.Basic`.
- `Fintype.Card` covers `Finite.injective_iff_surjective`, `Fintype.card_fin`,
  and transitively imports `Finset.Card` for card-specific lemmas.

### Module Path Notes

In Mathlib4, the import path for BigOperators Finset changed:
- Old (Mathlib3): `Mathlib.Algebra.BigOperators.Basic`
- New (Mathlib4): `Mathlib.Algebra.BigOperators.Group.Finset`

The `Basic.lean` file in `Group/Finset/` is a re-export module that pulls in
`Defs.lean`, `Finset.Prod`, and `Finset.Sum`. Use the directory import:
```lean
import Mathlib.Algebra.BigOperators.Group.Finset
```
(without `.Basic` suffix — the directory has its own module entry point)

**Note**: This needs build verification with Docker. The import set is based on
module-level research of the installed Mathlib package but has not been tested.

---

## Granular Imports for `SpernerSimplicialInstance.lean`

### Additional Lemmas Used

| Lemma | Module |
|-------|--------|
| `Finset.sort` | `Mathlib.Data.Finset.Sort` |
| `Finset.length_sort`, `Finset.mem_sort` | `Mathlib.Data.Finset.Sort` |
| `List.get`, `List.get_mem` | `Mathlib.Data.List.Basic` |
| `List.Nodup` (via `Finset.sort`) | `Mathlib.Data.List.Nodup` |
| `List.Sorted` (via `Finset.sort`) | `Mathlib.Data.List.Sort` |

### Additional Imports Needed

```lean
import Mathlib.Data.Finset.Sort
```

This likely brings in `Mathlib.Data.List.Sort` and friends transitively.

---

## PR Strategy: Two-File vs. Combined PR

### Option A: Submit Part 1 Only (Recommended for Initial PR)

Submit `SpernerMathlib4.lean` content as a single file:
```
Mathlib/Combinatorics/Sperner.lean
```

This aligns with SproutSeeds' "split approach to keep review load low." The abstract
`CellComplex` structure + `sperner_parity` can be reviewed independently.

**Pros**: Smaller review surface, faster acceptance.
**Cons**: Doesn't satisfy YaelDillies' request for Part 2.

### Option B: Submit Both Files (Complete PR)

Submit two files:
```
Mathlib/Combinatorics/Sperner/CellComplex.lean  (SpernerMathlib4 content)
Mathlib/Combinatorics/Sperner/SimplicialInstance.lean  (SpernerSimplicialInstance content)
```

**Pros**: Answers YaelDillies' question about Part 2 completely.
**Cons**: Larger review surface; `SpernerSimplicialInstance` needs heartbeat reduction.

### Recommendation

Start with Option A. Post a comment on #25231 linking to the file and asking if
this direction is correct before submitting the full PR. If Dillies approves the
abstract CellComplex approach, submit as a PR with just Part 1.

---

## Heartbeat Reduction for `SpernerSimplicialInstance.lean`

Current: `maxHeartbeats 1600000` (8× default)

The file has no obvious analogue to the `strongInduction` → `sum_involution`
optimization that reduced `SpernerMathlib4.lean`. The expensive proofs are:

1. **`adjFn_symm`** (87 lines): Adjacency symmetry for abstract simplicial data.
   Uses `dite` chains + `hne_erase.choose` pattern. May be improvable by
   extracting the uniqueness argument into a helper lemma.

2. **`adjFn_vertex`** (62 lines): Vertex sharing proof. Set-theoretic argument
   about `Finset.sort` images.

3. **`toTriangulation`** (55 lines): The full construction. Likely fast.

4. **`iadj_vertex'`** (57 lines): Interval triangulation vertex axiom. Fin arithmetic.

**Recommendation**: Profile with `set_option profiler true` after Docker build to
identify the actual bottleneck. Without profiler data, optimizations are guesswork.

---

## Next Actions (Prioritized)

1. **[EXTERNAL]** Post comment on mathlib4#25231 pointing Dillies to
   `SpernerSimplicialInstance.lean` as Part 2.

2. **[TECHNICAL]** Docker build test:
   ```bash
   ./proofs/scripts/docker-build.sh Proofs.SpernerMathlib4
   ```
   Verify compilation with the current `maxHeartbeats 400000` after any edits.

3. **[TECHNICAL]** Test granular imports by editing `SpernerMathlib4.lean`:
   Replace `import Mathlib` with the three proposed imports above.
   Run Docker build. If it fails, identify missing modules.

4. **[TECHNICAL]** Profile `SpernerSimplicialInstance.lean` to find expensive proofs.

5. **[SUBMISSION]** Once heartbeats are acceptable for both files, prepare the Mathlib
   fork branch with proper imports and submit PR to mathlib4.
