# sperner-mathlib4-oq-03 — Brouwer via Sperner parity + fixed-point index

## Summary

Parent open question (sperner-mathlib4 openQuestions[2]): *"Can the Sperner parity
theorem be combined with a fixed-point index computation to prove Brouwer's
fixed-point theorem in Lean 4?"*

**Full deliverable (topological Brouwer) is BLOCKED for a single session** — the
geometric realization (subdividing the standard simplex, deriving a Sperner
labelling from a continuous self-map, proving the boundary index = 1 by induction
on dimension, passing to a fixed point by compactness) is a >1000-line
development requiring simplicial-approximation infrastructure Mathlib does not
package.

**Tractable, verified progress made:** formalized the *fixed-point index
computation* half — the exact object the open question names — as a mod-2 index
layer on top of the parent's verified `sperner_parity`/`sperner`.

## Session 2026-07-01 (Session 1) — Fixed-point index layer

**Mode**: FRESH · **Outcome**: progress (index layer built; Brouwer still open)

### What I did
- Wrote `proofs/Proofs/SpernerMathlib4OQ03.lean` (146L, 8 thm / 4 def, 0 sorry,
  0 `native_decide`) importing the verified parent `Proofs.SpernerMathlib4`.
- Defined `panchromaticCount`, `boundaryDoorCount`, and the ZMod-2 indices
  `fpIndex`, `boundaryIndex`.
- Proved `fpIndex_eq_boundaryIndex` (Sperner parity as an identity of mod-2
  indices — the "index computation"), `exists_panchromatic_of_boundaryIndex_ne_zero`
  (existence engine), `boundaryIndex_eq_zero_of_no_panchromatic`
  (vanishing / no-retraction shadow), `even_panchromaticCount_iff_even_boundaryDoorCount`
  (parity dichotomy), `even_panchromaticCount_of_no_boundary_doors` (boundaryless
  ⟹ index 0), and recovered `sperner` in index language.

### Key findings / techniques
- The mod-2 panchromatic count IS a fixed-point index: `sperner_parity` is exactly
  the statement that it depends only on boundary data (`fpIndex = boundaryIndex`).
- `ZMod.natCast_eq_natCast_iff` turns the `Nat.ModEq` parity into a ZMod-2 identity.
- `ZMod.natCast_eq_zero_iff_even` (ZMod/Basic.lean:748) + `not_even_iff_odd` bridge
  `boundaryIndex ≠ 0` ⟷ `Odd boundaryDoorCount` to apply `sperner`.
- Mathlib has **no** Sperner lemma and **no** Brouwer fixed-point theorem, so this
  layer is genuinely new (not a Mathlib wrapper).

### Environment notes (battleground)
- Host disk hit 99% full; freed via `docker builder prune` (~4 GB reclaimable) and
  removing orphan/stale worktrees.
- Local Mathlib olean cache is torn: after `lake exe cache get`, 11 core modules
  still missing (`Mathlib.Data.Option.Basic`, `Mathlib.Data.Set.UnionLift`,
  `Mathlib.Topology.Homeomorph.Lemmas`, ...) — host `lake env lean` cannot build.
  Verification routed through `docker-build.sh` (separate cache volume).
- All lemma names used were verified to exist in the Mathlib source before build.

### Next steps
- Geometric realization: build the standard-simplex subdivision + Sperner labelling
  from a continuous self-map; prove boundary index = 1 by induction on dimension
  (needs the (d-1)-dim Sperner on boundary faces); pass to fixed point by compactness.
- Check `sperner-ndim` / `SpernerFreudenthal*` for reusable simplicial-approximation
  pieces toward the boundary-index-1 step.
