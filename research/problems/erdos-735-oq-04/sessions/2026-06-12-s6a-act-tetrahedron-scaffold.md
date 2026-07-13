# S6a ACT scaffold — tetrahedron `(d=3, k=2)` magic witness (Lean)

**Date**: 2026-06-12
**Researcher**: researcher-2
**Mode**: ACT (scaffold — Docker build-verified; proofs isolated as documented sorries)
**Phase**: S6a ACT
**Branch**: `research/erdos-735-oq-04-s6a-tetrahedron-<ts>`

## Deliverable

New leaf file **`proofs/Proofs/Erdos735OQ04Tetrahedron.lean`** (+ one import
line in `proofs/Proofs.lean`).  First Lean realization of the concrete
higher-flat (`k = 2`) magic witness conjectured by the parent slug.

```lean
namespace Erdos735OQ04Tetra
open Erdos735OQ04

noncomputable def tetraVertex : Fin 4 → EuclideanSpace ℝ (Fin 3)
  | 0 => !₂[ 1,  1,  1] | 1 => !₂[ 1, -1, -1]
  | 2 => !₂[-1,  1, -1] | 3 => !₂[-1, -1,  1]

noncomputable def tetraConfig : PointConfigD 3 := Finset.image tetraVertex Finset.univ

theorem tetra_affineIndependent : AffineIndependent ℝ tetraVertex := by sorry
theorem tetraConfig_isKFlatMagic : IsKFlatMagic 2 tetraConfig := by sorry
```

**Counts**: 0 axioms, 2 sorries, 2 defs, 2 theorems (statements only).

## Build verification

`./proofs/scripts/docker-build.sh Proofs.Erdos735OQ04Tetrahedron` → **clean,
3063 jobs**.  Warnings: the two expected `declaration uses 'sorry'` plus the
pre-existing benign `Erdos735Problem.lean:142 unused variable hp` (not
introduced here).  Confirms against Mathlib v4.26.0 that:

- the `!₂[…]` `EuclideanSpace ℝ (Fin 3)` vertex literals typecheck,
- `Finset.image tetraVertex Finset.univ : PointConfigD 3` typechecks,
- both theorem statements (`AffineIndependent`, `IsKFlatMagic 2`) are
  well-formed against the parent's `IsKFlatMagic` / `ConfigKFlat` defs.

## Why a scaffold (not a full discharge) this iteration

1. **Aristotle MCP unreachable.**  `prove` and `prove_file` both returned
   `{"status":"error","message":"Resource not found."}` — including a trivial
   `a + b = b + a` probe.  The backend was down for the whole session.
2. **Mathlib source not browsable in the worktree.**  `proofs/.lake/packages`
   resolves to a self-referential symlink, so exact lemma-name confirmation
   (e.g. `AffineIndependent.finrank_vectorSpan`, `affineSpan_le`,
   `Module.finrank_eq_of_rank_eq`) is not possible without per-name Docker
   round-trips.  Hand-proving affine independence of explicit `EuclideanSpace`
   vectors is notoriously fiddly and was judged a poor use of unbounded
   ~minute-scale Docker iterations under those two constraints.

Shipping a build-verified scaffold mirrors the slug's own S2 ACT (#19012,
which shipped two `sorry`-theorems as a typechecked scaffold) and is honest,
additive, leaf-only progress.

## Architecture improvement over S6a PREP (#18486)

The PREP planned to **enumerate the four faces** `F₁…F₄` and prove "no other
minimal-spanning 2-flat" (its Lemma 3.2, a case analysis on
`(filter (· ∈ F)).card`).  This file replaces that with the leaner
**affine-independence** route, which needs no face enumeration:

> For uniform weight `w ≡ 1`, `kFlatSum = (filter (· ∈ F)).card`.  Every
> `F : ConfigKFlat 2 tetraConfig` has filter card `≥ 3` (the config
> constraint) and `≤ 3`: if all four vertices lay in the rank-2 flat `F`, then
> `affineSpan ℝ (range tetraVertex) ≤ F`, hence
> `vectorSpan ℝ (range tetraVertex) ≤ F.direction`; but the vertices are
> affinely independent so `finrank (vectorSpan …) = 3`, forcing
> `finrank F.direction ≥ 3`, contradicting `Module.rank F.direction = 2`.
> Therefore the card is exactly `3` and every flat-sum equals the constant
> `c = 3`.

This generalizes verbatim to "any affinely independent `d+1` points in `ℝᵈ`
are `(d-1)`-flat magic with constant `d`" — a natural S6e follow-up.

## Discharge route (hand-tractable, 0 new axioms)

- `tetra_affineIndependent`:
  `rw [affineIndependent_iff_linearIndependent_vsub ℝ tetraVertex 0]`, then
  linear independence of the three difference vectors
  `(0,-2,-2), (-2,0,-2), (-2,-2,0)` (det `-16 ≠ 0`).
- `tetraConfig_isKFlatMagic`: `refine ⟨⟨fun _ => 1, …⟩, 3, …, ?_⟩`; reduce
  `kFlatSum` to the filter card via `Finset.sum_const` / `dif_pos`; bound the
  card with `tetra_affineIndependent` + `AffineIndependent.finrank_vectorSpan`
  (`Fintype.card (Fin 4) = 3 + 1`) + `affineSpan_le` + `direction`
  monotonicity + `Module.finrank_eq_of_rank_eq`.

## Files changed

- `proofs/Proofs/Erdos735OQ04Tetrahedron.lean` — new (defs + 2 statements + 2 sorries + header memo)
- `proofs/Proofs.lean` — +1 import line
- `research/problems/erdos-735-oq-04/state.md` — phase header + new section + OQ-table row
- `research/problems/erdos-735-oq-04/sessions/2026-06-12-s6a-act-tetrahedron-scaffold.md` — this file

No edits to the parent `.lean`, the gallery JSON, `problem.md`, or
`knowledge.md`.

## Next action

- **Discharge the two sorries** following the in-file route (Aristotle once the
  MCP backend is reachable, or a hand pass).
- **S6e generalization**: lift the affine-independence argument to the abstract
  "`d+1` affinely independent points ⇒ `(d-1)`-flat magic" theorem.
- **S7**: gallery JSON `status: "axiomatized"` for the parent slug.
