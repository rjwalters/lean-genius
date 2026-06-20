# Knowledge Base: dirichlet-approximation-theorem-oq-03

Dirichlet's approximation theorem via Minkowski's convex-body theorem (geometry of numbers).

**Status**: COMPLETE (drafted, build-unverified) — the full unconditional Minkowski re-derivation of Dirichlet's bound is drafted sorry-free and axiom-free in `DirichletApproximationOQ03.lean` (18 theorems/defs, 0 sorry, 0 axiom, no native_decide). The `volume(K) = 4` step is closed via the determinant-(−1) shear and `dirichlet_via_minkowski` assembles the unconditional bound. **BUILD UNVERIFIED this session: the Docker daemon was unresponsive, so the elaboration / axiom-free claims rest on source inspection and need a successful `docker-build.sh Proofs.DirichletApproximationOQ03` to confirm.**

---

## Problem Understanding

Re-derive the gallery's pigeonhole bound `|qα - p| ≤ 1/N` (`1 ≤ q ≤ N`) from Minkowski's
convex-body theorem applied to `K = {(x,y) : |x| ≤ N, |αx - y| ≤ 1/N}`, a symmetric parallelogram
of area exactly `4 = 2²·covol(ℤ²)`.

---

## What We've Built

- `body` - the symmetric convex body `K(α,N) = {v : ℝ² | |v 0| ≤ N ∧ |α·v 0 - v 1| ≤ 1/N}`.
- `body_symm` - `K` is symmetric about the origin (`v ∈ K → -v ∈ K`).
- `body_convex` - `K` is convex (intersection of two linear slabs).
- `body_isClosed` - `K` is closed (preimages of closed intervals under continuous functionals).
- `dirichlet_of_lattice_point` - arithmetic bridge: for `N ≥ 2`, a nonzero integer point of `K` is a Dirichlet approximation (sign normalisation to `1 ≤ q ≤ N`, plus the `q = 0` boundary exclusion).
- `dirichlet_via_convex_body` - Dirichlet's bound, conditional on the Minkowski conclusion (a nonzero integer point of `K`).
- `shear`, `box`, `body_eq_image`, `box_eq_Icc`, `box_isCompact`, `body_isCompact` - the determinant-(−1) shear `(x,y) ↦ (x, αx − y)` (an involution), the axis-aligned box, and the identity `K = shear '' box` plus compactness of both.
- `box_volume` (`= 4`), `body_volume` (`= 4`) - the measure computation, via `volume_pi_pi`/`Real.volume_Icc` and `addHaar_image_linearMap` with `LinearMap.det_toLin'` + `Matrix.det_fin_two_of`.
- `dirichlet_via_minkowski` - **the unconditional capstone**: Dirichlet's `|qα − p| ≤ 1/N` (`1 ≤ q ≤ N`, `N ≥ 2`) from `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure` against the standard lattice `ℤ² = span ℤ (range (Pi.basisFun ℝ (Fin 2)))`. **Build-unverified this session (Docker down).**

---

## Insights

- **The whole proof collapses to `volume(K) = 4`.** With the geometric facts and the arithmetic
  back-end machine-checked, the only remaining content is the single measure computation.
- **Minkowski gives the non-strict bound** `|qα - p| ≤ 1/N`. The body has area *exactly* `4`, so
  only the closed/compact `≤`-variant `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure`
  applies; the strict `<` of the pigeonhole entry needs the open-boundary refinement.
- **`q = 0` boundary subtlety.** A nonzero integer point of `K` can have first coordinate `0` only
  if it is `(0, ±1)`, which lies in `K` exactly when `N = 1`. Hence the bridge assumes `N ≥ 2`
  (`N = 1` is the trivial case `q = 1`, `p = round α`).
- **Volume via a shear.** `K` is the image of the box `[-N,N]×[-1/N,1/N]` (volume 4) under
  `(x,y) ↦ (x, αx - y)`, a linear map of determinant `-1`; `addHaar_image_linearMap` then gives
  `volume(K) = |det|·4 = 4`.

## Mathlib inventory (for the finish)

- `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure` - Minkowski (compact).
- `ZSpan.isAddFundamentalDomain`, `ZSpan.volume_fundamentalDomain` - standard-lattice covolume `1`.
- `MeasureTheory.Measure.addHaar_image_linearMap` - linear-image volume law.
- `Convex.linear_preimage`, `convex_Icc` - convexity of `K`.
- `abs_sub_convergents_le'`, `abs_sub_convs_le` - continued-fraction error bounds (subsumption route).

## Dead Ends

- Strict `<` directly from Minkowski: the area-`= 4` body needs `> 4` for the strict
  (`..._lt_measure`) variant, so strict Dirichlet is not free from this body.

## Next Steps

1. **Verify the build** — `./proofs/scripts/docker-build.sh Proofs.DirichletApproximationOQ03` once
   Docker is back up. Risk surface is Mathlib lemma-name/signature drift in the unconditional
   assembly (`ZSpan.isAddFundamentalDomain'`, `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure`,
   `ZSpan.fundamentalDomain_pi_basisFun`, `addHaar_image_linearMap`, `Basis.mem_span_iff_repr_mem`).
2. Once verified, promote to a gallery entry (`src/data/proofs/`) as `verified` / `original`
   (0 sorry, 0 axiom, no `Lean.ofReduceBool`), cross-referencing the pigeonhole
   `dirichlet-approximation-theorem` entry.
3. Settle the subsumption question via the continued-fraction convergent selection, or record that
   pigeonhole/Minkowski/CF give the same `1/N` strength.

## Session 2026-06-19 — gallery promotion

**Mode:** REVISIT (problem already COMPLETE + build-verified) · **Outcome:** completed (published to gallery)

### What I did
- Re-verified `Proofs/DirichletApproximationOQ03.lean` compiles cleanly via single-file
  `lake env lean` against pinned Mathlib v4.26.0 (exit 0, 0 errors); `#print axioms
  dirichlet_via_minkowski` = `[propext, Classical.choice, Quot.sound]` (axiom-free).
- Authored the gallery entry `src/data/proofs/dirichlet-approximation-theorem-oq-03/`
  (`meta.json` + `annotations.json`): status `verified`, badge `original`, 6 sections,
  5 annotations, cross-references to the parent and the oq-02 sibling.
- `pnpm annotations:validate` does not flag this entry (anchors resolve cleanly).

### Files modified
- `src/data/proofs/dirichlet-approximation-theorem-oq-03/meta.json` (new)
- `src/data/proofs/dirichlet-approximation-theorem-oq-03/annotations.json` (new)
- `src/data/research/problems/dirichlet-approximation-theorem-oq-03.json` (knowledge)

### Next steps
- Optional sharpenings only: strict `< 1/N` via the open-boundary (area > 4) refinement;
  simultaneous (oq-02) via Minkowski instead of torus pigeonhole; reusable shear-volume lemma.
