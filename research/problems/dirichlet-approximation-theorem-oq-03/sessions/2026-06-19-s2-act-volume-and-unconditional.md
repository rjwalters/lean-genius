# Session 2026-06-19 (Session 2) — ACT: volume computation + unconditional assembly

**Mode:** REVISIT · **Outcome:** complete (drafted) — full unconditional proof, BUILD UNVERIFIED (Docker down)

## What I did

Closed the single remaining crux from Session 1 (`volume(K) = 4`) and assembled the unconditional
geometry-of-numbers proof of Dirichlet's bound, all sorry-free and axiom-free by source inspection.

Added to `Proofs/DirichletApproximationOQ03.lean`:

- **The shear.** `shear α : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := Matrix.toLin' !![1,0; α,-1]`, with
  `shear_apply_zero`/`shear_apply_one` reading off its action `(x,y) ↦ (x, αx − y)` and
  `shear_involutive` showing `T ∘ T = id`.
- **Box / body image identity.** `box` is the axis-aligned rectangle `[-N,N] × [-1/N,1/N]`;
  `body_eq_image` proves `K = shear '' box` (one-line round-trip via the involution);
  `box_eq_Icc` rewrites `box` as an `Icc`, giving `box_isCompact` and hence `body_isCompact`.
- **Volume.** `box_volume : volume (box N) = 4` via `volume_pi_pi` + `Real.volume_Icc`;
  `body_volume : volume (body α N) = 4` via `addHaar_image_linearMap` with
  `LinearMap.det_toLin'` + `Matrix.det_fin_two_of` giving `det = -1`.
- **Unconditional capstone.** `dirichlet_via_minkowski (hN : 2 ≤ N)` feeds
  `covol(ℤ²)·2^dim = 1·2² = 4 ≤ 4 = volume(K)` into
  `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure` against the standard lattice
  `span ℤ (range (Pi.basisFun ℝ (Fin 2)))`, converts lattice membership to integer coordinates via
  `Basis.mem_span_iff_repr_mem`, and discharges the `hMink` hypothesis of `dirichlet_via_convex_body`.

## Honest status

- File: 18 theorems/defs, **0 `sorry`, 0 `axiom` declarations, no `native_decide`/`decide`** (grep-confirmed; the two "sorry"/"axiom" string hits are doc-comment prose).
- **The build was NOT run.** `docker version` and `docker ps` both hung (daemon unresponsive,
  host load avg ~12–17). So the elaboration and axiom-free claims rest on **source inspection only**.
  A successful `./proofs/scripts/docker-build.sh Proofs.DirichletApproximationOQ03` is required
  before this is treated as machine-checked. Risk surface: Mathlib lemma-name/signature drift in the
  unconditional assembly (`ZSpan.isAddFundamentalDomain'`,
  `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure`,
  `ZSpan.fundamentalDomain_pi_basisFun`, `addHaar_image_linearMap`, `Basis.mem_span_iff_repr_mem`).

## Next

1. Verify the build once Docker is back; fix any lemma drift.
2. On green build, promote to a gallery entry (`src/data/proofs/`) as `verified`/`original`.
3. Optional: continued-fraction subsumption note; strict `< 1/N` via open-boundary (area > 4) refinement.
