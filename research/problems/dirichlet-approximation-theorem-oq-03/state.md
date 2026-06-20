# State: dirichlet-approximation-theorem-oq-03

**Status**: active
**Phase**: COMPLETED
**Last updated**: 2026-06-20

## Current Focus

Minkowski convex-body re-derivation of Dirichlet's approximation theorem. The full proof —
geometry, arithmetic bridge, the `volume(K) = 4` shear computation, and the unconditional Minkowski
assembly — is complete, sorry-free, axiom-free, and now **BUILD VERIFIED** in
`DirichletApproximationOQ03.lean`. Single-file elaboration via
`lake env lean Proofs/DirichletApproximationOQ03.lean` against the pinned Mathlib v4.26.0 oleans
type-checks with 0 errors/warnings/sorries; `#print axioms dirichlet_via_minkowski` reports only
`[propext, Classical.choice, Quot.sound]`. The type-check caught 7 real lemma-name/tactic drifts the
earlier source-inspection had missed (all now fixed).

## Progress

- [x] Survey Mathlib geometry-of-numbers + continued-fraction APIs.
- [x] Convex body `K(α,N)`: symmetry, convexity, closedness (sorry-free).
- [x] Arithmetic bridge: nonzero integer point of `K` ⇒ Dirichlet approximation (sorry-free).
- [x] Dirichlet's bound conditional on the Minkowski conclusion (sorry-free).
- [x] Volume computation `volume(K) = 4` via the determinant-(−1) shear `(x,y) ↦ (x, αx − y)`
      (`shear`, `box`, `body_eq_image`, `box_volume`, `body_volume`) — drafted sorry-free.
- [x] Unconditional Minkowski assembly `dirichlet_via_minkowski` from
      `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure` against the standard lattice
      `ℤ² = span ℤ (range (Pi.basisFun ℝ (Fin 2)))` — drafted sorry-free.
- [x] **Source-level Mathlib API verification** (s3, 2026-06-19): every external lemma the proof
      consumes exists in the pinned mathlib (`leanprover/lean4:v4.26.0`) with a matching signature —
      `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure`
      (`MeasureTheory/Group/GeometryOfNumbers.lean:92`, args `fund h_symm h_conv h_cpt h`),
      `ZSpan.isAddFundamentalDomain'` (`Algebra/Module/ZLattice/Basic.lean:359`),
      `ZSpan.fundamentalDomain_pi_basisFun` (`…:113`, `= Set.pi univ (Ico 0 1)`),
      `addHaar_image_linearMap` (`…/Lebesgue/EqHaar.lean:300`, `μ (f '' s) = ofReal |det f| * μ s`),
      `LinearMap.det_toLin'`, `Matrix.det_fin_two_of`, `Basis.mem_span_iff_repr_mem`. Tactic-level
      elaboration (simp lemma sets, `field_simp; ring`, term shapes) is NOT verified — needs a build.
- [x] **Build verification** of `Proofs.DirichletApproximationOQ03` (2026-06-20): single-file
      `lake env lean` against pinned Mathlib v4.26.0 type-checks cleanly (0 errors/warnings/sorries);
      `#print axioms` = `[propext, Classical.choice, Quot.sound]`. Fixed 7 compile errors the prior
      source-inspection missed. A full docker build remains an optional CI nicety, not a blocker.
- [ ] Continued-fraction subsumption (optional).

## Build status

`DirichletApproximationOQ03.lean`: 18 theorems/defs, 0 `sorry`, 0 `axiom` declarations, no
`native_decide`/`decide`. **BUILD VERIFIED (2026-06-20)** via single-file elaboration
`LAKE_UNSAFE=1 lake env lean Proofs/DirichletApproximationOQ03.lean` against the prebuilt Mathlib
v4.26.0 oleans in `proofs/.lake/packages/mathlib` — 0 errors, 0 warnings, 0 sorries. This is a sound
type-check (the file elaborates against the real Mathlib oleans the docker build would use); it
caught 7 errors source-inspection had missed: `Matrix.dotProduct`→`dotProduct`,
`addHaar_image_linearMap`→`Measure.addHaar_image_linearMap`, a natAbs cast using the real instead of
integer `abs` hypothesis (`Nat.cast_natAbs` + `abs_of_neg hneg`/`abs_of_pos hpos`), `fin_cases`
index normalisation in `shear_involutive` (explicit `show`), and redundant `tauto`/`ring`/`push_cast`
steps. `#print axioms dirichlet_via_minkowski` = `[propext, Classical.choice, Quot.sound]` (no
`sorryAx`, no `Lean.ofReduceBool`) ⇒ genuinely axiom-free / verified.
