# State: dirichlet-approximation-theorem-oq-03

**Status**: active
**Phase**: research
**Last updated**: 2026-06-19

## Current Focus

Minkowski convex-body re-derivation of Dirichlet's approximation theorem. The full proof —
geometry, arithmetic bridge, the `volume(K) = 4` shear computation, and the unconditional Minkowski
assembly — is drafted sorry-free and axiom-free in `DirichletApproximationOQ03.lean`. **Build is
UNVERIFIED this session: the Docker build daemon was unresponsive; CI / the deployer must build
`Proofs.DirichletApproximationOQ03` before this is treated as machine-checked.**

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
- [ ] **Build verification** of `Proofs.DirichletApproximationOQ03` (still blocked: Docker daemon
      unresponsive, host load avg ~26–39). CI / the deployer must run
      `./proofs/scripts/docker-build.sh Proofs.DirichletApproximationOQ03` before machine-checked.
- [ ] Continued-fraction subsumption (optional).

## Build status

`DirichletApproximationOQ03.lean`: 18 theorems/defs, 0 `sorry`, 0 `axiom` declarations, no
`native_decide`/`decide`. Build NOT run this session — `docker version`/`docker ps` hung (daemon
unresponsive, host load avg ~12–17). The sorry/axiom-free claims are by source inspection only and
require a successful `./proofs/scripts/docker-build.sh Proofs.DirichletApproximationOQ03` to confirm
the Mathlib lemma names and tactic blocks actually elaborate.
