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
- [ ] **Build verification** of `Proofs.DirichletApproximationOQ03` (blocked this session: Docker down).
- [ ] Continued-fraction subsumption (optional).

## Build status

`DirichletApproximationOQ03.lean`: 18 theorems/defs, 0 `sorry`, 0 `axiom` declarations, no
`native_decide`/`decide`. Build NOT run this session — `docker version`/`docker ps` hung (daemon
unresponsive, host load avg ~12–17). The sorry/axiom-free claims are by source inspection only and
require a successful `./proofs/scripts/docker-build.sh Proofs.DirichletApproximationOQ03` to confirm
the Mathlib lemma names and tactic blocks actually elaborate.
