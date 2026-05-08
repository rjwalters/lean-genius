# Current State

**Phase**: ACT
**Since**: 2026-05-08T05:35:00Z
**Iteration**: 4

## Current Focus

S4 (2026-05-08, researcher-4): **Eliminated `dirichletEllipsoid_volume` axiom.**
Built four supporting theorems and one definition that turn the previously
axiomatized closed-form volume into a `theorem` derived from Mathlib:

1. `dirichletScaleMatrix` / `dirichletScale` — diagonal scaling map
   `T = diag(√R, √(R/d), √(R/d))` as a `LinearMap (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)`.
2. `dirichletScale_det` — `LinearMap.det T = R^(3/2)/d` for `d > 0`, `R > 0`.
3. `dirichletEllipsoid_eq_image` — `dirichletEllipsoid d R = T '' unitEuclideanBall3`.
4. `unitEuclideanBall3_volume` — `vol(unitEuclideanBall3) = 4π/3`, via the
   `WithLp.ofLp` measure-preserving bridge to `EuclideanSpace ℝ (Fin 3)` plus
   `EuclideanSpace.volume_closedBall_fin_three`.
5. `dirichletEllipsoid_volume` (now `theorem`, not `axiom`) — assembles 1–4 via
   `MeasureTheory.Measure.addHaar_image_linearMap`.

**Axiom delta**: `ThreeSquares.lean` axioms 7 → 6.

## Active Approach

The Dirichlet-application skeleton (Mathlib `exists_ne_zero_mem_lattice_*` →
ellipsoid → integer point → quadratic-residue extraction) is still gated by
the remaining axioms (`minkowski_ellipsoid_has_lattice_point`,
`dirichlet_key_lemma`, `not_excluded_form_is_sum_three_sq`,
`gauss_eisenstein_r3`, `general_r3_formula`, `class_number_positive`).
Eliminating any of the four "deep" axioms remains the open work.

## Blockers

1. `minkowski_ellipsoid_has_lattice_point` — applies Mathlib's
   `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure` with the
   newly-proved volume formula. Mostly mechanical (~100 lines of plumbing
   between `Submodule ℤ (Fin 3 → ℝ)` and `AddSubgroup`). Best next target.
2. `dirichlet_key_lemma` — requires the quadratic-residue-→ integer-point
   reduction; involves `legendreSym(-d) = 1 mod p` case analysis.
3. `not_excluded_form_is_sum_three_sq` — the user-facing sufficiency axiom;
   reduces to applying `dirichlet_key_lemma` for each `n mod 8` case plus
   Dirichlet's theorem on primes in AP (now in Mathlib as
   `Nat.setOf_prime_and_eq_mod_infinite`).

## Next Action

**Session 5**: Eliminate `minkowski_ellipsoid_has_lattice_point` by setting
up the AddSubgroup-vs-Submodule bridge for ℤ³ and applying
`Mathlib.MeasureTheory.Group.GeometryOfNumbers.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`.
Estimated ~120 lines. With the new `dirichletEllipsoid_volume` theorem the
volume hypothesis is now derivable; only the lattice-isomorphism plumbing
remains.

## Attempt Counts

- Total attempts: 4 (Sessions 1–4)
- Approaches tried:
  - **S1 (researcher-?)**: OBSERVE/scaffolding (PR #16805)
  - **S2 (researcher-?)**: stub + Legendre infra
  - **S3 (researcher-3)**: corrected `dirichletEllipsoid_volume` formula
    (was off by factor √d). Axiom remained. (PR #16827)
  - **S4 (researcher-4)**: discharged the axiom into a theorem. Built
    `dirichletScale`, set equation, unit-ball volume bridge.
