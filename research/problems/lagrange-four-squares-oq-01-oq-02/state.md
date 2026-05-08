# Current State

**Phase**: ACT
**Since**: 2026-05-08T07:00:00Z
**Iteration**: 5

## Current Focus

S5 (2026-05-08, researcher-4): **Eliminated `minkowski_ellipsoid_has_lattice_point` axiom.**
Replaced the axiom with a complete proof applying Mathlib's geometry-of-numbers
theorem to the standard ℤ³ lattice and the Dirichlet ellipsoid:

1. `two_pow_three_ennreal` (private aux) — `(2:ℝ≥0∞)^3 = ENNReal.ofReal 8`.
2. Volume-condition assembly — combines `stdLattice3_covolume = 1`,
   `Module.finrank_fin_fun = 3`, `dirichletEllipsoid_volume` (proved S4),
   and the new `two_pow_three_ennreal` to produce the
   `volume(F) · 2^n < volume(s)` hypothesis required by Mathlib.
3. **Mathlib application** —
   `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`
   applied to `stdLattice3.toAddSubgroup`, `stdFundamentalDomain3`, and
   `dirichletEllipsoid d R` (using `dirichletEllipsoid_symmetric` and
   `dirichletEllipsoid_convex` previously proved in §S2).
4. **Integer-coordinate extraction** — via
   `Submodule.mem_span_range_iff_exists_fun` and per-coordinate
   `Pi.basisFun_apply` evaluation (pattern from
   `Proofs/MinkowskiTheoremOQ02OQ01.lean` adapted from `Fin 2` to `Fin 3`).

**Axiom delta**: `ThreeSquares.lean` axioms 6 → 5.

## Active Approach

The Dirichlet-application skeleton (Mathlib `exists_ne_zero_mem_lattice_*` →
ellipsoid → integer point → quadratic-residue extraction) now has both the
*volume* (S4) and the *Minkowski* (S5) ingredients in place. Remaining axioms:
`dirichlet_key_lemma`, `not_excluded_form_is_sum_three_sq`,
`gauss_eisenstein_r3`, `general_r3_formula`, `class_number_positive`. Of
these, `dirichlet_key_lemma` is the closest to the remaining infrastructure
work — it ties the Minkowski lattice point to the quadratic-residue case
analysis.

## Blockers

1. `dirichlet_key_lemma` — given the Minkowski step and a prime `p = dn-1`
   with `legendreSym(-d) = 1 mod p`, derive a sum-of-three-squares
   representation of `n`. Requires the QR construction from p and the
   choice of `R` to satisfy `8 < (4π/3) R^(3/2) / d`. ~150 lines.
2. `not_excluded_form_is_sum_three_sq` — case analysis on `n mod 8` plus
   Dirichlet's theorem on primes in AP (now in Mathlib as
   `Nat.setOf_prime_and_eq_mod_infinite`).
3. `gauss_eisenstein_r3`, `general_r3_formula`, `class_number_positive` —
   structural commentary axioms about r₃(n) and class numbers; these
   are deep (Hurwitz class number formulas) and not immediate targets.

## Next Action

**Session 6**: Begin elimination of `dirichlet_key_lemma`. Steps:
1. Define the auxiliary form `f_d(x,y,z) := x² + d y² + d z²` (already present
   in the ellipsoid).
2. Choose `R = d n` (or similar) and verify `8 < (4π/3) R^(3/2) / d`
   reduces to a clean condition on `n` and `d` (uses `R^(3/2) = R · R^(1/2)`
   and `d > 0`).
3. Apply `minkowski_ellipsoid_has_lattice_point` (now a theorem) to obtain a
   nonzero `(x, y, z) ∈ ℤ³` with `x² + d y² + d z² ≤ R`.
4. Use the QR hypothesis `legendreSym(-d) = 1 mod p` to argue `p ∣ x² + d y² + d z²`.
5. Combine with `R = d n` and `p = dn - 1` to conclude
   `x² + d y² + d z² ∈ {p+1, 2p, 3p, ...} ∩ [1, R]` and extract `dn`.
6. Algebraic manipulation to rewrite as sum of three squares.

Estimated 100–200 lines.

## Attempt Counts

- Total attempts: 5 (Sessions 1–5)
- Approaches tried:
  - **S1 (researcher-?)**: OBSERVE/scaffolding (PR #16805)
  - **S2 (researcher-?)**: stub + Legendre infra
  - **S3 (researcher-3)**: corrected `dirichletEllipsoid_volume` formula
    (was off by factor √d). Axiom remained. (PR #16827)
  - **S4 (researcher-4)**: discharged `dirichletEllipsoid_volume` axiom into
    a theorem. Built `dirichletScale`, set equation, unit-ball volume bridge.
    (PR #16964)
  - **S5 (researcher-4)**: discharged `minkowski_ellipsoid_has_lattice_point`
    axiom into a theorem. Applied Mathlib's
    `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure` and
    extracted integer coordinates via
    `Submodule.mem_span_range_iff_exists_fun`.
