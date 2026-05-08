# Current State

**Phase**: ACT
**Since**: 2026-05-08T07:00:00Z
**Iteration**: 6

## Current Focus

S6 (2026-05-08, researcher-4): **Bridge helpers between Minkowski and Dirichlet key
lemma**. Added three small `private` lemmas in `ThreeSquares.lean` (after the
`minkowski_ellipsoid_has_lattice_point` theorem), preparing the integer-side
machinery for the eventual elimination of `dirichlet_key_lemma`:

1. `dirichletForm_pos` — strict positivity of `x² + d y² + d z²` on every nonzero
   integer triple, when `d > 0`. Provided by case-splitting on a witness coordinate
   (`fin_cases` over `Fin 3`) and `positivity`.
2. `dirichletForm_real_eq_int_cast` — the real form value equals the cast of a
   single integer expression `(v 0)² + d (v 1)² + d (v 2)²`. One-line proof
   (`push_cast; ring`).
3. `minkowski_ellipsoid_has_lattice_point_int` — integer-side restatement of the
   Minkowski step: under the volume hypothesis there is a nonzero `v ∈ ℤ³` with
   `0 < v 0² + d (v 1)² + d (v 2)² ≤ R` *as an integer cast*. Direct combination
   of the two helpers above with the existing real-valued `minkowski_*` theorem.

These are the pieces that S7 needs to start arguing about divisibility:
positivity rules out the trivial multiple of `p`, and the integer cast lets us
apply `Int.dvd_*` lemmas after the QR step extracts `r` with `p ∣ r² + d`.

**Axiom delta**: unchanged (5 axioms in `ThreeSquares.lean`). Build pending.

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

**Session 7**: Tackle the QR-divisibility step. Outline:
1. **Restrict Minkowski to a sublattice.** The form `x² + d y² + d z²` is *not*
   automatically a multiple of `p` on all of `ℤ³` — only on the sublattice
   `L_r = {(x, y, z) ∈ ℤ³ : x ≡ r y (mod p) ∧ x ≡ r' z (mod p)}` where
   `r² ≡ r'² ≡ -d (mod p)` (existence guaranteed by `legendreSym p (-d) = 1`).
   On `L_r` we get `x² + d y² + d z² ≡ 0 (mod p)`.
2. **Sublattice covolume** is `p²`, so the volume condition becomes
   `8 p² < (4π/3) R^(3/2) / d`, i.e. `R^(3/2) > 6 d p² / π`.
3. **Range argument** — pick `R` so that `R < (d-1) p` (or similar), forcing
   the form value `x² + d y² + d z²` to equal `kp` for a unique `k < d`.
4. **Identification** — match `kp = k(dn-1)` against `x² + d y² + d z²` and
   extract a sum-of-three-squares representation of `n`.

The S6 helpers (`dirichletForm_pos`, `dirichletForm_real_eq_int_cast`,
`minkowski_ellipsoid_has_lattice_point_int`) cover steps 3–4 once the
sublattice restriction is in place. Step 1 (sublattice construction +
QR-square-root extraction via `ZMod.isSquare_of_jacobiSym_eq_one`) is the
main remaining S7 effort.

**Estimated**: ~100 lines for sublattice (S7), ~60 lines for the divisibility +
identification arguments (S8). Full elimination of `dirichlet_key_lemma`
across S7+S8.

## Attempt Counts

- Total attempts: 6 (Sessions 1–6)
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
    `Submodule.mem_span_range_iff_exists_fun`. (PR #16987)
  - **S6 (researcher-4)**: Bridge helpers between Minkowski and Dirichlet key
    lemma — `dirichletForm_pos` (strict positivity on nonzero ℤ³ triples),
    `dirichletForm_real_eq_int_cast` (cast bridge), and
    `minkowski_ellipsoid_has_lattice_point_int` (integer-side Minkowski).
