# Current State

**Phase**: OBSERVE → ACT (S1 complete; S2 ready)
**Since**: 2026-05-12 (S1)
**Iteration**: 1
**Last Updated**: 2026-05-12 (researcher-5)

## Current Focus

S1 (researcher-5) — scaffold OQ-05 of the parent
`spherical-law-of-cosines` gallery entry: the **haversine formula**

  hav(c) = hav(a − b) + sin(a) · sin(b) · hav(C)

where `hav(θ) := sin²(θ/2)`.

## Active Approach

**Two-layer split**: prove the *pure algebraic* identity
unconditionally; record the `SphericalTriangle` version as the open
`sorry`.

* `haversine_formula_algebraic`: given `cos c = cos a · cos b + sin
  a · sin b · cos C` as a real-number hypothesis, derive
  `haversine c = haversine (a−b) + sin a · sin b · haversine C` by
  linear arithmetic using `Real.cos_sub` and the half-angle identity
  `Real.cos_two_mul` + `Real.sin_sq_add_cos_sq`.
* `haversine_formula` (SphericalTriangle version): recorded as
  `sorry`. The remaining gap is the conversion of the parent's
  projection-inner-product term `⟨projectPerp t.A t.C, projectPerp
  t.B t.C⟩` (from `spherical_law_of_cosines_trig`) into the
  trigonometric `sin(sideB) · sin(sideA) · cos(angleC)` form, which
  requires a case split on the degenerate branch of `angleC`.

## Next Action

**S2**: discharge `haversine_formula` from
`haversine_formula_algebraic` by:

1. Case-split on whether `‖projectPerp t.A t.C‖ = 0` or
   `‖projectPerp t.B t.C‖ = 0`.
2. **Non-degenerate branch** (both nonzero): unfold
   `t.angleC` to its `Real.arccos` definition, apply
   `Real.cos_arccos` (with the `|·| ≤ 1` bound from
   Cauchy–Schwarz), and use `norm_projectPerp_eq_sin` to identify
   `‖projectPerp t.A t.C‖ = sin t.sideB` and `‖projectPerp t.B
   t.C‖ = sin t.sideA`. This converts the inner-product term to
   `sin sideB · sin sideA · cos angleC` exactly.
3. **Degenerate branch**: either projection has zero norm, so
   `‖projectPerp t.A t.C‖ = 0 ⇒ sin t.sideB = 0 ⇒ t.sideB ∈ {0,
   π}`. The cross-term `sin sideB · sin sideA · hav angleC`
   vanishes regardless of `hav angleC`. The identity reduces to
   `hav sideC = hav(sideB − sideA)`, which follows from `sin
   sideB = 0 ⇒ cos sideB = ±1` (case split) + the parent's
   `cos_sideC`, `cos_sideB`.

S3 candidates (after S2):

* **Inverse formula** `Real.sideC_eq_two_arcsin_sqrt_hav`: extract
  `sideC = 2 · arcsin(√(hav sideC))` from `haversine_formula` for
  the canonical great-circle distance computation.
* **Numerical-stability application**: explicit error bound for the
  haversine vs `arccos` evaluation paths.
* **Mathlib contribution**: lift `haversine` and the algebraic
  identity into `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1 (S1 scaffold)
- Approaches tried: 1 (split algebraic + SphericalTriangle)

## Build Status

S1 build: **PENDING**. Worktree's `proofs/.lake` is the recursive
self-symlink case; CI is ground truth.

S1 risk profile:
* All Mathlib API used (`Real.cos_two_mul`, `Real.sin_sq_add_cos_sq`,
  `Real.cos_sub`, `Real.cos_neg`, `Real.cos_pi`, `Real.neg_one_le_cos`,
  `sq_nonneg`) is standard and exercised elsewhere in the gallery
  (`LawOfCosinesOQ01OQ04.lean` line 73 uses `Real.cos_two_mul`).
* `haversine_formula_algebraic` proof is `rw + linarith` after
  unfolding the half-angle identity and `cos_sub` — a pattern that
  works robustly across Mathlib versions.
* No new structures, no new imports beyond `Proofs.SphericalLawOfCosines`.

## Blockers

None for S1. The S2 deferred work requires careful case-split on
`Real.arccos` degenerate behaviour, which is fully tracked in the
parent file's `SphericalTriangle.angleC` definition.

## Session log

* **S1 (researcher-5, 2026-05-12)**: created
  `proofs/Proofs/SphericalLawOfCosinesOQ05.lean` (297 lines, 12
  proved theorems + 1 sorry on `haversine_formula`, 1 definition,
  0 axioms). Gallery entry created at
  `src/data/proofs/spherical-law-of-cosines-oq-05/` with meta.json
  (6 sections, 6 annotations) + index.ts. Research metadata at
  `research/problems/spherical-law-of-cosines-oq-05/` and
  `src/data/research/problems/spherical-law-of-cosines-oq-05.json`.
  Imports updated in `proofs/Proofs.lean`.
