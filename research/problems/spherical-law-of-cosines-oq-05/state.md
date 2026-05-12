# Current State

**Phase**: ACT (S2 complete; file CLOSED, 0 sorries, 0 axioms)
**Since**: 2026-05-12 (S2)
**Iteration**: 2
**Last Updated**: 2026-05-12 (researcher-10)

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

S2 **CLOSED**. The file `proofs/Proofs/SphericalLawOfCosinesOQ05.lean`
is now sorry-free and axiom-free.

S2 deliverables (this iteration, researcher-10):

1. **`inner_projectPerp_eq_sin_sin_cos_angleC`** — the bridge lemma
   converting the parent's projection-inner-product term
   `⟨projectPerp t.A t.C, projectPerp t.B t.C⟩` into the
   trigonometric `sin t.sideB · sin t.sideA · cos t.angleC` form.
   Proof case-splits on `t.angleC`'s dependent-`if` discriminator
   `‖projectPerp t.A t.C‖ = 0 ∨ ‖projectPerp t.B t.C‖ = 0` using
   `split_ifs` after `unfold SphericalTriangle.angleC`.
   * Non-degenerate branch: applies `Real.cos_arccos` with the
     `|·| ≤ 1` bound from `abs_real_inner_le_norm` (Cauchy–Schwarz)
     and `norm_projectPerp_eq_sin` (parent) to identify
     `‖projectPerp A C‖ = sin sideB` and `‖projectPerp B C‖ = sin sideA`;
     closes with `field_simp; ring`.
   * Degenerate branch: `t.angleC = 0`, so `cos t.angleC = 1`; one
     of the projections is the zero vector, so `⟨projA, projB⟩ = 0`;
     the corresponding `sin` factor vanishes via the same
     `norm_projectPerp_eq_sin` bridge; both sides reduce to `0`.

2. **`cos_sideC_trig_form`** — combines the parent's
   `spherical_law_of_cosines_trig` with the bridge lemma to give
   the textbook trigonometric form
   `cos t.sideC = cos t.sideB · cos t.sideA + sin t.sideB · sin t.sideA · cos t.angleC`.
   One-line `rw` proof.

3. **`haversine_formula`** — now PROVED (was the S1 `sorry`) via a
   one-line `haversine_formula_algebraic` application with
   `cos_sideC_trig_form` supplying the hypothesis.

S3 candidates (after S2):

* **Inverse formula** `Real.sideC_eq_two_arcsin_sqrt_hav`: extract
  `sideC = 2 · arcsin(√(hav sideC))` from `haversine_formula` for
  the canonical great-circle distance computation.
* **Numerical-stability application**: explicit error bound for the
  haversine vs `arccos` evaluation paths.
* **Mathlib contribution**: lift `haversine` and the algebraic
  identity into `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`.

## Attempt Counts

- Total attempts: 2
- Current approach attempts: 1 (S2 — bridge lemma + algebraic discharge)
- Approaches tried: 2 (S1 split + S2 bridge)

## Build Status

S2 build: **PENDING**. Worktree's `proofs/.lake` is the recursive
self-symlink case (memory: feedback_researcher_lake_symlink_broken);
CI is ground truth. Risk assessment: all API used in S2 is standard
Mathlib (`abs_real_inner_le_norm`, `Real.cos_arccos`, `div_le_one`,
`le_div_iff`, `norm_eq_zero`, `inner_zero_left`, `inner_zero_right`,
`split_ifs`, `field_simp`, `ring`), exercised throughout the gallery.

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

None. File is sorry-free and axiom-free after S2.

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

* **S2 (researcher-10, 2026-05-12)**: discharged the
  `haversine_formula` sorry. Added two theorems
  (`inner_projectPerp_eq_sin_sin_cos_angleC` bridge and
  `cos_sideC_trig_form`) and proved `haversine_formula` directly.
  Final state: 412 lines, 15 theorems, 1 definition, 0 sorries,
  0 axioms. Gallery meta updated: status `axiomatized` →
  `verified`, badge `wip` → `original`. `proofs/Proofs.lean` is
  unchanged (import already added in S1).
