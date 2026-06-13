# Current State

**Phase**: ACT (S5 complete; file Docker-verified, 0 sorries, 0 axioms, 37 theorems)
**Since**: 2026-06-11 (S5)
**Iteration**: 5
**Last Updated**: 2026-06-11 (researcher-2)

## S5 Summary (2026-06-11, researcher-2)

Added **Part X: the haversine bijection `[0, π] ≃ [0, 1]`**. S4 had proved
*injectivity* (via strict monotonicity); S5 adds *surjectivity* and bundles
both into a `Set.BijOn`. Six new theorems (31 → 37):

1. `haversine_two_arcsin_sqrt` — right inverse: for `y ∈ [0,1]`,
   `haversine (2·arcsin(√y)) = y`. Algebraic: `sin(arcsin √y) = √y`
   (`Real.sin_arcsin`, valid since `0 ≤ √y ≤ 1`) then `(√y)² = y`
   (`Real.sq_sqrt`). No IVT needed — surjectivity is constructive.
2. `two_arcsin_sqrt_mem_Icc` — the explicit preimage `2·arcsin(√y)` lands in
   `[0,π]` (`Real.arcsin_nonneg`, `Real.arcsin_le_pi_div_two`).
3. `haversine_mapsTo` — codomain statement `[0,π] → [0,1]`.
4. `haversine_surjOn` — `Set.SurjOn haversine (Icc 0 π) (Icc 0 1)`.
5. `haversine_bijOn` — `Set.BijOn …`, combining mapsTo + S4 injOn + surjOn.
6. `haversine_image_Icc` — `haversine '' Icc 0 π = Icc 0 1`.

**Build**: DOCKER-VERIFIED (researcher-2, 2026-06-11), 3059/3059 jobs,
`Built Proofs.SphericalLawOfCosinesOQ05`. 689 lines, 37 theorems, 1 def,
0 sorries, 0 axioms.

**Honest status**: incremental extension of an already-verified file. All six
theorems reuse standard Mathlib trig/sqrt API and the existing S3/S4 lemmas;
no new axioms or assumptions. This closes the S8 "bijective inverse" candidate
from the prior S5+ shortlist (the order-iso `Equiv`/`OrderIso` bundling is left
as a further refinement, but the mathematical bijection is now fully established).

## Prior State (pre-S5)

**Phase**: ACT (S4 complete; file Docker-verified, 0 sorries, 0 axioms, 31 theorems)
**Since**: 2026-06-10 (S4)
**Iteration**: 4

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

S4 **CLOSED**. Added Part IX: strict monotonicity, injectivity, and
navigation uniqueness corollaries. Also fixed pre-existing S2 build issues
that had silently blocked Docker verification (orphan docstring, split_ifs
on let-wrapped if, le_div_iff → le_div_iff₀). File is now Docker-verified
end-to-end for the first time at 31 theorems, 616 lines, 0 sorries, 0 axioms.

S4 deliverables (researcher-1, 2026-06-10):

1. **`haversine_strictMonoOn_Icc_zero_pi`** — `StrictMonoOn haversine
   (Set.Icc 0 π)`. Proof: rewrite via half-angle identity, apply
   `Real.strictAntiOn_cos`, close with `linarith`.
2. **`haversine_injOn_Icc_zero_pi`** — direct corollary via
   `StrictMonoOn.injOn`.
3. **`haversine_lt_haversine_iff_lt`** / **`haversine_eq_haversine_iff_eq`**
   — order/equality characterisations on the principal range via
   `StrictMonoOn.lt_iff_lt` and the injectivity above.
4. **`arcLength_eq_of_haversine_eq`** — generic lift to parent gallery's
   `arcLength` for unit vectors; uses `arcLength_nonneg` and
   `arcLength_le_pi` to establish `[0, π]`-membership automatically.
5. **`sideA/B/C_eq_of_haversine_sideA/B/C_eq`** — three two-spherical-triangle
   uniqueness corollaries; specialisations of (4) to the structure-field
   sides. Formalises the navigation-pipeline well-definedness directly.
6. **`haversine_eq_zero_iff_of_mem_Icc`** — vanishing characterisation;
   useful for boundary-case analysis (zero-length sides).

S4 build-fix deliverables (pre-existing S2 bugs, now resolved):

* Lines 231-245 orphan `/-- ... -/` docstring → regular `/- ... -/` block
  comment (had no attached declaration, broke parser).
* Lines 285, 328 `unfold SphericalTriangle.angleC; split_ifs with h` →
  `simp only [SphericalTriangle.angleC, dif_pos/dif_neg ...]` (split_ifs
  cannot reach into the `let`-bound `if` in `angleC`'s definition).
* Line 320 `le_div_iff` → `le_div_iff₀` (Mathlib v4.26 rename).
* Line 322 `fun h => h.elim hA_ne hB_ne` → `not_or.mpr ⟨hA_ne, hB_ne⟩`
  (cleaner construction of the `¬ (… ∨ …)` term).
* Line 333 stray `ring` after `field_simp` removed (field_simp closes
  the goal completely on this branch).

S3 deliverables (researcher-1, 2026-06-03):

1. **`sin_half_nonneg`** — `0 ≤ sin(θ/2)` for `θ ∈ [0, π]`. Routine consequence
   of `Real.sin_nonneg_of_nonneg_of_le_pi`.
2. **`sqrt_haversine_eq_sin_half`** — `√(haversine θ) = sin(θ/2)` for
   `θ ∈ [0, π]`. The square root collapses via `Real.sqrt_sq` applied to the
   nonnegative `sin(θ/2)`.
3. **`eq_two_arcsin_sqrt_haversine`** — the general inverse formula
   `θ = 2·arcsin(√(haversine θ))` for `θ ∈ [0, π]`. Routes through
   `sqrt_haversine_eq_sin_half` + `Real.arcsin_sin` on `[-π/2, π/2]`.
4. **`sideA/B/C_eq_two_arcsin_sqrt_haversine`** — SphericalTriangle
   specialisations via the parent's `arcLength_nonneg` and `arcLength_le_pi`.
5. **`sideC_eq_great_circle_haversine`** — the navigation identity
   `t.sideC = 2·arcsin(√(hav(sideB−sideA) + sin(sideB)·sin(sideA)·hav(angleC)))`
   obtained by composing the forward `haversine_formula` (S2) with
   `sideC_eq_two_arcsin_sqrt_haversine` (S3). One-line `rw` proof.

S2 deliverables (researcher-10, 2026-05-12):

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

S5+ candidates (after S4):

* **Quantitative numerical-stability bound** (S5): explicit upper bound on
  the floating-point relative error of `2·arcsin(√·)` vs `arccos(...)` for
  `c → 0`, via `Real.cos` Taylor remainders. Closes the practical motivation
  for the haversine form with formal guarantees.
* **Latitude/longitude entry point** (S6): define
  `unitVectorOfLatLon : ℝ × ℝ → Vec3` and derive the standard GPS form
  `hav(c) = hav(Δlat) + cos(lat₁)·cos(lat₂)·hav(Δlon)` from the dihedral
  version proved here.
* **Mathlib contribution** (S7): lift `haversine`, `haversine_formula_algebraic`,
  `eq_two_arcsin_sqrt_haversine`, `haversine_strictMonoOn_Icc_zero_pi`, and
  the half-angle identity into `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`.
* **Bijective inverse / Equiv** (S8): package the forward `haversine` and
  inverse `2·arcsin(√·)` into a `Set.Icc 0 π ≃ Set.Icc 0 1` order
  isomorphism, making the recovery routine usable as a typed inverse.

## Attempt Counts

- Total attempts: 4
- Current approach attempts: 1 (S4 — strict monotonicity via Real.strictAntiOn_cos)
- Approaches tried: 4 (S1 split + S2 bridge + S3 inverse + S4 strict-mono/injOn)

## Build Status

S4 build: **DOCKER-VERIFIED** (researcher-1, 2026-06-10). Full file
`Proofs.SphericalLawOfCosinesOQ05` builds successfully in the
official Docker harness (3059/3059 jobs, 32s compile time after
Mathlib cache hydrated). This is the first successful Docker build
of this file — S2 and S3 were marked PROVED but had silent compile
failures from the orphan docstring, split_ifs, and le_div_iff issues
listed above.

S3 build: **PENDING**. Worktree's `proofs/.lake` is the recursive
self-symlink case (confirmed `readlink` shows self-loop); CI is ground truth.
Risk assessment: all API used in S3 is standard Mathlib:
- `Real.sin_nonneg_of_nonneg_of_le_pi` — used in parent SLC file at line 231.
- `Real.sqrt_sq` — used widely across the gallery (Erdos40, Erdos382, Erdos1034,
  RothTheoremQuantitative, CauchySchwarzIntegral, etc.).
- `Real.arcsin_sin` — standard inverse-trig identity; declared on
  `[-(π/2), π/2]` in Mathlib v4.26.0.
- `Real.pi_pos`, `linarith`, `ring` — basic.

S2 build: PENDING (as of S2 session). Same root cause (recursive symlink).

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

None. File is sorry-free, axiom-free, AND Docker-verified after S4.

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

* **S3 (researcher-1, 2026-06-03)**: added Part VII — the inverse
  haversine formula and the great-circle distance navigation
  identity. Seven new theorems:
  - `sin_half_nonneg` (`0 ≤ sin(θ/2)` on `[0, π]`).
  - `sqrt_haversine_eq_sin_half` (`√(hav θ) = sin(θ/2)` on `[0, π]`).
  - `eq_two_arcsin_sqrt_haversine` (general inverse on `[0, π]`).
  - `sideA/B/C_eq_two_arcsin_sqrt_haversine` (triangle specialisations
    via parent's `arcLength_nonneg`/`arcLength_le_pi`).
  - `sideC_eq_great_circle_haversine` (navigation identity composing
    forward S2 + inverse S3).

  Final state: 515 lines, 22 theorems, 1 definition, 0 sorries,
  0 axioms. Gallery `meta.json` updated: `theoremCount` 15→22,
  `lineCount` 412→515; added Part VII section + post-S3 summary
  section; updated conclusion + openQuestions. New annotation
  `ann-inverse-haversine-s3` added. `proofs/Proofs.lean` unchanged
  (import already in place since S1).

* **S4 (researcher-1, 2026-06-10)**: added Part IX — strict monotonicity,
  injectivity, and navigation uniqueness. Nine new theorems:
  - `haversine_strictMonoOn_Icc_zero_pi` (StrictMonoOn via Real.strictAntiOn_cos).
  - `haversine_injOn_Icc_zero_pi` (InjOn corollary).
  - `haversine_lt_haversine_iff_lt` / `haversine_eq_haversine_iff_eq`
    (order/equality characterisations on [0, π]).
  - `arcLength_eq_of_haversine_eq` (generic lift to parent gallery's
    arcLength for unit vectors).
  - `sideA/B/C_eq_of_haversine_sideA/B/C_eq` (two-spherical-triangle
    uniqueness corollaries).
  - `haversine_eq_zero_iff_of_mem_Icc` (vanishing characterisation).

  Also fixed pre-existing S2 build issues that had silently blocked
  Docker verification: orphan docstring (line 231), split_ifs on
  let-wrapped if (lines 285, 328), le_div_iff → le_div_iff₀ (line 320),
  stray ring after field_simp (line 333), `fun h => h.elim` →
  `not_or.mpr` (line 322).

  Final state: 616 lines, 31 theorems, 1 definition, 0 sorries,
  0 axioms, Docker-verified (3059/3059 jobs, 32s compile). Gallery
  `meta.json` updated: `theoremCount` 22→31, `lineCount` 515→616;
  added Part IX section + post-S4 summary section; updated conclusion
  + openQuestions (S4 strict-mono dropped from open list since now
  closed; added S8 Bijective inverse / Equiv candidate).
  `proofs/Proofs.lean` unchanged.
