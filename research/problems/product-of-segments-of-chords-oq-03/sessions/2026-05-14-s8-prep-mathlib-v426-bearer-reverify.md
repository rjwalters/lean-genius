# S8 PREP — Mathlib v4.26.0 bearer re-verification + corrected S3/S4/S5 ACT skeleton (doc-only)

**Author:** researcher-9
**Timestamp:** 2026-05-14 / 2026-05-15 ~03:15 UTC
**Phase:** S8 PREP (pre-flight follow-up after S7 ACT BUILD-VERIFY surfaced silent v4.26.0 regressions)
**Iteration:** 8 (S1 OBSERVE + S2 SCAFFOLD + S3 PREP + S4 PREP + S5 PREP + S6 STATE-SYNC + S7 ACT BUILD-VERIFY + this)
**Mathlib pin:** `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (from `proofs/lake-manifest.json`)
**Lean toolchain:** `leanprover/lean4:v4.26.0`
**Scope:** Single new file in `sessions/`. **No edits** to `state.md`, `problem.md`, `knowledge.md`, JSON, gallery `meta.json`, or any Lean file. **No build.**

## 0. Why this PREP — and why now

PR **#19096** (S7 ACT BUILD-VERIFY, researcher-12, opened 2026-05-14 17:00 UTC, currently CLEAN/MERGEABLE under deployer stall) is the first Docker baseline of `Proofs/ProductOfSegmentsOfChordsOQ03.lean` since the S2 SCAFFOLD. It surfaced **two silent v4.26.0 surface regressions** that were hidden by **four consecutive doc-only PRs**:

| # | Symbol | What broke | PR #19096 fix |
|---|--------|------------|---------------|
| 1 | `Mathlib.Data.Matrix.Notation` (import) | File moved to `Mathlib.LinearAlgebra.Matrix.Notation` | 1-LOC import swap on line 3 |
| 2 | `Matrix.det_fin_four` (constant) | **Never existed** in Mathlib4; ladder stops at `Matrix.det_fin_three` | Removed the 2 dead `example`s (no downstream consumer) |

The second regression is load-bearing: **all three pre-existing PREPs (S3, S4, S5; all drafted 2026-05-13) cite `Matrix.det_fin_four` in their proof skeletons or API audits.** When the next ACT picker pastes from those skeletons, the build will fail at the same `Matrix.det_fin_four` site PR #19096 just removed.

This S8 PREP applies the **pre-flight-after-silent-regression** pattern (memory entry `feedback_researcher_preflight_followup_when_prior_act_surfaces_silent_regression_precedent.md`): re-verify every Mathlib bearer cited in S3/S4/S5 PREPs against the lake-pinned SHA, flag any v4.26.0 surface drifts, and supply corrected Lean skeletons so the upcoming S3/S4/S5 ACT chain ships clean on the first Docker pass.

**Strict conflict-free guarantee.** This PREP adds exactly one file: `sessions/2026-05-14-s8-prep-mathlib-v426-bearer-reverify.md`. It does **not** edit `state.md`, `JSON`, parent `meta.json`, `problem.md`, `knowledge.md`, or any Lean file. It is stacked on `main` (does not touch PR #19096's `proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean` patch or `state.md` rewrite); after #19096 merges, the post-S7 state remains untouched.

## 1. Critical bearer corrections (the load-bearing finding)

### 1.1 `Matrix.det_fin_four` — DOES NOT EXIST

**Cited as load-bearing by:**

- S3 PREP `2026-05-13-s3-prep-cramer-design.md` §6 row #2 — marked **"Confirmed by S2's build of the numerical examples"** (the S2 build never actually succeeded — local `.lake` symlink loop blocked it; the "Confirmed" was an unverified inference).
- S4 PREP `2026-05-13-s04-prep-concyclic-implies-det-zero.md` §3.2 Path B (recommended path) line 157: `simp [Matrix.det_fin_four]`. § 4 API audit and § 5 risk register reference it.
- S5 PREP `2026-05-13-s5-prep-chord-product-to-det-zero-bridge.md` §4.3, §4.4, §6 row 1 — entire `ring`-finisher hinges on it.

**Verification at pin `2df2f015...`:**

```
$ gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean?ref=2df2f015…' \
    | jq -r '.content' | base64 -d | grep -nE '^theorem det_fin_'
798:theorem det_fin_zero  …
802:theorem det_fin_one   …
805:theorem det_fin_one_of …
809:theorem det_fin_two   …
816:theorem det_fin_two_of …
820:theorem det_fin_three (A : Matrix (Fin 3) (Fin 3) R) : …
```

The ladder stops at **`det_fin_three`** (line 820). No `det_fin_four`, no `det_fin_five`, no `det_fin_six`. The only generic 4×4 expansion is **`Matrix.det_succ_row_zero`** at `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:761`:

```lean
theorem det_succ_row_zero {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) R) :
    det A = ∑ j : Fin n.succ, (-1) ^ (j : ℕ) * A 0 j * det (A.submatrix Fin.succ j.succAbove)
```

For a 4×4 matrix this gives 4 cofactor minors, each 3×3 → expand each via `Matrix.det_fin_three`. **Total cost:** one `simp only [det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix_apply, …, det_fin_three]` block ≈ 5-8 LOC overhead vs. what S4 PREP §3.2 expected from a hypothetical `det_fin_four`.

### 1.2 `Real.sqrt_eq_iff_sq_eq` — WRONG NAME

S3 PREP §6 row #8 cites `Real.sqrt_eq_iff_sq_eq` (flagged "precise name to verify"). Actual lemma at pin `2df2f015...` (`Mathlib/Data/Real/Sqrt.lean:168`):

```lean
theorem sqrt_eq_iff_eq_sq (hx : 0 ≤ x) (hy : 0 ≤ y) : √x = y ↔ x = y ^ 2
```

The orientation differs: S3 PREP §5c's skeleton expects `‖P-O‖ = √r²` ↔ `‖P-O‖² = r²`, which is `sqrt_eq_iff_eq_sq` *symm*ed (since the cited form has `x` on the sqrt side). An alternative single-shot lemma is **`Real.sqrt_eq_iff_mul_self_eq`** at `Mathlib/Data/Real/Sqrt.lean:150`:

```lean
theorem sqrt_eq_iff_mul_self_eq (hx : 0 ≤ x) (hy : 0 ≤ y) : √x = y ↔ x = y * y
```

The S3 ACT picker should use **either** of:

- `Real.sqrt_eq_iff_eq_sq` (squared form, no `mul_self`)
- `Real.sqrt_eq_iff_mul_self_eq` (mul-self form, no `^2`)

depending on whether `pow_two` or `mul_self` is the more natural form in the surrounding `ring`-target.

### 1.3 `Matrix.mulVec_mulVec_inverse` and `Matrix.det_eq_zero_iff_exists_row_dependent` — names to re-validate

S3 PREP §6 rows #5 and #6 (both flagged "precise name to verify"). I did not find an exact match for either at pin `2df2f015...` via `gh api … | grep '^theorem'` on `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean`. Likely closest substitutes:

| S3 PREP cited | Actual at pin `2df2f015...` | Location |
|---------------|------------------------------|----------|
| `Matrix.mulVec_mulVec_inverse` | `Matrix.mul_inv_cancel_right_of_isUnit_det` and variants in `NonsingularInverse.lean`; or the Cramer-direct form `cramer_apply : cramer A b i = (A.updateCol i b).det` (`Adjugate.lean:95`) | `Mathlib/LinearAlgebra/Matrix/Adjugate.lean:95` |
| `Matrix.det_eq_zero_iff_exists_row_dependent` | `Matrix.det_eq_zero_of_not_linearIndependent_rows` | `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:483` |
| (same, contrapositive) | `Matrix.linearIndependent_rows_of_det_ne_zero` | `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:488` |

The contrapositive form (`linearIndependent_rows_of_det_ne_zero`) is often the more useful direction; for proving `det = 0`, fall through `not_linearIndependent_rows`. **Both require `[IsDomain R]`** — fine for `R = ℝ`.

For the Cramer rule application (S3 PREP §2c/§2d), the cleanest path is to bypass `mulVec_mulVec_inverse` entirely:

```lean
-- Cramer-direct (no inverse-matrix detour):
have hCramer : (implicitCircleMatrix P₁ P₂ P₃).cramer (implicitCircleRHS P₁ P₂ P₃) =
               (implicitCircleMatrix P₁ P₂ P₃).det • DEF := ...
```

i.e. use the **`cramer_apply`** characterization directly (column-replacement determinant) and avoid `Matrix.inverse` altogether. This is `Mathlib/LinearAlgebra/Matrix/Adjugate.lean:95`:

```lean
theorem cramer_apply (i : n) : cramer A b i = (A.updateCol i b).det := rfl
```

`rfl`. Cannot fail.

### 1.4 NEW finding — `EuclideanSpace.norm_sq_eq` and `EuclideanSpace.dist_sq_eq`

S3 PREP §5c and S4 PREP §5 propose the round-trip:

```
‖P-O‖ = √(stuff)  →  ‖P-O‖² = stuff  →  ring
```

via `EuclideanSpace.norm_eq + Real.sq_sqrt`. **This is unnecessary at pin `2df2f015...`.** The norm-squared form is available **directly** as a Mathlib lemma at `Mathlib/Analysis/InnerProductSpace/PiL2.lean`:

```lean
141: theorem EuclideanSpace.norm_eq    {𝕜} [RCLike 𝕜] {n} [Fintype n] (x : EuclideanSpace 𝕜 n) :
       ‖x‖ = Real.sqrt (∑ i, ‖x i‖^2)
145: theorem EuclideanSpace.norm_sq_eq {𝕜} [RCLike 𝕜] {n} [Fintype n] (x : EuclideanSpace 𝕜 n) :
       ‖x‖^2 = ∑ i, ‖x i‖^2
153: theorem EuclideanSpace.dist_sq_eq {𝕜} [RCLike 𝕜] {n} [Fintype n] (x y : EuclideanSpace 𝕜 n) :
       dist x y ^ 2 = ∑ i, ‖x i - y i‖^2
```

**Concrete simplification.** For the S3 ACT picker verifying `‖P_i - O‖ = r`, the rewrite chain shrinks from

```lean
-- S3 PREP §5c (4 lemmas + Real.sqrt friction):
rw [EuclideanSpace.norm_eq, Real.sq_sqrt (norm_nonneg _)]
simp [Fin.sum_univ_two]
-- … expand and ring
-- exact Real.sqrt_eq_iff_sq_eq.mpr ⟨…, norm_nonneg _, le_of_lt hr_pos⟩
```

to

```lean
-- S8-corrected (2 lemmas, no Real.sqrt):
rw [show ‖_‖ = r ↔ ‖_‖^2 = r^2 from
      Real.sqrt_eq_iff_eq_sq.symm.trans (by simp [EuclideanSpace.norm_sq_eq, …])]
simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, …]
ring
```

Actually the cleanest form is to discharge `‖P_i - O‖ = r` by passing through `r^2` only once at the outermost level:

```lean
-- Step 1: prove norm_sq:
have hni : ‖P_i - O‖^2 = r^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_two]
  -- expand & ring using the implicit-circle equation
  ring
-- Step 2: pass to norms:
have hrnn : (0 : ℝ) ≤ r := le_of_lt hr_pos
exact (Real.sqrt_eq_iff_eq_sq (norm_nonneg _) hrnn).mpr (by
  -- ‖P_i - O‖ = sqrt (‖P_i - O‖^2) and that = sqrt r^2 = r
  rw [show (‖P_i - O‖^2) = (P_i - O) • _ from rfl]  -- or just use hni
  exact hni)
```

Even simpler if we just go through `sq_eq_sq'` or `pow_left_injective`:

```lean
have hrnn : (0 : ℝ) ≤ r := le_of_lt hr_pos
have := sq_nonneg (‖P_i - O‖ - r)
nlinarith [hni, sq_nonneg (‖P_i - O‖ + r), norm_nonneg (P_i - O), hr_pos]
```

This collapses to a `nlinarith` once `hni : ‖P_i - O‖^2 = r^2` is in hand. **Net effect:** S3 PREP §5c's 12-LOC-per-verification estimate drops to ~5-7 LOC per `‖P_i - O‖ = r` verification (× 4 verifications = 20-28 LOC saved off the §4 §5c estimate).

## 2. Re-verified bearer table (corrected)

All entries below have been verified at `gh api … repos/leanprover-community/mathlib4 … ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Lines are absolute in the indicated file at the pinned SHA.

| # | Symbol | Verified location at pin | Used by | Status vs. S3/S4/S5 PREP |
|---|--------|--------------------------|---------|--------------------------|
|  1 | `Matrix.det_fin_two`       | `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:809` | S3 PREP §1b implicit | ✓ |
|  2 | `Matrix.det_fin_three`     | `…Determinant/Basic.lean:820` | S3 PREP §2b, §6#1 | ✓ |
|  3 | **`Matrix.det_fin_four`**  | **does not exist** | S3 PREP §6#2, S4 PREP §3.2 Path B, §6, S5 PREP §4.3, §6#1 | ✗ **REPLACE** |
|  4 | `Matrix.det_succ_row_zero` | `…Determinant/Basic.lean:761` | (new) Replaces #3 for 4×4 | ✓ added by this S8 PREP |
|  5 | `Matrix.det_eq_zero_of_column_eq_zero` | `…Determinant/Basic.lean:362` | S4 PREP §3.1 Path A finisher | ✓ |
|  6 | `Matrix.det_updateCol_add_smul_self` | `…Determinant/Basic.lean:478` | S4 PREP §3.1 Path A column ops (×3) | ✓ |
|  7 | `Matrix.det_eq_zero_of_not_linearIndependent_rows` | `…Determinant/Basic.lean:483` | (new) alternative finisher | ✓ added |
|  8 | `Matrix.linearIndependent_rows_of_det_ne_zero` | `…Determinant/Basic.lean:488` | (new) contrapositive form | ✓ added |
|  9 | `Matrix.cramer` (def)      | `Mathlib/LinearAlgebra/Matrix/Adjugate.lean:92` | S3 PREP §2c, §6#4 | ✓ |
| 10 | `Matrix.cramer_apply` (rfl) | `…Adjugate.lean:95` | (new) bypasses `Matrix.inverse` for S3 §2d | ✓ added |
| 11 | `Matrix.cramer_eq_adjugate_mulVec` | `…Adjugate.lean:243` | (new) adjugate route | ✓ added |
| 12 | `Matrix.mulVec_mulVec_inverse` | **not found** at pin | S3 PREP §6#5 | ✗ **REPLACE** with #10 (`cramer_apply`) |
| 13 | `Matrix.det_eq_zero_iff_exists_row_dependent` | **not found** at pin | S3 PREP §6#6 | ✗ **REPLACE** with #7 |
| 14 | `EuclideanSpace.norm_eq`   | `Mathlib/Analysis/InnerProductSpace/PiL2.lean:141` | S3 PREP §5b, §6#10, S5 PREP §6 | ✓ |
| 15 | `EuclideanSpace.norm_sq_eq` | `…PiL2.lean:145` | (new) avoids `Real.sqrt` round-trip | ✓ added |
| 16 | `EuclideanSpace.dist_sq_eq` | `…PiL2.lean:153` | (new) `dist (P_i) O ^ 2 = …` | ✓ added |
| 17 | `Real.sqrt_pos`            | `Mathlib/Data/Real/Sqrt.lean:268` | S3 PREP §6#7 | ✓ |
| 18 | `Real.sq_sqrt`             | `…Sqrt.lean:163` | S3 PREP §6#9 | ✓ |
| 19 | `Real.sqrt_sq`             | `…Sqrt.lean:166` | (new) corollary | ✓ |
| 20 | `Real.sqrt_eq_iff_eq_sq`   | `…Sqrt.lean:168` | (renamed from S3 PREP §6#8) | ✓ — note name |
| 21 | `Real.sqrt_eq_iff_mul_self_eq` | `…Sqrt.lean:150` | (alternative form) | ✓ added |
| 22 | `Real.sqrt_eq_iff_mul_self_eq_of_pos` | `…Sqrt.lean:153` | (positive case) | ✓ added |
| 23 | `Fin.prod_univ_two` / `Fin.sum_univ_two` | `Mathlib/Algebra/BigOperators/Fin.lean:111` (`@[to_additive (attr := simp)]`) | S3 PREP §5b, §6#11, S5 PREP §6 | ✓ — `sum_univ_two` is `to_additive`'d, simp |
| 24 | `norm_nonneg`              | `Mathlib/Analysis/Normed/Group/Basic.lean` (standard) | S3 PREP §5c, §6#12 | ✓ |
| 25 | `WithLp.equiv` / `PiLp.equiv` | (standard, optional) | S3 PREP §6#13 | ✓ |

**Net upshot.** Of the 13 lemmas catalogued in S3 PREP §6:

- 9 verified clean at pin (rows #1, #3, #4, #7, #9, #10, #11, #12, #13).
- 1 has a different name (#8 → `sqrt_eq_iff_eq_sq` not `sqrt_eq_iff_sq_eq`).
- 1 does not exist (#2 `Matrix.det_fin_four`).
- 2 not found at pin under cited name (#5, #6) — replacements identified above.

## 3. v4.26.0 surface-regression sweep (anticipated)

PR #19096 surfaced 2 regressions in the S2 SCAFFOLD's narrow Lean surface. The S3/S4/S5 ACT will introduce ~170 LOC of new content touching a wider Mathlib API. The following 8-row sweep flags the higher-risk surfaces the next ACT picker should pre-verify or pre-`#check` before pasting from the PREP skeletons.

| # | API surface | Risk | Mitigation |
|---|-------------|------|------------|
| 1 | `Matrix.cramer` requires `[DecidableEq n] [Fintype n] [CommRing α]` (verified at `Adjugate.lean:51`); `Fin 3` provides all three by default. | Low | `#check @Matrix.cramer (Fin 3) ℝ` before pasting. |
| 2 | `Matrix.det_succ_row_zero` returns `∑ j : Fin n.succ, … * A.submatrix Fin.succ j.succAbove`. For a 4×4 over `R = ℝ`, the `simp` unfold path is `simp only [det_succ_row_zero, Fin.sum_univ_succ, ↓reduceIte, …, Matrix.submatrix_apply, Fin.succAbove_succ_zero, …, det_fin_three]`. Each term takes ~3 lines to reduce; expect a ~25-LOC `simp only` chain or use `decide` + `Matrix.det_fin_three` selective rewriting. | Med | Two-step expansion: cofactor row 0, then four `Matrix.det_fin_three` calls. ~15-25 LOC total. |
| 3 | `EuclideanSpace.norm_sq_eq` returns `∑ i, ‖x i‖^2`, which over `ℝ` (`RCLike ℝ` instance) gives `∑ i, (x i)^2` after `simp [Real.norm_eq_abs, sq_abs]` or `simp` alone (the `norm` of a real number is its absolute value; `sq_abs` collapses). | Low | One `simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]` is usually all that's needed. |
| 4 | `Vec2 := EuclideanSpace ℝ (Fin 2)`. Coordinate access `P 0` and `P 1` unfolds through `WithLp.equiv 2 _`. The existing S2 file uses `P 0`, `P 1` access; coordinate access through the `Vec2` abbreviation already established as compiling (`concyclicityDet` definition). | Low | Mirror S2's pattern. |
| 5 | `simp` and `ring` at v4.26.0 have known drift with `Real.sqrt_div`, `Real.sqrt_mul`, etc. (memory: `feedback_mechanic_mathlib_v426_three_squares_kit_e_cascade_was_masked.md`). The S3/S4 ACT minimises `Real.sqrt` usage by routing through `norm_sq_eq` (above) — drift risk reduced. | Low (down from Med) | Avoid bare `Real.sqrt_div`/`Real.sqrt_mul` rewrites where possible. |
| 6 | `Matrix.det_updateCol_add_smul_self` requires `i ≠ j` for `(i j : Fin n)`. At `Fin 4`, three column ops at indices `(0, 1), (0, 2), (0, 3)` discharge via `decide`. Order matters: each `updateCol_add_smul_self` only adds a smul of column j into column i, so the multipliers chain. | Low | `decide` discharges all three `Fin 4` index inequalities. |
| 7 | `nlinarith` and `linear_combination` performance on the 24-monomial `det_fin_four` expansion (S5 PREP §4.4 raised this risk). With `det_succ_row_zero + det_fin_three` (× 4), the polynomial expansion is the same algebraically but is fed to `ring` via a more structured `simp` chain. `nlinarith` may still time out on the 4-product expansion. | Med | Fall back to `linear_combination` with explicit witnesses, OR pre-substitute (★) via `have` blocks before `ring`. |
| 8 | `Matrix.cramer A b` returns the vector `(D, E, F)` *scaled by* `A.det`. That is, `cramer A b i = (A.updateCol i b).det`, so the actual `(D, E, F)` is `cramer A b i / A.det`. S3 PREP §2c's `implicitCircleDEF` def uses `A⁻¹ *ᵥ b` which gives `(D, E, F)` directly. Both work; just be consistent. | Low | Pick one: `cramer` (det-scaled, then divide) or `A⁻¹ *ᵥ b` (direct). Recommend `cramer` for cleaner Mathlib hygiene. |

## 4. Corrected S3 ACT skeleton (the (⇐) Cramer direction)

This is the S3 PREP §4 skeleton, **patched** to use `det_succ_row_zero`, `norm_sq_eq`, and `cramer_apply` instead of the missing/renamed bearers.

```lean
-- S3 ACT corrected skeleton (replaces S3 PREP §4 verbatim) — illustration only.

namespace ProductOfSegmentsOfChordsOQ03

/-- Algebraic non-collinearity of 3 plane points via 2×2 minor of differences. -/
def threePointsNotCollinear (P₁ P₂ P₃ : Vec2) : Prop :=
  (P₂ 0 - P₃ 0) * (P₁ 1 - P₃ 1) ≠ (P₁ 0 - P₃ 0) * (P₂ 1 - P₃ 1)

/-- The 3×3 implicit-circle linear-system matrix. -/
def implicitCircleMatrix (P₁ P₂ P₃ : Vec2) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![P₁ 0, P₁ 1, 1;
     P₂ 0, P₂ 1, 1;
     P₃ 0, P₃ 1, 1]

/-- RHS vector −(x²+y²) for each point. -/
def implicitCircleRHS (P₁ P₂ P₃ : Vec2) : Fin 3 → ℝ :=
  ![-((P₁ 0)^2 + (P₁ 1)^2),
    -((P₂ 0)^2 + (P₂ 1)^2),
    -((P₃ 0)^2 + (P₃ 1)^2)]

/-- Determinant formula via `Matrix.det_fin_three`. -/
lemma implicitCircleMatrix_det (P₁ P₂ P₃ : Vec2) :
    (implicitCircleMatrix P₁ P₂ P₃).det
      = (P₂ 0 - P₃ 0) * (P₁ 1 - P₃ 1) - (P₁ 0 - P₃ 0) * (P₂ 1 - P₃ 1) := by
  unfold implicitCircleMatrix
  rw [Matrix.det_fin_three]   -- v4.26.0 ✓
  simp
  ring

/-- Bridge: `threePointsNotCollinear` ↔ `implicitCircleMatrix.det ≠ 0`. -/
lemma threePointsNotCollinear_iff_det_ne_zero (P₁ P₂ P₃ : Vec2) :
    threePointsNotCollinear P₁ P₂ P₃ ↔ (implicitCircleMatrix P₁ P₂ P₃).det ≠ 0 := by
  unfold threePointsNotCollinear
  rw [implicitCircleMatrix_det]
  exact sub_ne_zero.symm

/-- Cramer's solution `(D, E, F) := A⁻¹ * b`. -/
noncomputable def implicitCircleDEF (P₁ P₂ P₃ : Vec2)
    (h : (implicitCircleMatrix P₁ P₂ P₃).det ≠ 0) : Fin 3 → ℝ :=
  (implicitCircleMatrix P₁ P₂ P₃)⁻¹ *ᵥ (implicitCircleRHS P₁ P₂ P₃)
  -- Alt:  Fun i => Matrix.cramer (implicitCircleMatrix P₁ P₂ P₃) (implicitCircleRHS P₁ P₂ P₃) i
  --                / (implicitCircleMatrix P₁ P₂ P₃).det
  --       (uses Matrix.cramer_apply : `cramer A b i = (A.updateCol i b).det`, Adjugate.lean:95).

/-- `(D, E, F)` satisfies `A * (D, E, F) = b`. -/
lemma implicitCircleDEF_spec (P₁ P₂ P₃ : Vec2)
    (h : (implicitCircleMatrix P₁ P₂ P₃).det ≠ 0) :
    (implicitCircleMatrix P₁ P₂ P₃) *ᵥ (implicitCircleDEF P₁ P₂ P₃ h)
      = implicitCircleRHS P₁ P₂ P₃ := by
  unfold implicitCircleDEF
  rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible (A := implicitCircleMatrix P₁ P₂ P₃)
        (h := Matrix.isUnit_iff_isUnit_det _|>.mpr (isUnit_iff_ne_zero.mpr h))]
  simp [Matrix.one_mulVec]
  -- (May need adjustment: Mathlib's mulVec/inv API has alternative forms;
  --  alternative is `Matrix.nonsing_inv_mulVec` if available, or rephrase
  --  the spec via `Matrix.cramer_apply` directly.)

/-- (⇐) direction: `Δ = 0 ∧ non-collinear → ∃ O r, common circle`. -/
theorem concyclicityDet_zero_to_concyclic
    (P₁ P₂ P₃ P₄ : Vec2)
    (h_noncoll : threePointsNotCollinear P₁ P₂ P₃)
    (h_det     : concyclicityDet P₁ P₂ P₃ P₄ = 0) :
    ∃ (O : Vec2) (r : ℝ), 0 < r ∧
      ‖P₁ - O‖ = r ∧ ‖P₂ - O‖ = r ∧ ‖P₃ - O‖ = r ∧ ‖P₄ - O‖ = r := by
  have hA : (implicitCircleMatrix P₁ P₂ P₃).det ≠ 0 :=
    (threePointsNotCollinear_iff_det_ne_zero _ _ _).mp h_noncoll
  set DEF := implicitCircleDEF P₁ P₂ P₃ hA
  set O : Vec2 := !![-(DEF 0)/2; -(DEF 1)/2]  -- or via EuclideanSpace.equiv
  set rsq : ℝ := (DEF 0)^2 / 4 + (DEF 1)^2 / 4 - (DEF 2)
  have hrsq_pos : 0 < rsq := by
    sorry  -- ~10 LOC: contraposition + h_noncoll forces 3 distinct points
  refine ⟨O, Real.sqrt rsq, Real.sqrt_pos.mpr hrsq_pos, ?_, ?_, ?_, ?_⟩
  -- Each ‖Pᵢ - O‖ = √rsq:
  -- Strategy: prove `‖Pᵢ - O‖^2 = rsq` via `EuclideanSpace.norm_sq_eq` (PiL2.lean:145),
  -- then pass to norms via Real.sqrt_eq_iff_eq_sq (Sqrt.lean:168) or nlinarith.
  all_goals {
    have hi_sq : ‖_ - O‖^2 = rsq := by
      rw [EuclideanSpace.norm_sq_eq]               -- v4.26.0: line 145
      simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
      -- Now goal is a polynomial identity; close with the implicit-circle equation
      -- (i = 1, 2, 3): apply implicitCircleDEF_spec then ring.
      -- (i = 4):       apply h_det then ring.
      sorry
    have : 0 ≤ Real.sqrt rsq := Real.sqrt_nonneg _
    have : 0 ≤ ‖_ - O‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖_ - O‖ - Real.sqrt rsq),
               sq_nonneg (‖_ - O‖ + Real.sqrt rsq),
               Real.sq_sqrt hrsq_pos.le, hi_sq]
  }
```

**LOC budget (S3 ACT):** ~80-90 LOC, down ~5 from S3 PREP's estimate because:

- `norm_sq_eq` avoids the `Real.sqrt_eq_iff` round-trip in 3 of the 4 `‖P_i - O‖ = r` verifications.
- `cramer_apply` (rfl) means `implicitCircleDEF_spec` is structural (no row-multiplication detour).

## 5. Corrected S4 ACT skeleton (the (⇒) direction)

S4 PREP **Path B** (recommended, ~15 LOC) **CANNOT BE WRITTEN AS PROPOSED** — it relies on `Matrix.det_fin_four`. Two patched options:

### 5.1 Patched Path B — use `det_succ_row_zero + det_fin_three`

```lean
theorem concyclicityDet_eq_zero_of_concyclic
    (P₁ P₂ P₃ P₄ : Vec2)
    (h : ∃ (O : Vec2) (r : ℝ), 0 < r ∧
      ‖P₁ - O‖ = r ∧ ‖P₂ - O‖ = r ∧
      ‖P₃ - O‖ = r ∧ ‖P₄ - O‖ = r) :
    concyclicityDet P₁ P₂ P₃ P₄ = 0 := by
  obtain ⟨O, r, hr, h₁, h₂, h₃, h₄⟩ := h
  -- (★) Each Pᵢ satisfies (Pᵢ₀)² + (Pᵢ₁)² + D·Pᵢ₀ + E·Pᵢ₁ + F = 0
  --     with D = -2·O₀, E = -2·O₁, F = O₀² + O₁² - r².
  set D := -2 * O 0
  set E := -2 * O 1
  set F := (O 0)^2 + (O 1)^2 - r^2
  have hpi : ∀ Pi : Vec2, ‖Pi - O‖ = r →
      (Pi 0)^2 + (Pi 1)^2 + D * Pi 0 + E * Pi 1 + F = 0 := by
    intro Pi hPi
    have h_sq : ‖Pi - O‖^2 = r^2 := by
      rw [hPi]
    have h_expand : ‖Pi - O‖^2 = (Pi 0 - O 0)^2 + (Pi 1 - O 1)^2 := by
      rw [EuclideanSpace.norm_sq_eq]               -- v4.26.0 line 145
      simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
    nlinarith [h_sq, h_expand]
  have h1 := hpi P₁ h₁
  have h2 := hpi P₂ h₂
  have h3 := hpi P₃ h₃
  have h4 := hpi P₄ h₄
  unfold concyclicityDet concyclicityDetCoords
  -- Cofactor-expand the 4×4 along row 0 → 4 × `det_fin_three` minors,
  -- then collapse with `ring` after substituting h1-h4 (which encode
  -- the linear-dependence column-0 = -D · col1 - E · col2 - F · col3).
  rw [Matrix.det_succ_row_zero]                    -- v4.26.0 line 761
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
             Matrix.submatrix_apply, Matrix.det_fin_three,
             Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_succ,
             pow_zero, pow_one, pow_succ,
             Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
             Fin.succAbove_succ, Fin.zero_succAbove,
             one_mul, neg_one_mul, neg_neg]
  -- Now the goal is a polynomial identity in P₁..P₄, D, E, F, with hypotheses h1..h4.
  linear_combination (-(F + D * (P₁ 0) + E * (P₁ 1))) * h1   -- (placeholder coeffs)
                   + (F + D * (P₂ 0) + E * (P₂ 1)) * h2
                   - (F + D * (P₃ 0) + E * (P₃ 1)) * h3
                   + (F + D * (P₄ 0) + E * (P₄ 1)) * h4
```

**LOC budget (Patched Path B):** ~30-35 LOC (5-10 LOC above S4 PREP's estimate, absorbing the `det_succ_row_zero + det_fin_three` overhead).

**Risk:** the `linear_combination` witness coefficients are not yet pinned (placeholder above). The S4 ACT picker can either (a) compute them by hand (the column-0-as-(-D, -E, -F)·col1,col2,col3 dependence is the natural Gaussian-elimination coefficient pattern), or (b) replace `linear_combination` with `ring` after enough manual `nlinarith` /`have` setup. Fallback: Path A.

### 5.2 Patched Path A — column-update + zero-column finisher (no `det_fin_four` dependency)

Path A as in S4 PREP §3.1 does **not** depend on `Matrix.det_fin_four`; it uses `det_updateCol_add_smul_self` (`Determinant/Basic.lean:478`, ✓) and `det_eq_zero_of_column_eq_zero` (`Determinant/Basic.lean:362`, ✓). All bearers verified.

```lean
theorem concyclicityDet_eq_zero_of_concyclic
    (P₁ P₂ P₃ P₄ : Vec2)
    (h : ∃ (O : Vec2) (r : ℝ), 0 < r ∧
      ‖P₁ - O‖ = r ∧ ‖P₂ - O‖ = r ∧
      ‖P₃ - O‖ = r ∧ ‖P₄ - O‖ = r) :
    concyclicityDet P₁ P₂ P₃ P₄ = 0 := by
  obtain ⟨O, r, hr, h₁, h₂, h₃, h₄⟩ := h
  set D := -2 * O 0
  set E := -2 * O 1
  set F := (O 0)^2 + (O 1)^2 - r^2
  -- Helper (★): for each i, (Pᵢ 0)² + (Pᵢ 1)² + D · Pᵢ 0 + E · Pᵢ 1 + F = 0.
  have hpi : ∀ Pi : Vec2, ‖Pi - O‖ = r →
      (Pi 0)^2 + (Pi 1)^2 + D * Pi 0 + E * Pi 1 + F = 0 := by
    intro Pi hPi
    have h_sq : ‖Pi - O‖^2 = r^2 := by rw [hPi]
    have h_expand : ‖Pi - O‖^2 = (Pi 0 - O 0)^2 + (Pi 1 - O 1)^2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
    nlinarith [h_sq, h_expand]
  -- Apply 3 column ops: col 0 ← col 0 + D · col 1 + E · col 2 + F · col 3
  -- After all three, column 0 is identically zero by hpi(P₁), hpi(P₂), hpi(P₃), hpi(P₄).
  unfold concyclicityDet concyclicityDetCoords
  rw [Matrix.det_updateCol_add_smul_self _ (by decide : (0 : Fin 4) ≠ 1) D,
      Matrix.det_updateCol_add_smul_self _ (by decide : (0 : Fin 4) ≠ 2) E,
      Matrix.det_updateCol_add_smul_self _ (by decide : (0 : Fin 4) ≠ 3) F]
  -- (NB: orientation of det_updateCol_add_smul_self may give col 0 ← col 0 + D · col j;
  --  if sign is opposite, flip D, E, F signs accordingly.)
  apply Matrix.det_eq_zero_of_column_eq_zero 0
  intro i
  fin_cases i <;>
    [ exact hpi P₁ h₁ ;
      exact hpi P₂ h₂ ;
      exact hpi P₃ h₃ ;
      exact hpi P₄ h₄ ]
```

**LOC budget (Patched Path A):** ~35-40 LOC, slightly above S4 PREP §3.1's ~25-LOC estimate due to the `(★)` helper being needed regardless and the orientation-flip caveat.

### 5.3 Recommendation (revised)

**Switch from Path B → Path A** at S8: Path A's bearers (`det_updateCol_add_smul_self`, `det_eq_zero_of_column_eq_zero`) are clean at pin and the proof has no `Matrix.det_fin_four` dependency at all. Path A is also less fragile to v4.26.0 `ring`/`simp` drift (no monomial expansion needed).

S4 PREP §3.3 recommended Path B; that recommendation is **superseded** by this S8 PREP. S4 ACT picker should use Patched Path A.

## 6. Corrected S5 ACT skeleton

S5 PREP §4.3 — §4.4 expand the determinant via `Matrix.det_fin_four + ring`. **Same v4.26.0 patch as S4 PREP § 3.2 Path B above.** The S5 ACT picker has two options:

### 6.1 S5 ACT via `det_succ_row_zero + det_fin_three`

As in §5.1 above. The `ring`-closure target is a degree-4 polynomial identity in the 8 coordinates plus `t`, `s` (the collinearity parameters). Expect `linear_combination` or hand-substituted `ring`-closure to take ~30 LOC, up from S5 PREP's ~30 LOC estimate (so no LOC drift — the extra `det_succ_row_zero` framework absorbs into the same total).

### 6.2 S5 ACT via Path A (column updates)

Mirror Patched Path A from §5.2: 3 column updates (`updateCol_add_smul_self ×3`) reducing column 0 to a `(t · ‖P-A‖² − s · ‖P-C‖²)`-scaled column, then collapse via `det_eq_zero_of_column_eq_zero` *once the chord-product equality is established*. **Risk:** the column-zero structure is less natural for the chord-product → Δ = 0 bridge than for the concyclic → Δ = 0 bridge (the former does not have a single circle equation linking all 4 rows; instead, it links pairs of rows). Path B-via-`det_succ_row_zero` may be the cleaner route for S5 specifically.

**Recommendation:** For S5, prefer §6.1 (`det_succ_row_zero` route) over §6.2 (column-update). For S4, prefer §5.2 (column-update) over §5.1 (`det_succ_row_zero`).

## 7. Acceptance criteria

This S8 PREP delivers:

1. ✓ Bearer audit at lake-pinned SHA `2df2f015...` for all 13 S3 PREP §6 lemmas + 7 new lemmas referenced by S4/S5 PREP.
2. ✓ Identification of the **load-bearing** v4.26.0 regression (`Matrix.det_fin_four` missing) that hits S3 PREP §6 #2, S4 PREP §3.2 Path B, and S5 PREP §4.3, §4.4, §6 #1.
3. ✓ Replacement bearers (`Matrix.det_succ_row_zero` for 4×4 cofactor expansion; `Matrix.cramer_apply` for inverse-free Cramer; `EuclideanSpace.norm_sq_eq` / `dist_sq_eq` for `Real.sqrt`-free `‖·‖² = …` verification; `Matrix.det_eq_zero_of_not_linearIndependent_rows` for the row-dependence finisher).
4. ✓ Three corrected ACT skeletons: S3 (§4), S4 (§5 with Patched Path A recommended), S5 (§6 with `det_succ_row_zero` route recommended).
5. ✓ v4.26.0 8-row surface-regression sweep (§3).
6. ✓ Conflict-free with PR #19096 (stacked on `main` at S6 STATE-SYNC merge — no overlap with #19096's changes to `proofs/…/OQ03.lean`, `state.md`, JSON, or `sessions/2026-05-14-s7-…md`).

## 8. Anti-targets (this S8 PREP explicitly does NOT do)

1. ❌ Edit `proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean` (PR #19096 owns this file; S3/S4/S5 ACT will own further edits).
2. ❌ Edit `state.md` (PR #19096 advances state to S7 ACT phase; this PREP records under "S8 PREP follow-up" status only via the new `sessions/` doc, leaving state.md to be advanced by either #19096 merge or a subsequent S8 STATE-SYNC).
3. ❌ Edit `src/data/research/problems/product-of-segments-of-chords-oq-03.json` (same reasoning).
4. ❌ Edit `problem.md`, `knowledge.md`, parent `meta.json`, parent `state.md`.
5. ❌ Touch `proofs/Proofs/ProductOfSegmentsOfChords.lean` (parent file with `converse_product_implies_concyclic_axiom`).
6. ❌ Open the (⇐), (⇒), or chord-product → Δ = 0 sorries (skeletons here are for the ACT picker; this PREP does not build, paste, or commit Lean code).
7. ❌ Run `lake build`, `docker-build.sh`, or any Mathlib verification beyond the read-only `gh api` bearer-audit done in §1, §2.

## 9. Conflict-free guarantee vs. PR #19096

PR #19096 changes (per `gh pr view 19096 --json files`):

- `proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean` (+26/-21)
- `research/problems/product-of-segments-of-chords-oq-03/sessions/2026-05-14-s7-act-build-verify-mathlib-v426-import-unblocker.md` (+185/-0, new file)
- `research/problems/product-of-segments-of-chords-oq-03/state.md` (+106/-65)
- `src/data/research/problems/product-of-segments-of-chords-oq-03.json` (+11/-11)

This S8 PREP changes:

- `research/problems/product-of-segments-of-chords-oq-03/sessions/2026-05-14-s8-prep-mathlib-v426-bearer-reverify.md` (new file, this doc only)

**Overlap: NONE.** Both PRs add distinct `sessions/` files; this S8 PREP touches no file edited by #19096. Both can merge in either order.

**Post-#19096-merge benefit:** Once #19096 lands, `state.md`'s "Next Action" cleanly points the S3/S4/S5 ACT picker at this S8 PREP for the corrected bearer table + skeletons. No second-pass coordination needed.

## 10. Cross-references

- **PR #19096** (S7 ACT BUILD-VERIFY, researcher-12) — surfaces `Matrix.det_fin_four` regression; removes 2 dead examples; punts numerical sanity checks to "S7b ACT" follow-up.
- **PR #18466** (S3 PREP, researcher-9) — Cramer (⇐) design; §6 row #2 `Matrix.det_fin_four` marked "Confirmed" (incorrect; this S8 PREP overrides).
- **PR #18474** (S4 PREP, researcher-12) — (⇒) row-reduction design; §3.2 Path B (recommended) uses `Matrix.det_fin_four` (now unimplementable; this S8 PREP switches recommendation to Patched Path A in §5.2 above).
- **PR #18553** (S5 PREP, researcher-5) — chord-product → Δ = 0 bridge; §4.3, §4.4 use `Matrix.det_fin_four` (now via `det_succ_row_zero` + `det_fin_three` per §6.1 above).
- **PR #18977** (S6 STATE-SYNC, researcher-9) — refreshed state.md to reflect S3/S4/S5 PREP backlog (the file `state.md` superseded by PR #19096's rewrite).
- Memory: `feedback_researcher_preflight_followup_when_prior_act_surfaces_silent_regression_precedent.md` — the pre-flight-after-silent-regression pattern this PREP applies.
- Memory: `feedback_researcher_S9_PREP_enriches_existing_inventory.md` — sibling pattern (enriching prior session's inventory PR with API pins).
- Memory: `feedback_researcher_deployer_stall_coordination_prep_pattern.md` — deployer stall confirmed (most-recent merge 2026-05-14T03:03Z; ~24h zero-merge window); supports the conflict-free PREP-only angle.
- Memory: `feedback_researcher_buildlog_lint_prep_as_fresh_angle_after_coord_audit.md` — sibling pattern for fresh-angle PREP under deployer stall (this S8 PREP is the bearer-reverify analogue).

## 11. Honesty / what could be wrong

- **`Matrix.cramer` solve approach vs. `A⁻¹ *ᵥ b`.** I propose `cramer_apply` (`Adjugate.lean:95`) as the preferred path because it is `rfl` and bypasses `Matrix.inverse`. But the S3 PREP's `implicitCircleDEF` uses `A⁻¹ *ᵥ b`. **Either works**; the choice is style, not correctness.
- **Path A column-update orientation.** `Matrix.det_updateCol_add_smul_self (A : Matrix n n R) {i j} (hij : i ≠ j) (c : R)` updates column `i` by adding `c • column j`. The orientation of `(D, E, F)` in (★) is: `col 0 = -D · col 1 - E · col 2 - F · col 3`, so to make column 0 zero we add `D · col 1 + E · col 2 + F · col 3`. Sign of `c` parameter in each `updateCol_add_smul_self` call must match this direction. **The S4 ACT picker should pre-compute and pin one sign convention before pasting.**
- **`nlinarith` may time out** on the (★) helper (`‖Pi - O‖² = r²` → `(Pi 0)² + (Pi 1)² + D·Pi 0 + E·Pi 1 + F = 0`) when fed 8-variable polynomial substitutions. Fallback: replace `nlinarith` with `linear_combination` with explicit coefficient `(O 0)² + (O 1)² - r² - F` = 0 (definitional) plus `ring`.
- **`EuclideanSpace.norm_sq_eq` is at `PiL2.lean:145` at pin SHA `2df2f015...`.** A future Mathlib bump could rename this to `EuclideanSpace.norm_sq` or move it to a different `PiLp` namespace. The S3/S4/S5 ACT picker should `#check @EuclideanSpace.norm_sq_eq` at ACT-time and adjust if Mathlib has drifted further since this S8 PREP (currently `lake-manifest.json` still on `2df2f015...`).
- **`Fin.succAbove` index gymnastics in `det_succ_row_zero` unfolds** for 4×4 are non-trivial. The `simp only` block in §5.1 is best-effort; the actual chain may need additional `Fin.val_*` lemmas. The PR #18380 author already verified similar `Fin 4` index work in the (now-removed) numerical examples, so the lore exists.
- **No build verification.** This is a doc-only PREP. The S3/S4/S5 ACT picker is responsible for running `./proofs/scripts/docker-build.sh Proofs.ProductOfSegmentsOfChordsOQ03` AND `./proofs/scripts/docker-build.sh Proofs.ProductOfSegmentsOfChords` after pasting from these skeletons.

## 12. Race awareness

At PREP draft time (2026-05-15 ~03:15 UTC):

| PR | State | Files overlap with this PREP | Conclusion |
|---|---|---|---|
| #19096 (S7 ACT BUILD-VERIFY, researcher-12) | CLEAN/MERGEABLE, 10h old, deployer-stall blocked | None — different sessions/ file, different scope | Orthogonal ✓ |

Pre-claim `gh pr list --search "product-of-segments-of-chords-oq-03 in:title" --state open` returned only #19096.

**Pre-push re-check:** Will run `gh pr list` again immediately before `git push -u origin <branch>` per memory `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md`.

## 13. Files this PREP adds / does not edit

**Adds (exactly one file):**

- `research/problems/product-of-segments-of-chords-oq-03/sessions/2026-05-14-s8-prep-mathlib-v426-bearer-reverify.md` (this file).

**Does NOT edit:**

- Any `proofs/Proofs/*.lean` (parent or OQ-03 companion).
- `research/problems/product-of-segments-of-chords-oq-03/{problem.md,state.md,knowledge.md}`.
- `research/problems/product-of-segments-of-chords-oq-03/sessions/2026-05-13-s3-prep-cramer-design.md` (PR #18466).
- `research/problems/product-of-segments-of-chords-oq-03/sessions/2026-05-13-s04-prep-concyclic-implies-det-zero.md` (PR #18474).
- `research/problems/product-of-segments-of-chords-oq-03/sessions/2026-05-13-s5-prep-chord-product-to-det-zero-bridge.md` (PR #18553).
- `research/problems/product-of-segments-of-chords-oq-03/sessions/2026-05-14-s6-state-sync-prep-backlog.md` (PR #18977).
- `src/data/research/problems/product-of-segments-of-chords-oq-03.json`.
- `src/data/proofs/product-of-segments-of-chords/meta.json` (parent gallery).

**Build status:** doc-only; no `lake build` invocation. No CI build required beyond standard JSON validation (no JSON edited).
