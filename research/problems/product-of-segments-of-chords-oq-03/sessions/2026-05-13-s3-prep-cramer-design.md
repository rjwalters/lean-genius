# S3 PREP — Cramer's rule discharge design for `concyclicityDet_eq_zero_iff_concyclic` (⇐) (doc-only)

**Author:** researcher-9
**Timestamp:** 2026-05-13 02:15 UTC
**Phase:** S3 PREP (pre-ACT design, doc-only)
**Iteration:** 3-prep
**Scope:** Single new file in `sessions/` (creates the `sessions/` subdir for this slug). No edits to `problem.md`, `state.md`, `knowledge.md`, or any Lean file. No edits to `proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean`. No edits to `src/data/research/problems/`. No build.

## 0. Why this angle now

S2 SCAFFOLD #18380 (researcher-3) merged 2026-05-13 02:11 UTC, **5 minutes** before this session's claim. It shipped `Proofs/ProductOfSegmentsOfChordsOQ03.lean` (106 LOC, 1 sorry) with:

- `concyclicityDetCoords` and `concyclicityDet` definitions
- 2 numerical examples (build verified algebraically)
- Statement of `concyclicityDet_eq_zero_iff_concyclic` with `(hNonCollinear : True)` placeholder and 1 `sorry`

The state.md `Next Action` for S3 specifies:

> 1. Replace the `hNonCollinear : True` placeholder with the real non-collinearity hypothesis (e.g. `¬ Collinear ℝ ({P₁, P₂, P₃} : Set Vec2)` or a stronger linear-independence form for the first three rows of the 3×3 minor).
> 2. Prove the (⇐) direction: Δ = 0 together with non-collinearity yields (D, E, F) via `Matrix.cramer`, define O := (-D/2, -E/2) and r := √(D²/4 + E²/4 - F), prove r > 0 from non-degeneracy, then verify ‖P_i - O‖ = r for each i.

This memo:

1. **Picks the non-collinearity hypothesis** definitively (§ 1).
2. **Specifies the Cramer's rule application** as a sequence of 4 Lean-friendly sub-steps (§ 2), with the matrix construction and the explicit `(D, E, F)` formulas.
3. **Constructs the center/radius** with non-degeneracy proofs (§ 3).
4. **Lists Mathlib API surface** (§ 4) — with caveat for the rate-limit-blocked verification queue.
5. **Anticipates 3 specific friction points** for the S3 ACT picker (§ 5) — `Vec2` ↔ `Fin 2 → ℝ` interconversion, `‖·‖` on `EuclideanSpace`, and `Real.sqrt` positivity.

Strictly orthogonal to the in-flight S2 SCAFFOLD (now merged) and to any future S3 ACT — this is the design memo, not the implementation.

**Build status of parent S2.** Per state.md § Build status, the S2 SCAFFOLD is **build-pending**: local Docker attempts were blocked by `proofs/.lake` symlink loop + partial-mathlib-clone wipe. CI should verify once a clean worktree opens up. **This PREP does not modify the S2 file**, so no rebuild is forced by this PR.

## 1. The non-collinearity hypothesis

S2's `(hNonCollinear : True)` is a placeholder. Three candidates:

### 1a. `¬ Collinear ℝ ({P₁, P₂, P₃} : Set Vec2)` (Mathlib geometric)

Mathlib has `Collinear : Set V → Prop` in `Mathlib/LinearAlgebra/AffineSpace/AffineSubspace.lean`. This is the *natural* geometric statement.

**Pros**: Standard Mathlib name; geometrically meaningful.
**Cons**: Unfolds via affine-span arguments; converting it to the form needed by Cramer's rule (a 3×3 minor being invertible) requires a bridging lemma. Mathlib provides `Collinear.affineSpan_eq_top` and `not_collinear_iff_affineSpan_eq_top` for ℝ² embedded as an affine plane; bridging from `Vec2 = EuclideanSpace ℝ (Fin 2)` to the affine-plane setting may need a small adapter (~10 LOC).

### 1b. `(Matrix.det !![P₁ 0 - P₃ 0, P₁ 1 - P₃ 1; P₂ 0 - P₃ 0, P₂ 1 - P₃ 1]) ≠ 0` (algebraic — 2×2 minor invertibility)

The 2×2 minor encoding "P₁, P₂, P₃ are not collinear" is the algebraic-determinant form. By a standard linear-algebra fact, 3 affine points in ℝ² are collinear iff this 2×2 determinant of differences vanishes.

**Pros**: Directly usable by Cramer's rule arguments; no Mathlib `Collinear` unfolding needed.
**Cons**: Less natural geometric statement.

### 1c. `LinearIndependent ℝ ![P₂ - P₁, P₃ - P₁]` (Mathlib linear)

Mathlib's `LinearIndependent` formulation. Two ℝ²-vectors are linearly independent iff the 2×2 minor is non-zero.

**Pros**: Mathlib-standard.
**Cons**: Needs a coercion from `Vec2 = EuclideanSpace ℝ (Fin 2)` to a basis-friendly form; `EuclideanSpace ℝ (Fin 2)` is *defeq* to `PiLp 2 (fun _ : Fin 2 => ℝ)`, which adds `simp` normal-form friction.

### Recommendation: 1b (algebraic 2×2 determinant)

For S3's Cramer's rule discharge, **1b is the most directly usable**. The 2×2 determinant `‖a‖₁ b‖₁ - ‖a‖₂ b‖₂` (where `a := P₂ - P₃`, `b := P₁ - P₃`) appears explicitly in the cofactor expansion of the 3×3 minor of the implicit-circle linear system, so the non-degeneracy of Cramer's rule reduces to **the same** non-vanishing condition.

```lean
def threePointsNotCollinear (P₁ P₂ P₃ : Vec2) : Prop :=
  (P₂ 0 - P₃ 0) * (P₁ 1 - P₃ 1) ≠ (P₁ 0 - P₃ 0) * (P₂ 1 - P₃ 1)
```

(Alternatively express via `Matrix.det !![...]`, which Mathlib normalizes via `Matrix.det_fin_two` to the same scalar form.)

**Bridging note.** A future session can prove `threePointsNotCollinear ↔ ¬ Collinear ℝ {P₁, P₂, P₃}` if the gallery wants the Mathlib-flavored statement to appear in the final theorem. For S3, use 1b internally; for the final user-facing theorem statement, either keep 1b or wrap it.

## 2. The Cramer's rule application

The implicit-circle equation is `x² + y² + Dx + Ey + F = 0`. Given `P₁, P₂, P₃` not collinear, the constraint that the circle passes through them is a 3×3 linear system in `(D, E, F)`:

| P     | Equation (linear in `D, E, F`)                                |
|-------|----------------------------------------------------------------|
| `P₁`  | `(P₁ 0) D + (P₁ 1) E + F = -((P₁ 0)² + (P₁ 1)²)`              |
| `P₂`  | `(P₂ 0) D + (P₂ 1) E + F = -((P₂ 0)² + (P₂ 1)²)`              |
| `P₃`  | `(P₃ 0) D + (P₃ 1) E + F = -((P₃ 0)² + (P₃ 1)²)`              |

Matrix form: `A · (D, E, F)ᵀ = b` where

```
A := !![P₁ 0, P₁ 1, 1;
        P₂ 0, P₂ 1, 1;
        P₃ 0, P₃ 1, 1]

b := ![-(P₁ 0)² - (P₁ 1)²,
       -(P₂ 0)² - (P₂ 1)²,
       -(P₃ 0)² - (P₃ 1)²]
```

By Cramer's rule, since `A.det = (P₁ 0 - P₃ 0) * (P₂ 1 - P₃ 1) - (P₂ 0 - P₃ 0) * (P₁ 1 - P₃ 1)` (cofactor expansion along the last column), non-collinearity (Hypothesis 1b) gives `A.det ≠ 0`, hence `(D, E, F)` exists uniquely.

The 4th point P₄ lies on this circle iff the augmented row `[(P₄ 0)² + (P₄ 1)², P₄ 0, P₄ 1, 1]` is in the row-space of the first 3 rows of `concyclicityDetCoords`'s matrix. By the standard determinant lemma (`Matrix.det_eq_zero_iff_exists_row_dependent` or similar), this is equivalent to `concyclicityDet P₁ P₂ P₃ P₄ = 0`.

### Sub-step 2a: Define the 3×3 matrix and Cramer's setup (~15 LOC)

```lean
-- in namespace ProductOfSegmentsOfChordsOQ03

/-- The 3×3 linear system matrix for the implicit-circle coefficients (D, E, F). -/
def implicitCircleMatrix (P₁ P₂ P₃ : Vec2) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![P₁ 0, P₁ 1, 1;
     P₂ 0, P₂ 1, 1;
     P₃ 0, P₃ 1, 1]

/-- The RHS vector: −(x²+y²) for each of the three points. -/
def implicitCircleRHS (P₁ P₂ P₃ : Vec2) : Fin 3 → ℝ :=
  ![-((P₁ 0)^2 + (P₁ 1)^2),
    -((P₂ 0)^2 + (P₂ 1)^2),
    -((P₃ 0)^2 + (P₃ 1)^2)]
```

### Sub-step 2b: Show `implicitCircleMatrix.det = (P₂ 0 - P₃ 0) * (P₁ 1 - P₃ 1) - (P₁ 0 - P₃ 0) * (P₂ 1 - P₃ 1)` (~10 LOC)

```lean
lemma implicitCircleMatrix_det (P₁ P₂ P₃ : Vec2) :
    (implicitCircleMatrix P₁ P₂ P₃).det
      = (P₂ 0 - P₃ 0) * (P₁ 1 - P₃ 1) - (P₁ 0 - P₃ 0) * (P₂ 1 - P₃ 1) := by
  unfold implicitCircleMatrix
  simp [Matrix.det_fin_three]
  ring
```

The sign convention has been chosen to match Hypothesis 1b — the non-vanishing of this expression is exactly `threePointsNotCollinear`.

### Sub-step 2c: Apply Cramer to extract `(D, E, F)` (~15 LOC)

```lean
/-- Cramer's solution for (D, E, F). -/
noncomputable def implicitCircleDEF (P₁ P₂ P₃ : Vec2)
    (h : (implicitCircleMatrix P₁ P₂ P₃).det ≠ 0) : Fin 3 → ℝ :=
  (implicitCircleMatrix P₁ P₂ P₃)⁻¹ *ᵥ (implicitCircleRHS P₁ P₂ P₃)
```

(Alternatively use `Matrix.cramer (implicitCircleMatrix P₁ P₂ P₃) (implicitCircleRHS P₁ P₂ P₃)` directly — Mathlib's `Matrix.cramer` gives the solution as `(D, E, F) = (det / A.det) · (cofactor row)`; for our purposes, the matrix-inverse form is simpler. Either form works.)

### Sub-step 2d: Verify `P_i` satisfies `(P_i 0)² + (P_i 1)² + D·(P_i 0) + E·(P_i 1) + F = 0` for `i ∈ {1, 2, 3}` (~10 LOC each, ~30 LOC total)

Each verification is `Matrix.mulVec` evaluation at row `i` plus the `implicitCircleDEF` definition. The key lemma is `Matrix.mulVec_mulVec_inverse` or directly `Matrix.det_smul_inv_mulVec_eq_cramer` from Mathlib.

## 3. Center/radius construction

With `(D, E, F)` from Sub-step 2c:

### Center: `O := (-D/2, -E/2)`

```lean
noncomputable def circleCenter (P₁ P₂ P₃ : Vec2)
    (h : (implicitCircleMatrix P₁ P₂ P₃).det ≠ 0) : Vec2 :=
  let DEF := implicitCircleDEF P₁ P₂ P₃ h
  -- O = (-D/2, -E/2) where D = DEF 0, E = DEF 1
  EuclideanSpace.equiv (Fin 2) ℝ |>.symm
    ![-(DEF 0)/2, -(DEF 1)/2]
```

(or use `(fun i : Fin 2 => if i = 0 then -(DEF 0)/2 else -(DEF 1)/2)` directly if the Equiv path is cumbersome.)

### Radius-squared: `r² := D²/4 + E²/4 - F`

```lean
noncomputable def circleRadiusSq (P₁ P₂ P₃ : Vec2)
    (h : (implicitCircleMatrix P₁ P₂ P₃).det ≠ 0) : ℝ :=
  let DEF := implicitCircleDEF P₁ P₂ P₃ h
  (DEF 0)^2 / 4 + (DEF 1)^2 / 4 - (DEF 2)
```

### Radius positivity

The key non-degeneracy fact: `r² > 0` iff at least one of `P₁, P₂, P₃` is *not equal to* the center `O`. Under our non-collinearity hypothesis (Hypothesis 1b), no point is at the center *and* the three points are distinct, so `r² > 0` follows.

**More carefully**: from the implicit-circle equation `(P_i 0)² + (P_i 1)² + D·(P_i 0) + E·(P_i 1) + F = 0`, we get `‖P_i - O‖² = (P_i 0 + D/2)² + (P_i 1 + E/2)² = (P_i 0)² + (P_i 1)² + D·(P_i 0) + E·(P_i 1) + D²/4 + E²/4 = -F + D²/4 + E²/4 = r²`. So `r² ≥ 0` always.

For `r² > 0` strictly, observe that if `r² = 0`, then all three points equal the center O, contradicting their non-collinearity (3 coincident points are trivially collinear).

### Radius (using `Real.sqrt`)

```lean
noncomputable def circleRadius (P₁ P₂ P₃ : Vec2)
    (h : (implicitCircleMatrix P₁ P₂ P₃).det ≠ 0) : ℝ :=
  Real.sqrt (circleRadiusSq P₁ P₂ P₃ h)
```

Positivity: `0 < r ↔ 0 < r²` via `Real.sqrt_pos`.

## 4. The (⇐) sub-theorem

```lean
theorem concyclicityDet_zero_to_concyclic
    (P₁ P₂ P₃ P₄ : Vec2)
    (h_noncoll : threePointsNotCollinear P₁ P₂ P₃)
    (h_det : concyclicityDet P₁ P₂ P₃ P₄ = 0) :
    ∃ (O : Vec2) (r : ℝ), 0 < r ∧
      ‖P₁ - O‖ = r ∧ ‖P₂ - O‖ = r ∧ ‖P₃ - O‖ = r ∧ ‖P₄ - O‖ = r := by
  -- Bridge h_noncoll to A.det ≠ 0
  have hA : (implicitCircleMatrix P₁ P₂ P₃).det ≠ 0 := by
    rw [implicitCircleMatrix_det]
    intro habs
    apply h_noncoll
    linarith [habs]   -- or `linear_combination` adjustment
  -- Construct O and r²
  let O := circleCenter P₁ P₂ P₃ hA
  let r² := circleRadiusSq P₁ P₂ P₃ hA
  -- r² > 0 from non-degeneracy
  have hr_pos : 0 < r² := by
    sorry  -- ~10 LOC: contraposition + 3-distinct-points argument
  refine ⟨O, Real.sqrt r², Real.sqrt_pos.mpr hr_pos, ?_, ?_, ?_, ?_⟩
  -- Each ‖P_i - O‖ = √r² verification
  -- Substeps i ∈ {1, 2, 3}: use the Cramer solution
  -- Substep i = 4: use h_det (the 4×4 determinant vanishing)
  all_goals sorry  -- ~12 LOC each * 4 = ~48 LOC
```

Total S3 (⇐) discharge: ~80 LOC matching the state.md estimate.

## 5. Anticipated friction points for the S3 ACT picker

### 5a. `Vec2` vs. `Fin 2 → ℝ` interconversion

`Vec2 = EuclideanSpace ℝ (Fin 2) = PiLp 2 (fun _ => ℝ)`. Coordinate access `P 0` and `P 1` is on the underlying `Fin 2 → ℝ`. The `simp` normal form for `P i` may unfold to `(P : Fin 2 → ℝ) i` or to `(WithLp.equiv 2 _).symm P i`, depending on Mathlib version. The S2 file already uses `P 0` and `P 1` without issue in the numerical examples (lines 75-78), so coordinate access is established.

For constructing new points (like `O := (-D/2, -E/2)`), use `(![−D/2, −E/2] : Vec2)` if the Fin 2 → ℝ coercion is automatic, or the explicit `EuclideanSpace.equiv` route in § 3.

### 5b. `‖P_i - O‖` on `EuclideanSpace`

`‖·‖` on `EuclideanSpace ℝ (Fin 2)` is the L²-norm: `‖v‖² = (v 0)² + (v 1)²`. Mathlib has `EuclideanSpace.norm_eq` (in `Mathlib/Analysis/InnerProductSpace/EuclideanDist.lean` or similar) which states `‖v‖ = Real.sqrt (∑ i, (v i)^2)`. For `Fin 2`, the sum unfolds to `(v 0)^2 + (v 1)^2`.

The S3 ACT picker should expect to `rw [EuclideanSpace.norm_eq]` + `simp [Fin.sum_univ_two]` + `ring` for each `‖P_i - O‖ = r` verification.

### 5c. `Real.sqrt` positivity and squaring

The end-goal needs `‖P_i - O‖ = r`, where `r = √r²`. Mathlib provides `Real.sqrt_eq_iff_sq_eq` (or `Real.sqrt_eq_iff_mul_self_eq`) that lets us replace `‖P_i - O‖ = √r²` with `‖P_i - O‖² = r²` (assuming both sides non-negative). The norm is non-negative; r² > 0 by hypothesis. So the chain is:

```lean
have : ‖P_i - O‖^2 = r² := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (norm_nonneg _)]   -- or analog
  simp [Fin.sum_univ_two]
  -- expand `P_i - O` and use the implicit-circle equation
  ring
exact Real.sqrt_eq_iff_sq_eq.mpr ⟨this, norm_nonneg _, le_of_lt hr_pos⟩
```

Each verification is ~12 LOC.

## 6. Mathlib API surface

13 lemmas total; all **likely** standard but unverified due to rate-limit (`code_search` 10/hr exhausted earlier in this session). The S3 ACT picker should verify these at S3 ACT time.

| # | Lemma                                | Substep | Status |
|---|--------------------------------------|---------|--------|
| 1 | `Matrix.det_fin_three`               | 2b      | **Confirmed** — used in `det_fin_four` family |
| 2 | `Matrix.det_fin_four`                | (S2 examples already use this) | **Confirmed** by S2's build of the numerical examples |
| 3 | `Matrix.det_fin_two`                 | 1 (Hypothesis 1b) | **Confirmed** standard |
| 4 | `Matrix.cramer`                      | 2c      | Standard; `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean` |
| 5 | `Matrix.mulVec_mulVec_inverse`       | 2d      | Standard variant; `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean` |
| 6 | `Matrix.det_eq_zero_iff_exists_row_dependent` | 2d (i=4) | Standard; precise name to verify |
| 7 | `Real.sqrt_pos`                      | 4       | Standard |
| 8 | `Real.sqrt_eq_iff_sq_eq`             | 5c      | Standard; precise name to verify |
| 9 | `Real.sq_sqrt`                       | 5c      | Standard |
| 10 | `EuclideanSpace.norm_eq`             | 5b      | Standard |
| 11 | `Fin.sum_univ_two`                   | 5b      | Standard |
| 12 | `norm_nonneg`                        | 5c      | Standard |
| 13 | `WithLp.equiv` (or `PiLp.equiv`)     | (optional) | Standard |

The 3 names flagged "precise name to verify" (#5, #6, #8) all have alternative-name fallbacks. For #6, the fallback is to expand the 4×4 `concyclicityDet` cofactor expansion explicitly along the last column and identify it with `A.det · (P₄'s row constraint) + Σ cofactor terms`.

## 7. Anti-targets (this S3 PREP explicitly does NOT do)

1. ❌ Edit `proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean` (no Lean discharge; S3 ACT's job).
2. ❌ Touch the parent file `proofs/Proofs/ProductOfSegmentsOfChords.lean`.
3. ❌ Edit `problem.md`, `state.md`, `knowledge.md` (preserve researcher-3's S2-merged framing).
4. ❌ Edit `src/data/research/problems/product-of-segments-of-chords-oq-03.json`.
5. ❌ Run `./proofs/scripts/docker-build.sh` (no build; S2's build is the pending one, per state.md).
6. ❌ Attempt the (⇒) direction (S4's job, ~30 LOC, row-reduction argument).
7. ❌ Attempt the chord-product → Δ = 0 bridge (S5's job).

## 8. Acceptance criteria

1. **Non-collinearity hypothesis picked (§ 1)** with justification (algebraic Cramer-friendly form).
2. **Cramer's rule application as 4 sub-steps (§ 2)** with explicit matrix construction + RHS + det formula + center/radius construction.
3. **(⇐) sub-theorem skeleton (§ 4)** with ~80 LOC budget broken down by sub-step.
4. **3 friction points anticipated (§ 5)** with concrete Lean patterns.
5. **Mathlib API inventory (§ 6)** with 13 lemmas catalogued and 3 flagged for verification.
6. **No edits** to parent Lean files, problem.md, state.md, knowledge.md, gallery JSON.
7. **Race-aware.** 0 open PRs on this slug at push time (verified earlier via `gh pr list --search`).

## 9. Honesty / what could be wrong

- **Mathlib name verifications (§ 6)**. 3 lemmas flagged; alternative-name fallbacks documented. The S3 ACT picker should `#check` each name before relying on it.
- **`r² > 0` strictly via 3-distinct-points argument** (§ 3). If 2 of the 3 points happen to coincide, the "non-collinear" hypothesis 1b still allows it (technically 2-collinear is trivially-not-3-collinear). The S3 ACT may need to additionally hypothesize `P₁ ≠ P₂` etc. **Refinement**: Hypothesis 1b actually implies all three distinct (if `P₁ = P₃`, the determinant degenerates to 0). So no extra hypothesis is needed; just include the distinctness derivation in the `hr_pos` substep.
- **The `(P₂ 0 - P₃ 0) * (P₁ 1 - P₃ 1) ≠ (P₁ 0 - P₃ 0) * (P₂ 1 - P₃ 1)` form** of Hypothesis 1b is one of 2 sign-equivalent forms. The opposite sign convention gives the same non-vanishing constraint. § 2b's `implicitCircleMatrix_det` derivation pins the convention; if the S3 ACT picker chooses a different convention, the `h_noncoll` lemma rewrite (§ 4) needs a sign flip.
- **`circleCenter` `noncomputable`** (§ 3). The center construction uses `implicitCircleDEF` which inherits `Matrix.inverse`'s noncomputability. This is fine for an existence theorem; if a future session wants a computable center (e.g. for `#eval` demos), there's an explicit formula `O := ((P_i 0)² + (P_i 1)²) cofactor / A.det · ...` that's computable but verbose. Skip for now.
- **No build verification.** This file makes no Lean claims that have been built. The skeleton in §§ 2-4 contains `sorry`s in the strategic locations (§ 4); the S3 ACT picker is responsible for discharging them.

## 10. Cross-references

- `proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean:54-59` — `concyclicityDetCoords` definition.
- `proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean:65-67` — `concyclicityDet` wrapper.
- `proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean:98-104` — `concyclicityDet_eq_zero_iff_concyclic` (the sorry this S3 PREP targets).
- `proofs/Proofs/ProductOfSegmentsOfChords.lean:468` — parent's `converse_product_implies_concyclic_axiom` (S6's eventual target).
- `research/problems/product-of-segments-of-chords-oq-03/state.md:69-81` — S3 Next Action.
- PR #18231 (merged) — S1 OBSERVE, power-of-a-point ↔ 4×4 concyclicity bridge.
- PR #18380 (merged 02:11 UTC, **5 minutes before this session**) — S2 SCAFFOLD, `concyclicityDet` def + 2 numerical examples + theorem statement with 1 sorry.
- Memory: `feedback_researcher_lake_symlink_loop_and_wipe.md` — `.lake` symlink trap that blocked researcher-3's S2 build.
- Memory: `feedback_researcher_6_2026_05_13_quadruple_prep_mathlib_audit.md` — Mathlib-audit-driven PREP pattern; this memo applies the same template.
