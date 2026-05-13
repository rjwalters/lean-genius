# S5 PREP — Shear-map volume calculation for n-dim Cassels parallelepiped

**Slug**: `minkowski-theorem-oq-02-oq-03`
**Phase**: PREP (doc-only — no Lean code or gallery JSON modified)
**Author**: researcher-11
**Date**: 2026-05-12
**Scope**: drills into the **S5 ACT step** flagged in
`state.md` as "the hardest step" of the 6-session ACT chain
(S2 symmetric → S3 measurable → S4 convex → **S5 volume** → S6 Minkowski
extraction). S1 OBSERVE (PR #18339, merged 22:39 UTC) only **named** the
shear map — this doc **drills in** with the explicit
`Matrix (Fin (n+1)) (Fin (n+1)) ℝ` form, determinant computation, and
the rectangular-volume integration chain.

## 1. Position vs in-flight PRs

| PR     | Status | What it touches                                                                          |
| ------ | ------ | ---------------------------------------------------------------------------------------- |
| #18339 | MERGED | `problem.md`, `knowledge.md`, `state.md`, JSON, `sessions/2026-05-12-s01-observe.md`     |
| (none) |   —    | No open PRs on this slug                                                                 |

**Orthogonality.** This PR touches only the single new file
`sessions/2026-05-12-s5-prep-shear-volume-generalization.md`. No edits
to `state.md`, `knowledge.md`, `problem.md`, Lean source, gallery JSON,
or research JSON.

## 2. The n=1 reference template

The axiom-free n=1 sibling `MinkowskiTheoremOQ02OQ01.lean` (lines 91–140)
gives the precise pattern S5 must generalise. Key ingredients:

```lean
private theorem shearMap_det (α : ℝ) :
    (Matrix.det (!![1, 0; α, -1] : Matrix (Fin 2) (Fin 2) ℝ)) = -1 := by
  simp [Matrix.det_fin_two]

theorem dirichletSet_volume (α : ℝ) (Q : ℕ) (hQ : 0 < Q) :
    MeasureTheory.volume (dirichletSet α Q) =
      ENNReal.ofReal (4 * ((Q : ℝ) + 1) / (Q : ℝ)) := by
  let M : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; α, -1]
  let T : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := M.toLin'
  have hdet : M.det = -1 := shearMap_det α
  -- T(v) = (v 0, αv₀ − v₁)
  -- Image rectangle: (-(Q+1), Q+1) × (-1/Q, 1/Q)
  -- vol(S) = vol(T⁻¹(rect)) = vol(rect) = 2(Q+1) · (2/Q) = 4(Q+1)/Q
  …
```

The chain has **four mechanical pieces**:

1. **Matrix form + determinant**: `!![1, 0; α, -1]`, `Matrix.det_fin_two` → `-1`.
2. **Shear formula**: `T v = (v 0, αv₀ − v₁)` via `Matrix.toLin'_apply` + `Matrix.mulVec` + `Fin.sum_univ_two`.
3. **Volume invariance under T**: `Measure.map T volume = volume` via
   `map_matrix_volume_pi_eq_smul_volume_pi hdet_ne`, then `hdet`, then `norm_num`.
4. **Rectangle volume**: `volume_pi_Ioo`, `Fin.prod_univ_two`, then numerical.

## 3. The n-dim generalisation

For `n : ℕ` with `n+1` coordinates, the matrix is **lower-triangular**:

```
M := !![1,    0,    0,    …,    0;
        α 0, -1,    0,    …,    0;
        α 1,  0,   -1,    …,    0;
        …;
        α (n-1), 0, 0,    …,   -1]
```

i.e. `M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ` with

```
M i j = if j = 0 then (if i = 0 then 1 else α (i.pred ‹i ≠ 0›))
        else if i = j then -1 else 0
```

**Concise Mathlib spelling** using `Matrix.of`:

```lean
def shearM (α : Fin n → ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  Matrix.of fun i j =>
    if j = 0 then
      Fin.cases (1 : ℝ) α i        -- i = 0 ↦ 1, i = succ k ↦ α k
    else if i = j then (-1 : ℝ) else 0
```

Or, more elegantly using `Matrix.diagonal` + a rank-1 update:

```lean
def shearM (α : Fin n → ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  Matrix.diagonal (fun i => Fin.cases (1 : ℝ) (fun _ => -1) i)
    + Matrix.of (fun i j =>
        if h : j = 0 ∧ i ≠ 0 then Fin.cases (0 : ℝ) α i else 0)
```

The diagonal form may simp more cleanly with `Matrix.diagonal_apply_*`
lemmas but introduces a sum-vs-`Matrix.of` style mismatch with the
linear-map machinery. **Recommendation**: use the concrete `Matrix.of`
spelling above (matches the n=1 `!![…]` template).

### 3.1 Determinant via `Matrix.det_of_lowerTriangular`

The matrix is lower-triangular (zero strictly above the diagonal):

```lean
theorem shearM_lowerTriangular (α : Fin n → ℝ) :
    (shearM α).BlockTriangular id := by
  intro i j hij
  simp only [shearM, Matrix.of_apply]
  split_ifs with hj heq
  · -- j = 0 ∧ i ≠ 0; but i < j = 0 is impossible
    exact absurd (Fin.zero_le _) (not_le.mpr (hj ▸ hij)) |>.elim
  · exact heq.symm ▸ rfl  -- contradiction: i < j requires i ≠ j
  · rfl
```

(Sketch only; exact spelling varies with the `BlockTriangular` API at
v4.26.) Then

```lean
Matrix.det_of_lowerTriangular (shearM α) shearM_lowerTriangular
  = ∏ i, (shearM α) i i
  = 1 * (∏ k : Fin n, -1)
  = (-1) ^ n
```

via `Fin.prod_univ_succ` (split off `i = 0`) and
`Finset.prod_const` plus `Finset.card_univ_fin`.

**Mathlib lemmas needed**:

| Lemma                                      | Path                                                                   |
| ------------------------------------------ | ---------------------------------------------------------------------- |
| `Matrix.det_of_lowerTriangular`            | `Mathlib.LinearAlgebra.Matrix.Block`                                   |
| `Matrix.BlockTriangular`                   | (same file)                                                            |
| `Fin.prod_univ_succ`                       | `Mathlib.Algebra.BigOperators.Fin`                                     |
| `Finset.prod_const`                        | `Mathlib.Algebra.BigOperators.Basic`                                   |
| `Finset.card_univ_fin`                     | `Mathlib.Data.Fintype.Card`                                            |

So `(shearM α).det = (-1) ^ n`, and `|det| = 1` regardless of parity.

### 3.2 Volume invariance

The Mathlib lemma at v4.26.0 (used at n=1):

```lean
theorem map_matrix_volume_pi_eq_smul_volume_pi
    {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℝ} (hM : M.det ≠ 0) :
    Measure.map M.toLin' volume =
      ENNReal.ofReal |M.det⁻¹| • volume
```

For our `M = shearM α`: `M.det = (-1)^n`, so `|M.det| = 1`, so
`|M.det⁻¹| = 1`, and `Measure.map M.toLin' volume = 1 • volume = volume`.

The discharge pattern is:

```lean
have hdet : (shearM α).det = (-1) ^ n := by
  rw [Matrix.det_of_lowerTriangular _ (shearM_lowerTriangular α)]
  -- Now goal is ∏ i, shearM α i i = (-1)^n
  simp only [shearM, Matrix.of_apply]
  rw [Fin.prod_univ_succ]
  · simp [Fin.cases_zero]
    -- Reduces to ∏ k : Fin n, -1 = (-1)^n
    exact Finset.prod_const_neg_one_eq_pow n  -- name may differ; check API
have hdet_ne : (shearM α).det ≠ 0 := by
  rw [hdet]; exact pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0)
have h_map : Measure.map (shearM α).toLin' volume = volume := by
  rw [map_matrix_volume_pi_eq_smul_volume_pi hdet_ne, hdet]
  -- Goal: ENNReal.ofReal |((-1)^n)⁻¹| • volume = volume
  rw [show |((-1 : ℝ) ^ n)⁻¹| = 1 by
    rw [abs_inv]; simp [abs_pow, abs_neg, abs_one]]
  simp [ENNReal.ofReal_one, one_smul]
```

### 3.3 Pre-image rectangle

The Cassels set:

```lean
def dirichletSetN (α : Fin n → ℝ) (Q : ℕ) : Set (Fin (n+1) → ℝ) :=
  {v | |v 0| < (Q : ℝ)^n + 1 ∧
       ∀ i : Fin n, |α i * v 0 - v i.succ| < 1 / (Q : ℝ)}
```

Under `T = (shearM α).toLin'`:

- `T v 0 = v 0` (by `Matrix.toLin'_apply` + `Matrix.mulVec` + the
  first row of `shearM α` being `(1, 0, 0, …, 0)`).
- `T v (Fin.succ k) = α k * v 0 - v (Fin.succ k)` (the
  `(k+1)`-th row of `shearM α` is `(α k, 0, …, 0, -1, 0, …, 0)`
  with the `-1` at column `k+1`).

So `T⁻¹(rect) = dirichletSetN α Q` where

```lean
def rectN (Q : ℕ) (n : ℕ) : Set (Fin (n+1) → ℝ) :=
  Set.pi Set.univ fun i : Fin (n+1) =>
    Fin.cases
      (Set.Ioo (-((Q : ℝ)^n + 1)) ((Q : ℝ)^n + 1))   -- i = 0
      (fun _ => Set.Ioo (-(1 / (Q : ℝ))) (1 / (Q : ℝ)))  -- i = succ k
      i
```

The `dirichletSetN ⇔ T⁻¹ rectN` equivalence is by:

```lean
have h_eq : dirichletSetN α Q = (shearM α).toLin' ⁻¹' rectN Q n := by
  ext v
  simp only [dirichletSetN, rectN, Set.mem_setOf_eq, Set.mem_preimage,
             Set.mem_pi, Set.mem_univ, forall_true_left,
             Fin.forall_fin_succ, Set.mem_Ioo, Fin.cases_zero,
             Fin.cases_succ, Tv0, Tv_succ]
  -- Same shape as n=1: peel `abs_lt`, distribute over the conj
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨abs_lt.mp h0, fun k => ?_⟩
    exact abs_lt.mp (h1 k)
  · rintro ⟨h0, h1⟩
    refine ⟨abs_lt.mpr h0, fun k => ?_⟩
    exact abs_lt.mpr (h1 k)
```

where `Tv0` and `Tv_succ` are explicit shear-formula lemmas:

```lean
have Tv0 : ∀ v : Fin (n+1) → ℝ, (shearM α).toLin' v 0 = v 0 := fun v => by
  simp [shearM, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ]
  -- Reduces: 1 · v 0 + ∑ k, 0 · v (succ k) = v 0
  ring

have Tv_succ : ∀ (v : Fin (n+1) → ℝ) (k : Fin n),
    (shearM α).toLin' v k.succ = α k * v 0 - v k.succ := fun v k => by
  simp [shearM, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ]
  -- Reduces: α k · v 0 + ∑ j, (if succ j = succ k then -1 else 0) · v (succ j) = α k · v 0 - v (succ k)
  ring  -- may need an extra rw [Finset.sum_ite_eq']
```

### 3.4 Volume of the rectangle

Using `volume_pi_Ioo` with `Fin.prod_univ_succ`:

```lean
have h_rect_vol :
    MeasureTheory.volume (rectN Q n) =
      ENNReal.ofReal (2 * ((Q : ℝ)^n + 1) * (2 / (Q : ℝ))^n) := by
  rw [rectN, volume_pi_Ioo, Fin.prod_univ_succ]
  -- First factor: 2((Q^n) + 1)
  -- Subsequent product: ∏ k : Fin n, (2/Q) = (2/Q)^n
  simp only [Fin.cases_zero, Fin.cases_succ]
  rw [show ∀ x : ℝ, x - (-x) = 2 * x from fun _ => by ring]
    -- pointwise factor cleanup
  rw [Finset.prod_const, Finset.card_univ_fin]
  rw [ENNReal.ofReal_mul (by positivity)]
  -- May need additional ofReal_pow lemma
  rfl
```

### 3.5 Assembly

```lean
theorem dirichletSetN_volume (α : Fin n → ℝ) (Q : ℕ) (hQ : 0 < Q) :
    MeasureTheory.volume (dirichletSetN α Q) =
      ENNReal.ofReal (2 * ((Q : ℝ)^n + 1) * (2 / (Q : ℝ))^n) := by
  rw [h_eq, ← Measure.map_apply h_meas_T h_meas_rect, h_map, h_rect_vol]
```

with the obvious `h_meas_T` (`Continuous → Measurable`) and `h_meas_rect`
(`MeasurableSet.univ_pi`) hypotheses.

## 4. The volume-vs-threshold inequality

For S6 (Minkowski extraction), we need

```lean
theorem dirichletSetN_volume_gt_threshold (α : Fin n → ℝ) (Q : ℕ) (hQ : 0 < Q) :
    (2 : ENNReal) ^ (n+1) <
      MeasureTheory.volume (dirichletSetN α Q) := by …
```

The arithmetic: `2 · (Qⁿ+1) · (2/Q)ⁿ = 2^(n+1) · (Qⁿ+1)/Qⁿ
= 2^(n+1) · (1 + Q^{-n}) > 2^(n+1)` for `Q ≥ 1`.

Discharge sketch:

```lean
  rw [dirichletSetN_volume α Q hQ]
  have hQpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ
  have hQn_pos : (0 : ℝ) < (Q : ℝ)^n := pow_pos hQpos n
  have key : (2 : ℝ)^(n+1) < 2 * ((Q : ℝ)^n + 1) * (2 / (Q : ℝ))^n := by
    rw [show (2 / (Q : ℝ))^n = 2^n / (Q : ℝ)^n by ring]
    rw [show (2 : ℝ)^(n+1) = 2 * 2^n from by ring]
    -- Goal: 2 · 2^n < 2 · (Q^n + 1) · (2^n / Q^n)
    --       = 2 · (Q^n + 1) · 2^n / Q^n
    rw [show 2 * ((Q : ℝ)^n + 1) * (2^n / (Q : ℝ)^n) =
            2 * 2^n * ((Q : ℝ)^n + 1) / (Q : ℝ)^n from by ring]
    rw [lt_div_iff₀ hQn_pos]
    nlinarith [hQn_pos]
  calc (2 : ENNReal) ^ (n+1)
      = ENNReal.ofReal (2^(n+1)) := by
        rw [show ((2 : ℝ)^(n+1) : ℝ) = ((2 : ENNReal)^(n+1)).toReal from by
          rw [ENNReal.toReal_pow]; norm_num]
        rw [ENNReal.ofReal_toReal]
        exact ENNReal.pow_ne_top (by norm_num)
    _ < ENNReal.ofReal (2 * ((Q : ℝ)^n + 1) * (2 / (Q : ℝ))^n) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr key
```

**Estimated S5 ACT size**: ~120–180 Lean lines, dominated by:

| Step                                 | Est. lines |
| ------------------------------------ | ---------- |
| `shearM` definition + helper lemmas  | ~20        |
| `shearM_lowerTriangular`              | ~15        |
| `shearM_det` (= `(-1)^n`)             | ~10        |
| `Tv0`, `Tv_succ` shear-formula lemmas | ~30        |
| `h_eq` (preimage equality)            | ~20        |
| `h_map` (volume invariance)           | ~10        |
| `h_rect_vol`                          | ~30        |
| Main `dirichletSetN_volume` assembly  | ~10        |
| `dirichletSetN_volume_gt_threshold`   | ~25        |

This is **comparable to** the n=1 reference (lines 91–155 of
`MinkowskiTheoremOQ02OQ01.lean`, ~65 lines total, but n=1 hard-codes
many things). The blow-up at general n is mostly in the
`Fin.prod_univ_succ` / `Fin.sum_univ_succ` bookkeeping.

## 5. Risk audit

### 5.1 `Matrix.det_of_lowerTriangular` vs `Matrix.det_blockTriangular`

At v4.26.0, the canonical name may be `Matrix.det_of_lowerTriangular`
or `Matrix.det_blockTriangular` or `Matrix.BlockTriangular.det`. The
S5 ACT session must `#check` the exact name. If absent in the form
above, fall back to:

```lean
Matrix.det_eq_prod_diag_of_blockTriangular
```

or, lacking that, expand directly via `Matrix.det_succ_column_zero`
(Laplace expansion along column 0) plus induction on `n`:

```lean
-- Inductive proof: det(shearM α) = 1 · det((shearM α).submatrix Fin.succ Fin.succ) - 0 - ... = det(diag(-1, -1, ..., -1)) = (-1)^n
```

### 5.2 `map_matrix_volume_pi_eq_smul_volume_pi` decidability

The Mathlib lemma name at v4.26.0 may also be stated as
`Matrix.map_matrix_volume_pi_eq_smul_volume_pi` (with the namespace
prefix). The n=1 file uses the un-namespaced form (`open Matrix`
inside the file scope). S5 ACT should keep the same `open Matrix`
hygiene to match.

### 5.3 `(-1)^n = ±1` in `Measure.map`

After `map_matrix_volume_pi_eq_smul_volume_pi`, the goal is
`ENNReal.ofReal |((-1)^n)⁻¹| • volume = volume`. The hand-roll:

```lean
|((-1 : ℝ)^n)⁻¹| = |(-1)^n|⁻¹ = 1⁻¹ = 1
```

requires `abs_inv`, `abs_pow`, `abs_neg`, `abs_one`. All standard
at v4.26.

### 5.4 `Fin.cases` simp normal form

The `Fin.cases ... ...` API is the canonical way to define functions
on `Fin (n+1)` by splitting at 0. The simp lemmas `Fin.cases_zero`
and `Fin.cases_succ` are `@[simp]`-tagged and should fire in the
shear-formula computations. **Risk**: if Mathlib's `Fin.cases` has
been deprecated in favour of `Fin.consInduction` or similar, the
shear matrix definition will need adjustment.

### 5.5 Universe issue with `(Fin (n+1) → ℝ) →ₗ[ℝ] (Fin (n+1) → ℝ)`

None expected — all types are `Type 0`. The `Matrix.toLin'` API is
specifically designed for `Fin n → α` modules.

## 6. Anti-targets (do NOT attempt in S5 ACT)

* ❌ **Don't try to define `shearM` as `Matrix.diagonal` + a rank-1
  correction.** The `(α k)` column is in column 0, not a rank-1 perturbation;
  the result is messier than the explicit `Matrix.of` spelling.
* ❌ **Don't expand the determinant via `Matrix.det_succ_row_zero`
  before trying `Matrix.det_of_lowerTriangular`.** Lower-triangular
  determinant is the canonical tactic; row-expansion would yield a
  recursive identity with `(n+1)` terms.
* ❌ **Don't try to prove `Tv0` and `Tv_succ` from `Matrix.mulVec_smul`
  or `LinearMap.toMatrix_apply`.** The direct `Matrix.toLin'_apply +
  Matrix.mulVec + dotProduct + Fin.sum_univ_succ` chain is what the
  n=1 file uses; same pattern transfers.
* ❌ **Don't generalise to `n : Type*` with `[Fintype n]` and abstract
  basis.** The Cassels parallelepiped is specifically tied to the
  `Fin (n+1)` indexing with `0` as the "common-denominator" coordinate;
  abstracting away the index structure complicates the rectangle
  description.

## 7. No-edit guarantee

This PR touches **only**:

```
research/problems/minkowski-theorem-oq-02-oq-03/sessions/
    2026-05-12-s5-prep-shear-volume-generalization.md
```

No existing file is modified. Branch
`research/minkowski-oq02oq03-s5-prep-shear-volume-*` is conflict-free
against any future S2/S3/S4 ACT PRs (they will edit
`proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean`, `state.md`,
`knowledge.md`, JSON — none of which this PR touches).

## 8. Done When (this PREP session)

- [x] n=1 reference template summarised (Section 2).
- [x] n-dim `shearM` explicit Matrix form (Section 3).
- [x] Lower-triangular determinant chain identified (Section 3.1).
- [x] Volume-invariance chain via `map_matrix_volume_pi_eq_smul_volume_pi`
  (Section 3.2).
- [x] Shear-formula lemmas `Tv0` / `Tv_succ` written out (Section 3.3).
- [x] Rectangle-volume integration via `volume_pi_Ioo` + `Fin.prod_univ_succ`
  (Section 3.4).
- [x] Volume-vs-threshold inequality proven by hand (Section 4).
- [x] S5 ACT estimated line count and risk audit (Sections 4–5).
- [x] Anti-targets enumerated (Section 6).
- [x] No edits outside `sessions/` (Section 7).

## 9. Honest framing

1. **No `lake env lean` probe was performed.** All Mathlib names
   cross-referenced from `MinkowskiTheoremOQ02OQ01.lean` lines 91–155
   and from the `Mathlib.LinearAlgebra.Matrix.Block` namespace.
2. **`Matrix.det_of_lowerTriangular` exact name at v4.26.0 unverified.**
   The fallback (Laplace expansion + induction on `n`) is 5–10 lines
   if the canonical lemma is renamed.
3. **`Finset.prod_const_neg_one_eq_pow n` name conjectural.** The
   underlying identity `∏ k : Fin n, (-1 : ℝ) = (-1)^n` is `rfl`-ish
   via `Finset.prod_const` + `Finset.card_univ_fin`; the exact lemma
   chain may need a 2-line proof rather than a 1-name lookup.
4. **The `Tv_succ` proof requires `Finset.sum_ite_eq'`** (or
   `Finset.sum_eq_single`) to pick out the `j = k` term in
   `∑ j, (if succ j = succ k then -1 else 0) · v (succ j)`. Mentioned
   in §3.3 but not fully written out.

## References

- Parent: `proofs/Proofs/MinkowskiTheoremOQ02OQ01.lean` (axiom-free
  n=1 sibling).
- Mathlib v4.26.0 (`mathlib4` HEAD):
  - `Mathlib/LinearAlgebra/Matrix/Block.lean` (`BlockTriangular`,
    `det_of_lowerTriangular` / `det_blockTriangular`).
  - `Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
    (`map_matrix_volume_pi_eq_smul_volume_pi`).
  - `Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
    (`volume_pi_Ioo`).
  - `Mathlib/Algebra/BigOperators/Fin.lean` (`Fin.prod_univ_succ`,
    `Fin.sum_univ_succ`).
- Cassels, J.W.S. (1957). *An Introduction to the Geometry of
  Numbers*. Springer, Theorem I.II.A.
- In flight: none.
- Merged: PR #18339 (S1 OBSERVE).
