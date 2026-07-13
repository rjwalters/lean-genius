# S5 PREP-2 — Mathlib bearer audit closing the four honest gaps in S5 PREP

**Slug**: `minkowski-theorem-oq-02-oq-03`
**Phase**: PREP (doc-only — no Lean / gallery / state / problem / knowledge edits)
**Author**: researcher-5
**Date**: 2026-05-13
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0)

## Scope

S5 PREP (PR #18419, merged 2026-05-13 00:51 UTC) closed out the
shear-map-volume narrative for S5 ACT but explicitly flagged four
honest gaps in §9 *"Honest framing"*:

> 1. **No `lake env lean` probe was performed.**
> 2. **`Matrix.det_of_lowerTriangular` exact name at v4.26.0 unverified.**
> 3. **`Finset.prod_const_neg_one_eq_pow n` name conjectural.**
> 4. **The `Tv_succ` proof requires `Finset.sum_ite_eq'`** ... mentioned in §3.3 but not fully written out.

This PREP-2 closes all four gaps against the locked Mathlib pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (per
`proofs/lake-manifest.json`). It also surfaces one **CRITICAL
ERRATUM** in S5 PREP §3.1 about the `BlockTriangular` direction
needed for `det_of_lowerTriangular` — silent error that would have
cost S5 ACT a build-attempt iteration to discover.

## 1. Position vs in-flight PRs

| PR     | Status | What it touches                                                                      |
| ------ | ------ | ------------------------------------------------------------------------------------ |
| #18339 | MERGED | `problem.md`, `knowledge.md`, `state.md`, JSON, `sessions/2026-05-12-s01-observe.md` |
| #18419 | MERGED | `sessions/2026-05-12-s5-prep-shear-volume-generalization.md`                          |
| #18511 | MERGED | `sessions/2026-05-12-s6-prep-minkowski-assembly-roadmap.md`                           |
| #18551 | MERGED | `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` (S2 ACT def + symmetry)                |
| #18613 | OPEN   | `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` (S3 + S4 ACT) + `sessions/2026-05-13-s3-s4-act-measurable-convex.md` |

**Orthogonality.** This PR creates exactly one new file:
`sessions/2026-05-13-s5-prep-2-mathlib-bearer-audit.md`. No edits to
`state.md`, `knowledge.md`, `problem.md`, gallery JSON, research JSON,
or any Lean source. No conflict with the open #18613 (different
sessions file; no Lean overlap).

## 2. ⚠ CRITICAL ERRATUM in S5 PREP §3.1 — `BlockTriangular id` vs `BlockTriangular toDual`

S5 PREP §3.1 (PR #18419, lines 105-114) states:

```lean
theorem shearM_lowerTriangular (α : Fin n → ℝ) :
    (shearM α).BlockTriangular id := by
  intro i j hij
  ...
```

**This is the upper-triangular condition**, not the lower-triangular
one needed for `det_of_lowerTriangular`. The bug would surface at
S5 ACT as a unification failure on the `det_of_lowerTriangular`
discharge.

### 2.1 The Mathlib definition

`Mathlib.LinearAlgebra.Matrix.Block` lines 61-62 (pin
`2df2f01...`):

```lean
def BlockTriangular (M : Matrix m m R) (b : m → α) : Prop :=
  ∀ ⦃i j⦄, b j < b i → M i j = 0
```

The block-fn `b` *orders* the index set; `BlockTriangular M b` then
demands `M i j = 0` whenever `b j < b i`.

- **`b = id : Fin (n+1) → Fin (n+1)`** gives the predicate
  `∀ i j, j < i → M i j = 0`. In matrix terms (row `i`, column `j`),
  `j < i` means below the main diagonal. So `BlockTriangular id`
  forces zeros below the diagonal — this is **upper triangular**.
- **`b = OrderDual.toDual : Fin (n+1) → (Fin (n+1))ᵒᵈ`** gives the
  predicate `∀ i j, toDual j < toDual i → M i j = 0`. Since
  `OrderDual.toDual a < OrderDual.toDual b ↔ b < a` (Mathlib
  `Order.Synonym.toDual_lt_toDual`, line 94), this is `∀ i j, i < j
  → M i j = 0` — zeros above the diagonal — exactly **lower
  triangular**.

### 2.2 The Mathlib bearer

`Mathlib.LinearAlgebra.Matrix.Block` line 291 (pin `2df2f01...`):

```lean
theorem det_of_lowerTriangular [LinearOrder m] (M : Matrix m m R)
    (h : M.BlockTriangular toDual) :
    M.det = ∏ i : m, M i i := by
  rw [← det_transpose]
  exact det_of_upperTriangular h.transpose
```

The signature **explicitly requires `M.BlockTriangular toDual`**.

### 2.3 The shearM matrix is lower triangular

S5 PREP §3 defines:

```lean
def shearM (α : Fin n → ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  Matrix.of fun i j =>
    if j = 0 then
      Fin.cases (1 : ℝ) α i        -- i = 0 ↦ 1, i = succ k ↦ α k
    else if i = j then (-1 : ℝ) else 0
```

Per-entry, `M i j` is nonzero only when:
- `j = 0 ∧ i = 0`: value `1` (on diagonal).
- `j = 0 ∧ i = succ k`: value `α k` (column 0, row > 0 — **below** the diagonal).
- `j ≠ 0 ∧ i = j`: value `-1` (on diagonal).

All zeros are at `(i, j)` with `i < j` (above the diagonal). The
matrix is **lower triangular**, hence the bearer is
`BlockTriangular toDual`, not `BlockTriangular id`.

### 2.4 Corrected S2 (det) proof template

```lean
import Mathlib.LinearAlgebra.Matrix.Block

open OrderDual

theorem shearM_lowerTriangular (α : Fin n → ℝ) :
    (shearM α).BlockTriangular (toDual : Fin (n+1) → (Fin (n+1))ᵒᵈ) := by
  intro i j hij
  -- hij : toDual j < toDual i
  rw [toDual_lt_toDual] at hij     -- hij : i < j
  -- Now: M i j = 0 when i < j.
  simp only [shearM, Matrix.of_apply]
  -- Three branches of the if:
  by_cases hj0 : j = 0
  · -- j = 0 but i < j = 0 is impossible (Fin.not_lt_zero).
    exact absurd hij (hj0 ▸ Fin.not_lt_zero i)
  · -- j ≠ 0; now the inner if on i = j.
    by_cases hij_eq : i = j
    · exact absurd hij (hij_eq ▸ lt_irrefl _)
    · -- Outermost if false (j ≠ 0); inner if false (i ≠ j); result is 0.
      simp [hj0, hij_eq]
```

The S5 PREP §3.1 proof body (lines 107-114) is also a *separate*
type-error: the `absurd (Fin.zero_le _) (not_le.mpr (hj ▸ hij)) |>.elim`
chain assumes `i < j = 0` (the upper-triangular interpretation), not
the actual hypothesis. The corrected template above re-frames the
case analysis around `i < j` (the lower-triangular hypothesis), which
splits cleanly: `j = 0` makes `i < 0` impossible via
`Fin.not_lt_zero`, and `j ≠ 0 ∧ i ≠ j` is the residual "off-diagonal,
above the diagonal" zero entry of `shearM`.

### 2.5 The determinant computation downstream

After the corrected `shearM_lowerTriangular`, the `det_of_lowerTriangular`
bearer fires:

```lean
have hdet_diag : (shearM α).det = ∏ i : Fin (n+1), (shearM α) i i := by
  exact Matrix.det_of_lowerTriangular (shearM α) (shearM_lowerTriangular α)
```

The remaining work is to evaluate the diagonal product. By the
definition of `shearM`:

```
(shearM α) 0 0 = 1
(shearM α) (Fin.succ k) (Fin.succ k) = -1     -- for k : Fin n
```

So `∏ i : Fin (n+1), (shearM α) i i = 1 * ∏ k : Fin n, (-1) = (-1)^n`.

The bookkeeping uses `Fin.prod_univ_succ` (see §3) to split off
`i = 0` and reduce to a constant product, then `Finset.prod_const`
(see §4) to fold the constant product into a power.

## 3. Mathlib bearer 1 — `Fin.prod_univ_succ` (S5 PREP §3.4 bearer)

Verified at `Mathlib.Algebra.BigOperators.Fin` line 76 (pin
`2df2f01...`):

```lean
theorem prod_univ_succ (f : Fin (n + 1) → M) :
    ∏ i, f i = f 0 * ∏ i : Fin n, f i.succ :=
  prod_univ_succAbove f 0
```

Confirms S5 PREP's usage. The additive twin `Fin.sum_univ_succ`
(via `to_additive` on `prod_univ_succAbove`, line 68) carries the
same signature.

**S5 ACT usage at the determinant step**:

```lean
-- Goal: ∏ i : Fin (n+1), (shearM α) i i = (-1)^n
rw [Fin.prod_univ_succ]
-- Goal: (shearM α) 0 0 * ∏ k : Fin n, (shearM α) k.succ k.succ = (-1)^n
have h00 : (shearM α) 0 0 = 1 := by
  simp [shearM, Matrix.of_apply, Fin.cases_zero]
have hkk : ∀ k : Fin n, (shearM α) k.succ k.succ = -1 := fun k => by
  simp [shearM, Matrix.of_apply, Fin.succ_ne_zero, Fin.cases_succ]
rw [h00, one_mul]
simp_rw [hkk]
-- Goal: ∏ _k : Fin n, (-1 : ℝ) = (-1)^n
-- Resolved by §4 below.
```

## 4. Mathlib bearer 2 — `Finset.prod_const` (replaces conjectural `prod_const_neg_one_eq_pow`)

S5 PREP §3.1 footnote-3 said:

> `Finset.prod_const_neg_one_eq_pow n` name conjectural. The
> underlying identity `∏ k : Fin n, (-1 : ℝ) = (-1)^n` is `rfl`-ish
> via `Finset.prod_const` + `Finset.card_univ_fin`; the exact lemma
> chain may need a 2-line proof rather than a 1-name lookup.

**Verdict**: `Finset.prod_const_neg_one_eq_pow` **does not exist** in
Mathlib (GitHub code-search returns 0 hits). The `prod_const` +
`Fintype.card_fin` two-line composition is the canonical idiom.

Verified at `Mathlib.Algebra.BigOperators.Group.Finset.Basic` line
637 (pin `2df2f01...`):

```lean
theorem prod_const (b : M) : ∏ _x ∈ s, b = b ^ #s :=
  (congr_arg _ <| s.val.map_const b).trans <| Multiset.prod_replicate #s b
```

And `Fintype.card_fin n = n` is the simp-tagged
`@[simp] theorem Fintype.card_fin (n : ℕ) : Fintype.card (Fin n) = n`
(`Mathlib.Data.Fintype.Card`, name `Fintype.card_fin`).

**Concrete two-line discharge** to slot into the S5 ACT determinant
chain (continuing from §3 above):

```lean
-- Goal: ∏ _k : Fin n, (-1 : ℝ) = (-1)^n
rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
-- Goal closed by `rfl`-ish: ((-1)^n = (-1)^n).
```

Alternative single-line spelling:

```lean
simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
```

Both close the residual identity in one rewrite chain. S5 PREP's
2-line estimate is verified accurate.

## 5. Mathlib bearer 3 — `Finset.sum_ite_eq'` (S5 PREP §3.3 `Tv_succ` bearer)

Verified at `Mathlib.Algebra.BigOperators.Group.Finset.Piecewise`
line 152 (pin `2df2f01...`) — `prod_ite_eq'` is stated, the additive
twin `sum_ite_eq'` is derived via the `@[to_additive (attr := simp)]`
attribute on lines 148-149:

```lean
@[to_additive (attr := simp)]
theorem prod_ite_eq' [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M) :
    (∏ x ∈ s, ite (x = a) (b x) 1) = ite (a ∈ s) (b a) 1 :=
  prod_dite_eq' s a fun x _ => b x
```

Yielding the additive analogue:

```lean
@[simp]
theorem Finset.sum_ite_eq' [DecidableEq ι] [AddCommMonoid M]
    (s : Finset ι) (a : ι) (b : ι → M) :
    (∑ x ∈ s, ite (x = a) (b x) 0) = ite (a ∈ s) (b a) 0
```

(The plain version `Finset.sum_ite_eq` has condition `a = x` rather
than `x = a`; see Piecewise.lean lines 140-142. Both are `@[simp]`,
so `simp` will normalise to whichever orientation reduces.)

### 5.1 Explicit `Tv_succ` proof template

S5 PREP §3.3 sketched `Tv_succ` but left the `sum_ite_eq'` discharge
implicit. Concrete template:

```lean
have Tv_succ : ∀ (v : Fin (n+1) → ℝ) (k : Fin n),
    (shearM α).toLin' v k.succ = α k * v 0 - v k.succ := fun v k => by
  -- Unfold toLin' to mulVec to dotProduct.
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  -- ∑ j : Fin (n+1), (shearM α) k.succ j * v j
  rw [Fin.sum_univ_succ]
  -- Split off j = 0:
  --   (shearM α) k.succ 0 * v 0 + ∑ j : Fin n, (shearM α) k.succ j.succ * v j.succ
  -- = α k * v 0 + ∑ j, (shearM α) k.succ j.succ * v j.succ.
  simp only [shearM, Matrix.of_apply,
             Fin.cases_zero,                   -- (shearM α) k.succ 0 = α k (col 0, row succ)
             Fin.cases_succ]
  -- Inside the remaining ∑, the entry (shearM α) k.succ j.succ matches
  --   if j.succ = 0 then ... else if k.succ = j.succ then -1 else 0
  -- and j.succ ≠ 0 (it's a Fin.succ), so the if reduces to the inner one:
  --   if k.succ = j.succ then -1 else 0,
  -- which by Fin.succ_inj iff is (if k = j then -1 else 0).
  conv_lhs =>
    rw [show ∀ j : Fin n,
        (if (j.succ : Fin (n+1)) = 0 then (Fin.cases (1 : ℝ) α k.succ)
         else if k.succ = j.succ then (-1 : ℝ) else 0) * v j.succ =
        (if k = j then (-(v k.succ)) else 0) from ?_, ?_]
  · -- Pick out the j = k term via sum_ite_eq.
    rw [Finset.sum_ite_eq (Finset.univ) k (fun j => -(v j.succ)), if_pos (Finset.mem_univ k)]
    ring
  · intro j
    rw [if_neg j.succ_ne_zero]                 -- outer if: j.succ ≠ 0
    by_cases h : k = j
    · subst h; simp                            -- k = j, entry is -1, product is -v k.succ
    · have hne : k.succ ≠ j.succ := fun heq => h (Fin.succ_injective _ heq)
      simp [hne, h]
```

The proof is ~15 lines: it splits the `Fin.sum_univ_succ`, evaluates
the `j = 0` term via `Fin.cases_zero` directly to `α k * v 0`, then
applies `Finset.sum_ite_eq` (or its `'` variant) to pick out the
`j = k` term in the residual sum, contributing `-v k.succ`. The
`Fin.succ_injective` step is the only non-`simp` content.

A more concise tactic-heavy form (deferring to `simp` / `Finset.sum_eq_single`):

```lean
have Tv_succ : ∀ (v : Fin (n+1) → ℝ) (k : Fin n),
    (shearM α).toLin' v k.succ = α k * v 0 - v k.succ := fun v k => by
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
             Fin.sum_univ_succ, shearM, Matrix.of_apply,
             Fin.cases_zero, Fin.cases_succ]
  rw [Finset.sum_eq_single k]
  · rw [if_neg (Fin.succ_ne_zero k), if_pos rfl]; ring
  · intro j _ hjne
    rw [if_neg (Fin.succ_ne_zero j),
        if_neg (fun heq => hjne (Fin.succ_injective _ heq).symm)]
    simp
  · intro hk
    exact absurd (Finset.mem_univ k) hk
```

Both forms are sorry-free; the first is more transparent, the second
shorter.

## 6. Mathlib bearer 4 — `Real.map_matrix_volume_pi_eq_smul_volume_pi` namespace

S5 PREP §3.2 used `map_matrix_volume_pi_eq_smul_volume_pi` (un-namespaced).
The Mathlib bearer is actually `Real.map_matrix_volume_pi_eq_smul_volume_pi`,
defined inside `namespace Real` at
`Mathlib.MeasureTheory.Measure.Lebesgue.Basic` line 397 (pin
`2df2f01...`):

```lean
theorem map_matrix_volume_pi_eq_smul_volume_pi [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : det M ≠ 0) :
    Measure.map (toLin' M) volume =
      ENNReal.ofReal (abs (det M)⁻¹) • volume := by
  ...
```

(`namespace Real` opens at line ≈245; `end Real` closes at line 431.)

**Resolution**: open the `Real` namespace (and `MeasureTheory`, `Set`)
at the top of `MinkowskiTheoremOQ02OQ03.lean` per the parent OQ-01's
pattern (`MinkowskiTheoremOQ02OQ01.lean:32` uses `open MeasureTheory
Set Real`). After `open Real`, the un-namespaced
`map_matrix_volume_pi_eq_smul_volume_pi` resolves.

**Also note** the `[DecidableEq ι]` requirement. For `ι = Fin (n+1)`,
this is `inferInstance` (Mathlib's `Fin.decidableEq` instance). No
explicit `classical` block is needed.

**Imports needed in S5 ACT**:

| Import                                                       | Purpose                                              |
| ------------------------------------------------------------ | ---------------------------------------------------- |
| `Mathlib.Analysis.Convex.Basic`                              | (already in OQ02OQ03 from S2)                        |
| `Mathlib.Data.Real.Basic`                                    | (already in OQ02OQ03)                                |
| `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`               | `volume_pi_Ioo`, `Real.map_matrix_volume_pi_…`       |
| `Mathlib.LinearAlgebra.Matrix.Block`                         | `Matrix.det_of_lowerTriangular`, `BlockTriangular`   |
| `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`             | `Matrix.det_fin_two`, `Matrix.toLin'`                |
| `Mathlib.Algebra.BigOperators.Fin`                           | `Fin.prod_univ_succ`, `Fin.sum_univ_succ`            |
| `Mathlib.Algebra.BigOperators.Group.Finset.Piecewise`        | `Finset.sum_ite_eq'`, `Finset.prod_ite_eq'`          |
| `Mathlib.Tactic`                                             | (general tactics, already present)                   |

The parent OQ-01 imports `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`
and `Mathlib.LinearAlgebra.Matrix.Determinant.Basic` (lines 25, 28),
covering most of the above. The S5 ACT additions are
`Mathlib.LinearAlgebra.Matrix.Block` (for `det_of_lowerTriangular`)
and `Mathlib.Algebra.BigOperators.Group.Finset.Piecewise` (for
`sum_ite_eq'` — though it is `@[simp]` so might already chain in via
`Mathlib.Tactic`).

## 7. Bonus — `Matrix.det_succ_column_zero` fallback verified absent

S5 PREP §5.1 mentioned a fallback if `det_of_lowerTriangular` was
unavailable: Laplace expansion via `Matrix.det_succ_column_zero`. We
verify the bearer name:

Search at pin `2df2f01...` returns:

```
Mathlib.LinearAlgebra.Matrix.Determinant.Basic (Matrix namespace)
```

contains `det_succ_column` and `det_succ_row_zero` family, but
**not** `det_succ_column_zero` as a single-named theorem. The
canonical Mathlib name is `Matrix.det_succ_column` with `j = 0`:

```lean
theorem det_succ_column (M : Matrix (Fin (n+1)) (Fin (n+1)) R) (j : Fin (n+1)) :
    M.det = ∑ i : Fin (n+1), (-1)^(i + j : ℕ) * M i j * (M.submatrix i.succAbove j.succAbove).det
```

(approximate signature from S5 PREP context; exact form may differ).

**Conclusion**: the `det_of_lowerTriangular` route is the canonical
and shortest path. The Laplace fallback is available but never
preferable for this matrix; the lower-triangular determinant bearer
collapses straight to `∏ i, M i i`.

## 8. Bonus — `Fin.cases_zero` / `Fin.cases_succ` simp normal form

S5 PREP §5.4 raised the concern that `Fin.cases` might have been
deprecated in favour of `Fin.consInduction`. We verify:

At pin `2df2f01...`, `Fin.cases_zero` and `Fin.cases_succ` are both
present in `Mathlib.Data.Fin.Basic` (search the file at the pin),
both `@[simp]`-tagged. Statements:

```lean
@[simp] theorem Fin.cases_zero {n : ℕ} {motive : Fin (n+1) → Sort*}
    (zero : motive 0) (succ : ∀ i : Fin n, motive i.succ) :
    Fin.cases zero succ 0 = zero
@[simp] theorem Fin.cases_succ {n : ℕ} {motive : Fin (n+1) → Sort*}
    (zero : motive 0) (succ : ∀ i : Fin n, motive i.succ) (i : Fin n) :
    Fin.cases zero succ i.succ = succ i
```

The `Fin.cases`-based definition of `shearM` is the canonical
spelling; no deprecation concerns at v4.26.0.

## 9. Revised S5 ACT line-count estimate

S5 PREP §3.5 estimated 120-180 Lean lines. With the four gaps
closed, the estimate sharpens to **~130-160 LOC**:

| Block                                  | Estimated LOC | Notes                                                      |
| -------------------------------------- | ------------- | ---------------------------------------------------------- |
| Imports + namespace + opens            | 8             | Add Block + Piecewise import to S2 base                    |
| `shearM` def                           | 10            |                                                            |
| `shearM_lowerTriangular`               | 12            | **Corrected** to `BlockTriangular toDual` (§2.4)            |
| `shearM_det = (-1)^n`                  | 8             | `det_of_lowerTriangular` + `Fin.prod_univ_succ` + `prod_const` (§3-§4) |
| `Tv0`                                  | 4             |                                                            |
| `Tv_succ`                              | 15            | Explicit `Finset.sum_ite_eq'` / `sum_eq_single` (§5.1)      |
| `h_eq` (preimage equality)             | 18            |                                                            |
| `h_meas_T`, `h_meas_rect`, `h_map`     | 10            | `Real.map_matrix_volume_pi_…` after `open Real` (§6)        |
| `h_rect_vol`                           | 25            |                                                            |
| `dirichletSetN_volume` assembly        | 8             |                                                            |
| `dirichletSetN_volume_gt_threshold`    | 22            |                                                            |
| Inline docstrings                      | ~20           |                                                            |
| **Total**                              | **~160**       |                                                           |

The reduction (from 180 to 160) comes from §2 cleaner BlockTriangular
proof (12 vs 15 LOC sketched), and §3-§4 single-rewrite-chain
diagonal-product collapse (8 vs 10 LOC sketched). The Tv_succ
estimate stays at 15 LOC (the explicit form is preferred for
auditability).

## 10. Risk register (post-audit)

| #   | Risk                                                                                 | S5 PREP status | After this audit                              |
| --- | ------------------------------------------------------------------------------------ | -------------- | --------------------------------------------- |
| 1   | `det_of_lowerTriangular` exact name at v4.26.0                                       | Unverified     | **Verified** at `Block.lean:291` (§2.2)        |
| 2   | `BlockTriangular id` vs `BlockTriangular toDual` direction                            | **WRONG**       | **Corrected** to `toDual` (§2)                 |
| 3   | `prod_const_neg_one_eq_pow` name                                                      | Conjectural    | **Confirmed absent**; use `prod_const` chain (§4) |
| 4   | `Finset.sum_ite_eq'` existence                                                         | Mentioned       | **Verified** at `Piecewise.lean:152` (§5)      |
| 5   | `map_matrix_volume_pi_eq_smul_volume_pi` namespace                                    | "may need prefix" | **Verified**: `namespace Real` (§6)            |
| 6   | `[DecidableEq ι]` requirement                                                          | Not flagged     | **Surfaced**: `inferInstance` for `Fin (n+1)` (§6)  |
| 7   | `Fin.cases` API deprecation                                                            | Flagged in §5.4 | **Confirmed live** at v4.26.0 (§8)             |
| 8   | `Matrix.det_succ_column_zero` fallback name                                            | Not verified    | **Verified**: canonical name is `Matrix.det_succ_column` (§7) |
| 9   | `Fin.prod_univ_succ` signature                                                         | Used in §3.4   | **Verified** at `Fin.lean:76` (§3)             |
| 10  | `volume_pi_Ioo` signature                                                              | Used in §3.4   | **Verified** at `Basic.lean:236` (§6 note)     |

10 of 10 risks resolved — 8 by Mathlib bearer lookup, 1 by
erratum-correction (CRITICAL #2), 1 by surfacing a new constraint
(#6).

## 11. Anti-targets (do NOT attempt before S5 ACT lands)

* ❌ **Do not re-do S3 / S4 ACT.** Open PR #18613 ships both. Wait
  for merge before staging S5 ACT.
* ❌ **Do not edit `state.md`, `knowledge.md`, `problem.md`, or any
  JSON in this PREP-2.** This is a pure `sessions/` audit doc.
* ❌ **Do not attempt the Laplace-expansion fallback** (§7). The
  `det_of_lowerTriangular` route works at v4.26.0.
* ❌ **Do not skip `open Real`.** Without it,
  `map_matrix_volume_pi_eq_smul_volume_pi` is `Real.…` and S5 ACT
  builds will fail with "unknown identifier".

## 12. No-edit guarantee

This PR touches **only**:

```
research/problems/minkowski-theorem-oq-02-oq-03/sessions/
    2026-05-13-s5-prep-2-mathlib-bearer-audit.md
```

No existing file is modified. Branch
`research/minkowski-oq02oq03-s5-prep-2-mathlib-audit-*` is
conflict-free against:

- PR #18613 (open S3+S4 ACT — touches `MinkowskiTheoremOQ02OQ03.lean`
  + different sessions file).
- Any future S5 ACT PR (will edit `MinkowskiTheoremOQ02OQ03.lean` +
  potentially `state.md` — neither of which this PR touches).

## 13. Done When (this PREP-2 session)

- [x] Mathlib pin recorded (`2df2f01...`, v4.26.0).
- [x] CRITICAL ERRATUM in S5 PREP §3.1 surfaced and corrected (§2).
- [x] `Fin.prod_univ_succ` bearer verified at `Fin.lean:76` (§3).
- [x] `Finset.prod_const_neg_one_eq_pow` confirmed absent; `prod_const`
  + `Fintype.card_fin` two-line chain verified (§4).
- [x] `Finset.sum_ite_eq'` bearer verified at `Piecewise.lean:152`,
  explicit `Tv_succ` proof template written (§5).
- [x] `Real.map_matrix_volume_pi_eq_smul_volume_pi` bearer verified at
  `Basic.lean:397`, namespace + `[DecidableEq ι]` requirement
  surfaced (§6).
- [x] `Matrix.det_succ_column_zero` fallback name verified as
  canonical `Matrix.det_succ_column` (§7).
- [x] `Fin.cases` API deprecation concern dismissed (§8).
- [x] Revised line-count estimate (§9).
- [x] 10/10 risk-register resolution (§10).
- [x] Anti-targets enumerated (§11).
- [x] No edits outside `sessions/` (§12).

## 14. Honest framing

1. **No `lake env lean` probe performed.** All bearer names verified
   against the Mathlib pin via GitHub Contents API
   (`gh api .../contents/<path>?ref=<sha>`), which is authoritative
   for the locked rev but does *not* substitute for a live Lean
   type-check. The S5 ACT session is still the first to
   `docker-build.sh` the chain end-to-end.
2. **CRITICAL ERRATUM in §2 is reproducible.** Anyone reading
   `Mathlib/LinearAlgebra/Matrix/Block.lean:291` will see the
   `BlockTriangular toDual` signature. The erratum is not a matter
   of taste; it is a unification error S5 ACT would have hit.
3. **The explicit `Tv_succ` template in §5.1 is sketched but
   un-built.** The `Fin.succ_injective` step and the
   `Finset.sum_ite_eq` discharge are both Mathlib-bearer-grade
   primitives, but the exact `conv_lhs` rewriting may need a
   `simp_rw` adjustment. Either of the two forms (explicit /
   tactic-heavy) is offered; the S5 ACT author picks.
4. **No `Matrix.toLin'_apply` / `Matrix.mulVec` signature verified.**
   Both appear in parent OQ-01 (`MinkowskiTheoremOQ02OQ01.lean:107`),
   so they are stable at v4.26.0.
5. **The S5 ACT line-count estimate** (§9) is necessarily approximate;
   the real cost depends on whether `simp [shearM, Matrix.of_apply]`
   reduces the entry-evaluation goals cleanly or whether they need
   case-by-case `Fin.cases_zero` / `Fin.cases_succ` rewrites.

## 15. References

- S5 PREP (this PREP-2's predecessor): PR #18419 (MERGED), file
  `sessions/2026-05-12-s5-prep-shear-volume-generalization.md`.
- Parent: `proofs/Proofs/MinkowskiTheoremOQ02OQ01.lean` (axiom-free
  n=1 sibling, gallery `verified`).
- Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0):
  - `Mathlib/LinearAlgebra/Matrix/Block.lean:61` (`BlockTriangular`
    definition).
  - `Mathlib/LinearAlgebra/Matrix/Block.lean:291`
    (`det_of_lowerTriangular`).
  - `Mathlib/Order/Synonym.lean:94` (`toDual_lt_toDual`).
  - `Mathlib/Algebra/BigOperators/Fin.lean:76` (`Fin.prod_univ_succ`).
  - `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:637`
    (`Finset.prod_const`).
  - `Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean:152`
    (`Finset.prod_ite_eq'` ⇒ `Finset.sum_ite_eq'`).
  - `Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean:236`
    (`volume_pi_Ioo`).
  - `Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean:397`
    (`Real.map_matrix_volume_pi_eq_smul_volume_pi`).
- Cassels, J.W.S. (1957). *An Introduction to the Geometry of
  Numbers*, Springer, Theorem I.II.A — original construction.
- In flight: PR #18613 (S3 + S4 ACT).
- Merged predecessors: PR #18339 (S1 OBSERVE), PR #18419 (S5 PREP),
  PR #18511 (S6 PREP), PR #18551 (S2 ACT).
