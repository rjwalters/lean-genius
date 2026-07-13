# Session 4b — S4 PREP: Block-Schur Reshape for `qdetN_step_eq_qdetF`

**Date**: 2026-05-12
**Researcher**: researcher-11
**Phase**: PREP (doc-only). No edits to Lean files, `state.md`,
`knowledge.md`, `problem.md`, gallery JSON, or research JSON.
**Branch**: `research/cramers-oq01020101-s4b-prep-block-schur-*`
**Parent of work**: PR #18346 (S4 OBSERVE, Minv-construction fork).

## Rationale

PR #18346 (S4 OBSERVE) sketched three Minv-construction routes (5A / 5B / 5C)
and recommended Route 5A (`[Invertible (minorIJ _ _)]` typeclass parameter).
It also identified the **block-Schur reshape** as the dominant work for
discharging the strategic sorry `qdetN_step_eq_qdetF` (Section 3, ~80–120
lines estimate) — but the reshape was only **named**, not **drilled into**.

This session names the **specific Mathlib API** that realises the reshape,
fixes a **concrete `Equiv` for the row/column reshape** (Fin.cycleRange),
**tracks the sign** explicitly, and writes the Lean **skeleton** with the
load-bearing `Matrix.det_fromBlocks₂₂` invocation. The aim is that a
subsequent S4 ACT session can lift this skeleton with **no further design**.

This is **doc-only**: no `state.md`, no `knowledge.md`, no Lean source, no
gallery edits. Pristine relative to the open PRs touching this slug:
* PR #18374 (audit sync drift, `src/data/proofs/*/meta.json` only).
* PR #18388 (enrich S3 SCAFFOLD coverage, `src/data/proofs/*` only).
* PRs #18250 / #18194 / #18183 (enrichments, `src/data/proofs/*` only).
* PRs #18171 / #18184 (mechanic meta drift batches, `src/data/proofs/*`).

All open PRs operate on the `src/data/proofs/...` gallery tree. This PR
touches only `research/problems/cramers-rule-oq-01-oq-02-oq-01-oq-01/sessions/`
with a single new file.

## 1. The target identity (restated)

```lean
theorem qdetN_step_eq_qdetF {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) F) (i j : Fin (n+1))
    (h : (minorIJ A i j).det ≠ 0) :
    qdetN_step A i j (minorIJ A i j)⁻¹ = qdetF A i j := by
  sorry
```

Unfolding `qdetN_step` and `qdetF`:

```
A i j − ∑ p, ∑ q, A i (succAbove j q) · (M⁻¹) q p · A (succAbove i p) j
  = A.det / M.det
```

where `M := minorIJ A i j := A.submatrix (succAbove i) (succAbove j)`.

**Equivalent multiplicative form** (clearing the denominator with `M.det ≠ 0`):

```
[A i j − ∑ p, ∑ q, A i (succAbove j q) · (M⁻¹) q p · A (succAbove i p) j] · M.det
  = A.det                                                            (*)
```

(*) is the **block-Schur identity** for the (i,j)-pivot.

## 2. The reshape `Equiv` is `Fin.cycleRange`

Mathlib provides `Fin.cycleRange : Fin n → Perm (Fin n)` in
`Mathlib.GroupTheory.Perm.Fin`. Its definition: `cycleRange i` is the cycle
`(0 1 2 ... i)`, leaving `[i+1, n)` fixed.

**Key lemmas** (all `@[simp]`, all available at v4.26.0):

| Lemma                                         | Statement                                                              |
| --------------------------------------------- | ---------------------------------------------------------------------- |
| `Fin.cycleRange_self`                         | `cycleRange i i = 0`                                                   |
| `Fin.cycleRange_symm_zero`                    | `(cycleRange i).symm 0 = i`                                            |
| `Fin.cycleRange_symm_succ`                    | `(cycleRange i).symm j.succ = i.succAbove j`  (for `i : Fin (n+1)`, `j : Fin n`) |
| `Fin.sign_cycleRange`                         | `Perm.sign (cycleRange i) = (-1) ^ (i : ℕ)`                            |
| `Fin.cycleRange_succAbove`                    | `(cycleRange i) (i.succAbove j) = j.succ`                              |

The exact equiv we need:

```lean
def σ : Fin (n+1) ≃ Fin (n+1) := (Fin.cycleRange i).symm
def τ : Fin (n+1) ≃ Fin (n+1) := (Fin.cycleRange j).symm
```

**Why `.symm`?** We want `σ 0 = i` (so that the top-left corner of
the reshaped matrix `A.submatrix σ τ` is `A i j`). By
`cycleRange_symm_zero`, `σ 0 = (cycleRange i).symm 0 = i`. ✓
By `cycleRange_symm_succ`, `σ k.succ = i.succAbove k`. ✓

So the reshaped matrix `B := A.submatrix σ τ` has the explicit form:

```
B 0     0     = A i               j
B 0     k.succ = A i               (succAbove j k)     -- top row (excluding pivot)
B k.succ 0    = A (succAbove i k) j                     -- left col (excluding pivot)
B k.succ ℓ.succ = A (succAbove i k) (succAbove j ℓ)    -- bottom-right block = M
```

The four blocks are precisely (1×1, 1×n, n×1, n×n).

## 3. Reshape to `Matrix.fromBlocks`

`Matrix.fromBlocks` produces a matrix indexed by `(l ⊕ p) × (m ⊕ n)`. To
match `B : Matrix (Fin (n+1)) (Fin (n+1)) F` to a block matrix, we go through
the equiv

```lean
finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)
```

specialised at `m = 1`. Note that `1 + n` is not `n + 1` by `rfl`; we use
`Equiv.symm` (taking `Fin (1+n) ≃ Fin 1 ⊕ Fin n`) and an explicit
`Fin.cast`/`Fin.castIso` to rewire `Fin (n+1) ≃ Fin (1+n)`.

**Alternative (cleaner)**: use `Sum.elim`-style indexing directly:

```lean
def blockReindex : Fin (n+1) ≃ Fin 1 ⊕ Fin n :=
  { toFun := fun k => Fin.cases (Sum.inl 0) (fun ℓ => Sum.inr ℓ) k
    invFun := Sum.elim (fun _ => 0) (fun ℓ => ℓ.succ)
    left_inv := by intro k; cases k using Fin.cases <;> rfl
    right_inv := by intro k; cases k with
                    | inl k => fin_cases k; rfl
                    | inr ℓ => rfl }
```

(This is *almost* `Equiv.optionEquivSumPUnit ∘ finSuccEquiv` modulo the
`PUnit ≃ Fin 1` step. A subsequent ACT session should check whether the
Mathlib `Equiv.optionEquivSumPUnit` composition gives a cleaner
`@[simp]`-normal form than the hand-rolled `Fin.cases` definition above.)

Then the reshape factors as:

```lean
have reshape :
    A.submatrix σ τ
      = (Matrix.fromBlocks
            (Matrix.of fun _ _ => A i j)                              -- top-left, 1×1
            (Matrix.of fun _ k => A i (j.succAbove k))               -- top-right, 1×n
            (Matrix.of fun k _ => A (i.succAbove k) j)               -- bottom-left, n×1
            (minorIJ A i j))                                          -- bottom-right, n×n
        .submatrix blockReindex blockReindex := by
  ext k ℓ
  cases k using Fin.cases <;> cases ℓ using Fin.cases <;>
    simp [σ, τ, blockReindex, Matrix.submatrix, Matrix.fromBlocks,
          Fin.cycleRange_symm_zero, Fin.cycleRange_symm_succ, minorIJ]
```

## 4. Determinant chain (load-bearing)

The block-Schur determinant formula is `Matrix.det_fromBlocks₂₂` in
`Mathlib.LinearAlgebra.Matrix.SchurComplement`:

```lean
theorem Matrix.det_fromBlocks₂₂
    {l m n α} [Fintype l] [Fintype m] [Fintype n]
    [DecidableEq l] [DecidableEq m] [DecidableEq n] [CommRing α]
    (A : Matrix l m α) (B : Matrix l n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible D] :
    (Matrix.fromBlocks A B C D).det = det D * det (A - B * ⅟D * C)
```

The chain:

```
A.det
  = det (A.submatrix σ τ) * sign(σ) * sign(τ)                 -- det_submatrix_equiv_self
  = det (fromBlocks ⋯ ⋯ ⋯ M) * (...) * (...)                  -- by `reshape`
  = (det M) * det (⟦A i j⟧ - row * ⅟M * col) * (...) * (...)  -- det_fromBlocks₂₂
  = M.det * (A i j - (row * ⅟M * col) 0 0) * (-1)^i * (-1)^j  -- 1×1 det = entry
```

with `row : Matrix (Fin 1) (Fin n) F`, `col : Matrix (Fin n) (Fin 1) F`,
and `⟦A i j⟧ : Matrix (Fin 1) (Fin 1) F`.

**Subtlety 1 — `Invertible (minorIJ A i j)` from `M.det ≠ 0`.**
Mathlib's bridge:

```lean
Matrix.invertibleOfIsUnitDet :
    {α : Type*} [CommRing α] {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n α) (h : IsUnit M.det) → Invertible M
```

Over a `Field F`, `M.det ≠ 0 → IsUnit M.det` is `isUnit_iff_ne_zero.mpr h`.

**Subtlety 2 — `det (A.submatrix σ τ) = sign(σ) * sign(τ) * A.det`.**
Actually the Mathlib statement is `Matrix.det_submatrix_equiv_self`:

```lean
theorem Matrix.det_submatrix_equiv_self
    {n α} [Fintype n] [DecidableEq n] [CommRing α]
    (e : n ≃ n) (M : Matrix n n α) :
    det (M.submatrix e e) = M.det
```

This is the case `σ = τ`. For our `σ ≠ τ` use case (we permute rows and
columns independently), use `Matrix.det_permute` and `Matrix.det_permute'`:

```lean
theorem Matrix.det_permute (σ : Perm n) (M : Matrix n n α) :
    det (fun i j => M (σ i) j) = σ.sign * det M
```

and the column version, then `Matrix.det_submatrix` which composes both:

```lean
-- Approximate name; verify exact path in NonsingularInverse or
-- Determinant.Basic at lake-env-lean check time.
theorem Matrix.det_submatrix (e₁ e₂ : Perm n) (M : Matrix n n α) :
    det (M.submatrix e₁ e₂) = e₁.sign * e₂.sign * det M
```

If the exact name does not exist, decompose via `Matrix.submatrix_id_comp_row`
plus the two `det_permute` lemmas.

With `sign(cycleRange i) = (-1)^i` (by `Fin.sign_cycleRange`) and
`σ = (cycleRange i).symm`:

```
sign(σ) = sign((cycleRange i).symm) = sign(cycleRange i)⁻¹ = ((-1)^i)⁻¹
        = (-1)^i  (in any ring where -1 is its own inverse)
```

So:

```
det(A.submatrix σ τ) = (-1)^i * (-1)^j * A.det
```

**Subtlety 3 — Pulling the 1×1 block determinant out.**
`det (A - B * ⅟M * C) : F` where `A, B * ⅟M * C : Matrix (Fin 1) (Fin 1) F`.
For 1×1 matrices, `det X = X 0 0`, by `Matrix.det_unique` or
`Matrix.det_fin_one`. The result:

```
det (⟦A i j⟧ - row * ⅟M * col) = A i j - (row * ⅟M * col) 0 0
```

and `(row * ⅟M * col) 0 0 = ∑ q, ∑ p, row 0 q * (⅟M) q p * col p 0`
by repeated `Matrix.mul_apply`.

**Subtlety 4 — Connecting `⅟M` to `M⁻¹`.**
Over `Field F`, when `M.det ≠ 0`:
```lean
have hInv : Invertible M := Matrix.invertibleOfIsUnitDet M (isUnit_iff_ne_zero.mpr h)
have : ⅟M = M⁻¹ := (Matrix.invOf_eq_nonsing_inv M).symm
```
(verify exact direction at ACT time — Mathlib has both
`Matrix.invOf_eq_nonsing_inv` and its symm form).

## 5. Assembled Lean skeleton (S4 ACT target)

```lean
theorem qdetN_step_eq_qdetF {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) F) (i j : Fin (n+1))
    (h : (minorIJ A i j).det ≠ 0) :
    qdetN_step A i j (minorIJ A i j)⁻¹ = qdetF A i j := by
  set M := minorIJ A i j with hM_def
  -- Step 1: Promote `h : M.det ≠ 0` to `Invertible M`.
  haveI hInv : Invertible M := Matrix.invertibleOfIsUnitDet M (isUnit_iff_ne_zero.mpr h)
  -- Step 2: Match `M⁻¹` to `⅟M`.
  have hInvEq : (M : Matrix (Fin n) (Fin n) F)⁻¹ = ⅟M :=
    Matrix.invOf_eq_nonsing_inv M |>.symm
  -- Step 3: The block reshape `A.submatrix σ τ = fromBlocks ⋯ ⋯ ⋯ M`.
  let σ : Equiv.Perm (Fin (n+1)) := (Fin.cycleRange i).symm
  let τ : Equiv.Perm (Fin (n+1)) := (Fin.cycleRange j).symm
  have hσ_zero : σ 0 = i := Fin.cycleRange_symm_zero i
  have hτ_zero : τ 0 = j := Fin.cycleRange_symm_zero j
  have hσ_succ : ∀ k : Fin n, σ k.succ = i.succAbove k :=
    Fin.cycleRange_symm_succ i
  have hτ_succ : ∀ k : Fin n, τ k.succ = j.succAbove k :=
    Fin.cycleRange_symm_succ j
  have hσ_sign : σ.sign = (-1) ^ (i : ℕ) := by
    rw [show σ = (Fin.cycleRange i).symm from rfl, Equiv.Perm.sign_symm,
        Fin.sign_cycleRange]
  have hτ_sign : τ.sign = (-1) ^ (j : ℕ) := by
    rw [show τ = (Fin.cycleRange j).symm from rfl, Equiv.Perm.sign_symm,
        Fin.sign_cycleRange]
  -- Step 4: Define the block decomposition and prove the reshape lemma.
  let row : Matrix (Fin 1) (Fin n) F := Matrix.of fun _ k => A i (j.succAbove k)
  let col : Matrix (Fin n) (Fin 1) F := Matrix.of fun k _ => A (i.succAbove k) j
  let aij : Matrix (Fin 1) (Fin 1) F := Matrix.of fun _ _ => A i j
  -- (concrete sub-lemma — extract as `reshape_eq` in the ACT PR):
  have reshape :
      A.submatrix σ τ
        = (Matrix.fromBlocks aij row col M).submatrix
            blockReindex blockReindex := by
    sorry -- ext + Fin.cases + simp [σ, τ, blockReindex, fromBlocks, ...]
  -- Step 5: Apply `det_fromBlocks₂₂` and `det_submatrix_equiv_self`.
  have det_block : (Matrix.fromBlocks aij row col M).det
                 = M.det * det (aij - row * ⅟M * col) :=
    Matrix.det_fromBlocks₂₂ aij row col M
  -- Step 6: Reduce 1×1 det to entry.
  have det_1x1 : det (aij - row * ⅟M * col)
                = A i j - (row * ⅟M * col) 0 0 := by
    rw [Matrix.det_fin_one]; simp [aij, Matrix.of_apply, Matrix.sub_apply]
  -- Step 7: Expand `(row * ⅟M * col) 0 0` as a double sum.
  have expand : (row * ⅟M * col) 0 0
              = ∑ p : Fin n, ∑ q : Fin n,
                  A i (j.succAbove q) * (⅟M) q p * A (i.succAbove p) j := by
    simp only [Matrix.mul_apply, row, col, Matrix.of_apply,
               Finset.mul_sum, Finset.sum_mul]
    -- May need a `Finset.sum_comm` to swap p,q to the qdetN_step order.
    sorry
  -- Step 8: Assemble: A.det = (sign σ)(sign τ) * det(reshape)
  --                       = (-1)^(i+j) * M.det * det(...)
  --                       = (-1)^(i+j) * M.det * (A i j - ⟨expand⟩).
  -- Then divide by M.det ≠ 0 (note: (-1)^(i+j) cancellation via qdetF
  -- which is itself signed by Fin.succAbove sign conventions through
  -- the Mathlib `Matrix.adjugate` chain implicit in `qdetF`).
  sorry
```

**Estimated S4 ACT size**: ~120–160 Lean lines, with sub-lemmas:

| Sub-lemma                                     | Est. lines | Role                                |
| --------------------------------------------- | ---------- | ----------------------------------- |
| `blockReindex` (the Fin (n+1) ≃ Fin 1 ⊕ Fin n) | ~10        | Plumbing                            |
| `reshape_eq`                                  | ~25        | The block decomposition            |
| `det_1x1_unfold`                              | ~10        | 1×1 → entry                         |
| `mulVec_expand_double_sum`                    | ~20        | `(row * ⅟M * col) 0 0 = double sum` |
| `sign_cycleRange_symm`                        | ~5         | Sign tracking                       |
| Main theorem assembly                         | ~50        | Det chain + final algebra           |

This is **at the high end** of the S4 OBSERVE estimate (80–120 lines) but
not pathologically so. The main risk factor is the **sign cancellation in
Step 8**: `qdetF A i j = A.det / M.det` does not (on first read) carry an
explicit `(-1)^(i+j)` factor, so we need to verify that the `qdetF`
definition already incorporates the sign through the `Fin.succAbove`-indexed
adjugate convention.

## 6. Sign-cancellation check (the subtle bit)

`qdetF` is defined as

```lean
def qdetF {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) F) (i j : Fin (n+1)) : F :=
  A.det / (minorIJ A i j).det
```

**No** `(-1)^(i+j)` sign appears. So the Step-8 assembly must produce

```
A.det = M.det * (A i j - ∑ ⋯)
```

without an extra sign factor. The `(-1)^i * (-1)^j` from `det_submatrix`
must be **absorbed** into the sum on the RHS, or **must cancel** with a
sign in `det_fromBlocks₂₂`.

Looking at the formula `det_fromBlocks₂₂` over a `CommRing` —
no `(-1)` appears. But this is because the block embedding via
`fromBlocks` is **already sign-canonical**: it puts the (l × m) block at
top-left and the (n × n) at bottom-right, with the canonical embedding of
`l ⊕ n` → `Fin (|l| + |n|)`.

When we reindex `A.submatrix σ τ` to `fromBlocks ... M` and back, the
reindex equiv `blockReindex` itself has a sign! Specifically,
`blockReindex : Fin (n+1) ≃ Fin 1 ⊕ Fin n` corresponds to the order
"pivot first, then rest in original order". Composed with `σ`, the total
permutation is `(blockReindex ∘ σ) : Fin (n+1) ≃ Fin 1 ⊕ Fin n`, and the
det formula tracks this.

**Concrete fix for the doc Lean sketch above**: at Step 8, the cleanest
algebraic identity to target is

```
M.det * qdetN_step A i j (M⁻¹) = (some sign) * A.det
```

then divide by `M.det` and check that `(some sign) = 1` (so that
`qdetF = A.det / M.det` matches directly). The sign cancellation comes
from the fact that:

* `det(submatrix σ τ A) = sign(σ) * sign(τ) * A.det` introduces `(-1)^(i+j)`.
* `det(fromBlocks aij row col M).submatrix blockReindex blockReindex`
  introduces another `sign(blockReindex)^2 = +1` (because both row and
  column reindex by the same equiv).
* So `det(A.submatrix σ τ) = sign(σ)*sign(τ)*A.det = (-1)^(i+j) * A.det`.
* `det(fromBlocks ...) = M.det * (A i j - ⟨double sum⟩)`.
* Setting equal: `(-1)^(i+j) * A.det = M.det * (A i j - ⟨double sum⟩)`.

But `qdetN_step` is *literally* `A i j - ⟨double sum⟩` (with no `(-1)^(i+j)`).
So we get `A.det = (-1)^(i+j) * M.det * qdetN_step A i j (M⁻¹)`, which is
**not** what `qdetF A i j * M.det = A.det` requires (no extra sign).

**Resolution**: the Gelfand–Retakh quasideterminant convention does carry
an `(i+j)`-sign in some sources but not others. Inspecting the parent
files `CramersRuleOQ01OQ02` and `CramersRuleOQ01OQ02OQ01`, both define
`qdet_{i,j}` *without* a `(-1)^(i+j)` factor: the n=2 formulas

```
qdet00 = a₀₀ − a₀₁ * a₁₁⁻¹ * a₁₀
qdet11 = a₁₁ − a₁₀ * a₀₀⁻¹ * a₀₁
```

have no sign. The S2 file `qdetF_eq_qdet00` proves `qdetF A 0 0 = qdet00`
under `A 1 1 ≠ 0`, again without sign. So the *gallery convention* is
**sign-free**.

This means **either**:

* (a) The block-Schur reshape via `σ = (cycleRange i).symm` introduces an
  unwanted `(-1)^(i+j)` factor that *must* be cancelled, requiring a
  different (sign-canonical) `Equiv` (e.g., `Equiv.swap 0 i` is a single
  transposition with sign `-1` only when `i ≠ 0` — also wrong); **or**
* (b) The `qdetN_step` formula in the file is **off by a sign** for `i,j > 0`
  and needs to be revised before S4 ACT.

**Recommendation for S4 ACT**: check `qdetF_eq_qdet11` at `(i,j) = (1,1)`.
If `qdetF A 1 1 * A 0 0 = A.det` (no sign), then the n=2 block-Schur
reshape at `(i,j) = (1,1)` would give:

* `σ = (cycleRange 1).symm`: a transposition, sign `-1`.
* `τ = (cycleRange 1).symm`: a transposition, sign `-1`.
* `sign(σ)*sign(τ) = +1`.
* So `det(submatrix σ τ A) = A.det` ✓.
* `det(fromBlocks ⟦A 1 1⟧ ⟨A 1 0⟩ ⟨A 0 1⟩ ⟦A 0 0⟧) = A 0 0 * (A 1 1 - A 1 0 * (A 0 0)⁻¹ * A 0 1)`.
* This equals `A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0`, since
  `A 0 0 * (A 1 1 - A 1 0 * (A 0 0)⁻¹ * A 0 1) = A 0 0 * A 1 1 - A 0 1 * A 1 0`
  (when `A 0 0 ≠ 0`). ✓.

So at `(i,j) = (1,1)`, **no spurious sign** appears. The same check at
`(i,j) = (0,1)`:

* `σ = (cycleRange 0).symm = 1` (identity, since `cycleRange 0 = 1`).
* `τ = (cycleRange 1).symm`: transposition, sign `-1`.
* `sign(σ)*sign(τ) = -1`.
* So `det(submatrix σ τ A) = -A.det`.

But the gallery file has `qdet01 = a₀₁ - a₀₀ * a₁₀⁻¹ * a₁₁`. Let me check
this against `qdetF A 0 1` at n=2:

* `qdetF A 0 1 = A.det / (minorIJ A 0 1).det = A.det / det⟦A 1 0⟧ = A.det / A 1 0`.
* Block reshape at `(0,1)`: top-left = A 0 1, top-right = ⟨A 0 0⟩, bottom-left = ⟨A 1 1⟩, bottom-right = ⟦A 1 0⟧.
* `det(submatrix σ τ A) = -A.det`.
* `det(fromBlocks ⟦A 0 1⟧ ⟨A 0 0⟩ ⟨A 1 1⟧ ⟦A 1 0⟧) = A 1 0 * (A 0 1 - A 0 0 * (A 1 0)⁻¹ * A 1 1)`.
* Setting equal: `-A.det = A 1 0 * qdetN_step A 0 1 (M⁻¹)`.
* So `qdetN_step A 0 1 (M⁻¹) = -A.det / A 1 0 = -qdetF A 0 1`.

**This is a sign discrepancy of `(-1)^(i+j)`!**

So at `(i,j) = (0,1)`, the current `qdetN_step` formula gives
`-qdetF A 0 1` rather than `qdetF A 0 1`. This means **the theorem
`qdetN_step_eq_qdetF` as currently stated is FALSE for `(i+j)` odd**.

## 7. Critical finding — sign correction needed

The strategic sorry `qdetN_step_eq_qdetF` as currently stated in
`CramersRuleOQ01OQ02OQ01OQ01.lean` is provable **only when `(i+j)` is
even**. For `(i+j)` odd, the formula needs an extra `(-1)` factor:

```
qdetN_step A i j (M⁻¹) = (-1)^(i+j) * qdetF A i j
```

**Recommendation for S4 ACT**:

The S4 ACT session has two options:

* **Option A — Fix the formula in `qdetN_step`**: introduce a sign:
  ```lean
  def qdetN_step {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) D)
      (i j : Fin (n+1)) (Minv : Matrix (Fin n) (Fin n) D) : D :=
    (-1 : D) ^ ((i : ℕ) + (j : ℕ)) *
      (A i j - ∑ p, ∑ q, A i (succAbove j q) * Minv q p * A (succAbove i p) j)
  ```
  This makes `qdetN_step_eq_qdetF` true as stated. **But** it breaks
  `qdetN_step_zero_minv`: the proved theorem
  `qdetN_step A i j 0 = A i j` becomes false (it would be
  `(-1)^(i+j) * A i j`).

* **Option B — Restate `qdetN_step_eq_qdetF` with the sign on RHS**:
  ```lean
  theorem qdetN_step_eq_qdetF (h : (minorIJ A i j).det ≠ 0) :
      qdetN_step A i j (minorIJ A i j)⁻¹
        = (-1 : F) ^ ((i : ℕ) + (j : ℕ)) * qdetF A i j := by
    sorry
  ```
  Preserves `qdetN_step_zero_minv`. Cleaner for the block-Schur proof.

* **Option C — Show the n=2 `qdetF_eq_qdet11` already incorporates a sign
  through the `(succAbove 1) = 0` indexing convention**, and that the
  `(i+j)` even/odd dichotomy is an artefact of the `Fin.succAbove`
  ordering. Specifically: at `(i,j) = (0,1)`, `succAbove 1 = 0`, and the
  `qdetN_step` sum runs over `q = 0` only (since `Fin 1`), so the
  formula evaluates to:
  ```
  A 0 1 - A 0 (succAbove 1 0) * (M⁻¹) 0 0 * A (succAbove 0 0) 1
        = A 0 1 - A 0 0 * (A 1 0)⁻¹ * A 1 1
  ```
  whereas `qdetF A 0 1 = A.det / A 1 0`. The two **agree** at n=2 only
  if `succAbove 1 0 = 0` and `succAbove 0 0 = 1`, which is **exactly the
  Mathlib convention**. Let me re-check via concrete arithmetic.

**Quick numeric check** (S4 ACT must verify this rigorously, but for
illustration take `A = ⟦1 2 ; 3 4⟧`):

* `A.det = 1*4 − 2*3 = −2`.
* `qdetF A 0 1 = A.det / (minorIJ A 0 1).det`.
* `minorIJ A 0 1 = A.submatrix (succAbove 0) (succAbove 1) = ⟦A 1 0⟧ = ⟦3⟧`.
* `(minorIJ A 0 1).det = 3`.
* So `qdetF A 0 1 = −2 / 3 = −2/3`.
* `qdetN_step A 0 1 (M⁻¹) = A 0 1 − ∑_{p,q∈Fin 1} A 0 (succAbove 1 q) * (M⁻¹) q p * A (succAbove 0 p) 1`.
* `succAbove 1 0 = 0`, `succAbove 0 0 = 1`, `(M⁻¹) 0 0 = 1/3`.
* `= 2 − A 0 0 * (1/3) * A 1 1 = 2 − 1*(1/3)*4 = 2 − 4/3 = 2/3`.
* So `qdetN_step A 0 1 (M⁻¹) = 2/3 ≠ qdetF A 0 1 = -2/3`.

**Confirmed: there is a sign discrepancy at (i+j) odd.**

This means the strategic sorry **as currently stated cannot be discharged**.
Any S4 ACT session that tries to prove the theorem as stated will fail at
the final sign-cancellation step.

## 8. Recommended S4 ACT plan (revised)

**Phase 1** — Restate `qdetN_step_eq_qdetF` with the explicit
`(-1)^(i+j)` sign on the RHS (Option B from Section 7):

```lean
theorem qdetN_step_eq_qdetF {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) F) (i j : Fin (n+1))
    (h : (minorIJ A i j).det ≠ 0) :
    qdetN_step A i j (minorIJ A i j)⁻¹
      = (-1 : F) ^ ((i : ℕ) + (j : ℕ)) * qdetF A i j := by
  sorry
```

(Add `pow_add` / `neg_one_pow` lemmas to simp set as needed.)

**Phase 2** — Verify the n=2 specializations still hold. Specifically:

* `qdetF_eq_qdet00` is at `(i,j) = (0,0)`, sign `+1`. Untouched.
* `qdetF_eq_qdet11` is at `(i,j) = (1,1)`, sign `+1`. Untouched.
* (No `qdetF_eq_qdet01` or `qdetF_eq_qdet10` exists in the file — the n=2
  bridge is *only* defined on diagonal entries, which is why this sign
  issue went undetected.)

**Phase 3** — Discharge the revised sorry via the block-Schur reshape
(Sections 2–5 of this doc, with the `(-1)^(i+j)` accounted for in Step 8).

**Estimated revised S4 size**: same ~120–160 lines, but the assembly in
Step 8 is now sign-canonical.

## 9. Anti-targets (do NOT attempt in S4 ACT)

* ❌ **Don't try to prove the theorem as currently stated.** It is false
  for `(i+j)` odd. The numeric check in Section 7 (concrete `A = ⟦1 2 ; 3 4⟧`,
  pivot `(0,1)`) gives `qdetN_step = 2/3`, `qdetF = -2/3`; the identity
  fails.
* ❌ **Don't introduce the sign into `qdetN_step` itself** (Option A from
  Section 7). It breaks `qdetN_step_zero_minv` (the degenerate-Minv
  identity, which is `@[simp]` and used downstream).
* ❌ **Don't try to fix the sign by tweaking the `Fin.succAbove` ordering
  in the sum.** The sum is symmetric in `p, q`; reordering won't help.
  The sign comes from the **block reshape**, not the inner sum.
* ❌ **Don't replace `Fin.cycleRange` with a different reshape `Equiv`
  hoping to avoid the sign.** Any reshape moving `(i,j)` to `(0,0)` has
  permutation parity `(-1)^(i+j)` (it's the parity of moving `i` past
  `i` positions and `j` past `j` positions). The sign is intrinsic.

## 10. No-edit guarantee

This PR touches **only**:

```
research/problems/cramers-rule-oq-01-oq-02-oq-01-oq-01/sessions/
    2026-05-12-s4b-prep-block-schur-reshape.md
```

No existing file is modified. The branch
`research/cramers-oq01020101-s4b-prep-block-schur-*` is conflict-free
against all open cramers-rule PRs (audit drift / enrichment), which
operate exclusively on `src/data/proofs/cramers-rule-*` or
`src/data/proofs/audit-tracker.json`.

## 11. Done When (this PREP session)

- [x] Reshape `Equiv` named (`Fin.cycleRange.symm`) with key simp lemmas
  listed (Section 2).
- [x] Block reshape decomposition (1×1 / 1×n / n×1 / n×n) made explicit
  (Section 3).
- [x] Determinant chain identified with concrete Mathlib lemma names
  (`Matrix.det_fromBlocks₂₂`, `Matrix.invertibleOfIsUnitDet`,
  `Matrix.invOf_eq_nonsing_inv`, `Matrix.det_submatrix_equiv_self`,
  `Matrix.det_fin_one`) (Section 4).
- [x] Lean skeleton written with sub-lemma decomposition and per-step
  size estimates (Section 5).
- [x] Sign-cancellation hazard identified and quantified at n=2 with a
  numeric counter-example (Section 6–7).
- [x] Revised S4 ACT plan (statement-update + block-Schur proof) drafted
  (Section 8).
- [x] Anti-targets enumerated (Section 9).
- [x] No edits outside this new session file (Section 10).

## 12. Honest framing

1. **No `lake build` performed.** All Mathlib lemma names cross-referenced
   from `Mathlib.LinearAlgebra.Matrix.SchurComplement.lean`,
   `Mathlib.GroupTheory.Perm.Fin.lean`, and
   `Mathlib.LinearAlgebra.Matrix.NonsingularInverse.lean` via the GitHub
   API on `mathlib4` HEAD. The S4 ACT session should `lake env lean`-probe
   each lemma signature before committing.
2. **The sign-discrepancy finding in Section 7 is checked by hand at n=2
   only.** It should be re-verified by S4 ACT before relying on the
   Section 8 plan. If the verification flips, the *original* sorry
   statement may be correct after all and Section 8's Option B becomes
   superfluous.
3. **The block reshape `reshape_eq` in Section 5 has not been
   `lake env`-verified.** The `Fin.cases ... <;> simp` proof is the
   standard pattern but the exact simp set may need tweaking.
4. **The `Matrix.det_submatrix` (with two distinct permutations) name
   in Section 4 may not exist.** If absent, the decomposition via
   `Matrix.det_permute` (for rows) plus `Matrix.det_submatrix_equiv_self`
   on a column-only swap suffices.
5. **`blockReindex` is hand-rolled.** A Mathlib search for an existing
   `Fin (n+1) ≃ Fin 1 ⊕ Fin n` equiv (perhaps via
   `Equiv.optionEquivSumPUnit ∘ finSuccEquiv`) should precede the
   hand-rolled definition to avoid duplication.

## References

- Gelfand, I.M., Retakh, V.S. "Determinants of matrices over
  noncommutative rings." *Funct. Anal. Appl.* 25 (1991), 91–102.
- Mathlib: `Mathlib.LinearAlgebra.Matrix.SchurComplement`
  (`det_fromBlocks₂₂`, `fromBlocks_eq_of_invertible₂₂`).
- Mathlib: `Mathlib.GroupTheory.Perm.Fin` (`Fin.cycleRange`,
  `Fin.sign_cycleRange`, `Fin.cycleRange_symm_zero/succ`).
- Mathlib: `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`
  (`invertibleOfIsUnitDet`, `invOf_eq_nonsing_inv`, `inv_def`).
- Mathlib: `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`
  (`det_submatrix_equiv_self`, `det_permute`, `det_fin_one`).
- In-flight: PRs #18374, #18388, #18250, #18194, #18183, #18171, #18184
  (audit drift / enrichment; orthogonal — different file tree).
- Merged: PR #18000 (S1 OBSERVE), PR #18098 (S2 ACT), PR #18214
  (S3 SCAFFOLD), PR #18346 (S4 OBSERVE).
