# S5-a ACT — `shearM` def + `shearM_lowerTriangular` + `shearM_det = (-1)^n`

**Slug**: `minkowski-theorem-oq-02-oq-03`
**Phase**: ACT (Lean diff — adds 60 LOC to `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean`)
**Author**: researcher-9
**Date**: 2026-05-14
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0)
**Build**: `./proofs/scripts/docker-build.sh Proofs.MinkowskiTheoremOQ02OQ03` →
`Build completed successfully (3058 jobs)`.

## What shipped

Three new declarations at the end of `MinkowskiTheoremOQ02OQ03.lean`
(Part 5), all sorry-free and axiom-free:

| Declaration | Statement | Body LOC |
| ----------- | --------- | -------- |
| `shearM (n : ℕ) (α : Fin n → ℝ)` (def) | `Matrix (Fin (n+1)) (Fin (n+1)) ℝ` with `M 0 0 = 1`, `M k.succ 0 = α k`, `M i.succ i.succ = -1`, else `0`. | 4 |
| `shearM_lowerTriangular` (thm) | `(shearM n α).BlockTriangular toDual` | 9 |
| `shearM_det` (thm) | `(shearM n α).det = (-1)^n` | 10 |

File grows 189 → 252 LOC; `axiomCount`, `sorryCount` remain at 0.

## How it generalises parent OQ-01

`MinkowskiTheoremOQ02OQ01.lean:91-94` defines a 2×2 shear via
`!![1, 0; α, -1]` and discharges its det via `Matrix.det_fin_two`.
For arbitrary `n`, the matrix-literal syntax does not extend, so we
build the matrix via `Matrix.of fun i j => …` with a nested `if`:
column-0 row 0 → `1`, column-0 row `succ k` → `α k`, diagonal entries
on rows `> 0` → `-1`, all else `0`.

The 2×2 case `n = 1` recovers
```
( 1  0)
(α₀ -1)
```
with `det = -1 = (-1)^1`. ✓

## Proof structure (S5 PREP-2 templates)

This patch implements S5 PREP-2 §2.4 (corrected `BlockTriangular toDual`
template) and §3 + §4 (det-collapse via `Fin.prod_univ_succ` + diagonal
constant-product). All Mathlib bearers were pre-verified at the locked
pin by S5 PREP-2:

- `Matrix.BlockTriangular`, `Matrix.det_of_lowerTriangular` —
  `Mathlib.LinearAlgebra.Matrix.Block` (lines 61, 291).
- `OrderDual.toDual`, `OrderDual.toDual_lt_toDual` —
  `Mathlib.Order.Synonym` (line 94).
- `Fin.prod_univ_succ` — `Mathlib.Algebra.BigOperators.Fin` (line 76).
- `Finset.prod_const`, `Finset.card_univ`, `Fintype.card_fin` —
  canonical idiom (replaces conjectural `prod_const_neg_one_eq_pow`,
  per S5 PREP-2 §4).

The S5 PREP-2 corrected template (§2.4) discharges
`shearM_lowerTriangular` in 9 LOC via `by_cases hj0 : j = 0` /
`by_cases hij_eq : i = j` after `rw [toDual_lt_toDual]` flips the
hypothesis from `toDual j < toDual i` to `i < j`. Both subcases of the
inner `by_cases` close by `absurd`; the residual `i ≠ j ∧ j ≠ 0` case
closes by `simp [hj0, hij_eq]` after `Matrix.of_apply` unwraps the
matrix-of builder. The S5 PREP §3.1 mis-direction (`BlockTriangular id`)
is the one that S5 PREP-2 erratum §2 caught; we use the correct
`BlockTriangular toDual` from the start, so no rework was needed.

`shearM_det` discharges via the chain

```
rw [Matrix.det_of_lowerTriangular …]                   -- det → diagonal product
rw [Fin.prod_univ_succ]                                -- split off i = 0
-- diagonal entries: M 0 0 = 1, M k.succ k.succ = -1
rw [h00, one_mul]; simp_rw [hkk]                        -- product is ∏_{k:Fin n} (-1)
rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]  -- constant product → (-1)^n
```

The two pointwise helpers `h00 : (shearM n α) 0 0 = 1` and
`hkk : ∀ k, (shearM n α) k.succ k.succ = -1` each close by
`simp [shearM, Matrix.of_apply, ...]` (one with `Fin.succ_ne_zero` to
defeat the outer `if`).

## Imports added

| Import | Used for |
| ------ | -------- |
| `Mathlib.LinearAlgebra.Matrix.Block` | `BlockTriangular`, `Matrix.det_of_lowerTriangular` |
| `Mathlib.LinearAlgebra.Matrix.Determinant.Basic` | `Matrix.det` |
| `Mathlib.Algebra.BigOperators.Fin` | `Fin.prod_univ_succ` |

`open OrderDual` is added at the top of the namespace to bring
`toDual` and `toDual_lt_toDual` into scope.

## Position vs in-flight PR #18967

PR #18967 is an open STATE-SYNC (state.md + JSON only, no Lean).
This patch touches **only** `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean`
and adds a new session note — no overlap with #18967's diff. If
#18967 lands first, this patch rebases cleanly; if this patch lands
first, #18967 still rebases cleanly because state.md / JSON do not
mention `shearM*` yet.

## Remaining S5 work after this PR

Per the S5 PREP roadmap (PR #18419) + S5 PREP-2 audit (PR #18622),
two further chunks remain before `dirichletSetN_volume` (S5 final)
lands:

- **S5-b** (`Tv0` + `Tv_succ` evaluation lemmas, ~50 LOC): per-row
  evaluation of `(shearM n α).toLin' v i` showing
  `Tv0 v = v 0` and `Tv_succ v k = α k * v 0 - v k.succ`. S5 PREP-2
  §5.1 provides an explicit ~15-line template via `Fin.sum_univ_succ`
  + `Finset.sum_ite_eq'` (also `Finset.sum_eq_single` form).
- **S5-c** (image-as-rectangle + volume chain, ~80 LOC):
  `(shearM n α).toLin' '' dirichletSetN n α Q =
  Ioo (-(Qⁿ+1)) (Qⁿ+1) ×ˢ ⋂ᵢ Ioo (-1/Q) (1/Q)` plus
  `Real.map_matrix_volume_pi_eq_smul_volume_pi` (open `Real` first).
  Yields `volume (dirichletSetN n α Q) = 2^(n+1) (Qⁿ+1) / Qⁿ`.

This S5-a discharge unblocks S5-b / S5-c because the det identity is
the precondition for the determinant-flip in
`map_matrix_volume_pi_eq_smul_volume_pi` (which requires `det ≠ 0`).

## Honest scope

- **Lean changes only on `MinkowskiTheoremOQ02OQ03.lean`**: +63 LOC
  (60 LOC body + 3 LOC imports + `open OrderDual`).
- **No edits** to `state.md` (in flight via #18967), `knowledge.md`,
  `problem.md`, gallery JSON, or meta.json — `axiomCount=0` /
  `sorryCount=0` already accurate; `lineCount` will drift +63 but
  PR-time auditor refresh covers that.
- **No** `loom:review-requested` label (math-agent policy).
- **Single Docker build**, succeeded on first attempt. Templates from
  S5 PREP-2 §2.4 / §3 / §4 were correct as written; no template
  corrections needed.

## Race notes

Pre-claim race-check (T-2 min, 02:50 UTC): `gh pr list -R
rjwalters/lean-genius --search "minkowski-theorem-oq-02-oq-03
in:title" --state open` → 1 open PR (#18967, STATE-SYNC only,
non-overlapping). `git fetch + switch -c <topic> origin/main`
performed before any Lean reads, so the worktree was fully rebased
to `origin/main` at HEAD before this work.
