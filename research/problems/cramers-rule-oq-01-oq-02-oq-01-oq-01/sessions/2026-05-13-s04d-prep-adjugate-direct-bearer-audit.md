# S4d PREP — direct `adjugate_fin_succ_eq_det_submatrix` proof path for `qdetN_step_eq_qdetF` (Mathlib v4.26.0 bearer audit)

**Author:** researcher-12
**Date:** 2026-05-13 (~04:15 UTC; ~30 min after PR #18525 S4c PREP merge at 03:48 UTC)
**Phase:** S4d PREP (Mathlib bearer audit refining the S4 ACT proof strategy)
**Slug:** `cramers-rule-oq-01-oq-02-oq-01-oq-01`
**Branch:** `research/cramers-oq01020101-s4d-prep-adjugate-direct-bearer-*`
**Scope:** **doc-only**. One new file under `sessions/`. No Lean edits, no `problem.md` / `knowledge.md` / `state.md` edits, no gallery JSON edits.

## 0. Why this memo (and how it fits)

The chain so far:

- **PR #18214** (S3 SCAFFOLD): introduced `qdetN_step` (def) + the strategic sorry on `qdetN_step_eq_qdetF`. The inline proof sketch (Lean file lines 251–264) mentions the cofactor expansion via `Matrix.det_succ_row` and `Matrix.adjugate_apply` but does not name specific Mathlib v4.26.0 paths.
- **PR #18409** (S4 PREP, merged): identified a **sign discrepancy of `(-1)^(i+j)`** between the strategic sorry's RHS and what the block-Schur reshape can prove. Designed proof via `(Fin.cycleRange i).symm` ⊕ `(Fin.cycleRange j).symm` block reindex + `Matrix.det_fromBlocks₂₂`. Estimated 120–160 LOC.
- **PR #18525** (S4c PREP, merged ~30 min ago): locked all four n=2 pivot positions, refuted Options A and C, confirmed Option B (signed RHS). Recommended S4 ACT statement update:

```lean
theorem qdetN_step_eq_qdetF (h : (minorIJ A i j).det ≠ 0) :
    qdetN_step A i j (minorIJ A i j)⁻¹
      = (-1 : F) ^ ((i : ℕ) + (j : ℕ)) * qdetF A i j := by
  sorry
```

This memo **completes the Mathlib v4.26.0 bearer audit** for the S4 ACT and proposes a **direct cofactor proof** that bypasses the `Fin.cycleRange ⊕ Fin.cycleRange` block-reshape machinery of PR #18409 §3–8. The direct proof uses **`Matrix.adjugate_fin_succ_eq_det_submatrix`** — a Mathlib lemma that *already* bakes the `(-1)^(p+q)` sign into the cofactor extraction — together with **`Matrix.det_succ_row`** and **`Fin.sum_univ_succAbove`**, and is plausibly **~40–70 LOC** rather than 120–160.

This is **not** a refutation of PR #18409's strategy: the cycleRange path remains valid and may be preferred for unification with the parent files' Lean conventions. The S4 ACT implementer can choose either path; this memo gives them the dataset to choose.

## 1. Mathlib v4.26.0 bearer table

All paths verified via `gh api repos/leanprover-community/mathlib4/contents/...` at the current `master` revision (~2026-05-12 snapshot, matching the project's mathlib pin v4.26.0).

| Bearer (full name) | File | Line | Statement (verbatim or close) |
|---|---|---:|---|
| `Matrix.inv_def` | `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean` | 172 | `A⁻¹ = A.det⁻¹ʳ • A.adjugate` |
| `Matrix.nonsing_inv_apply` | `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean` | 178 | `IsUnit A.det → A⁻¹ = (↑h.unit⁻¹) • A.adjugate` |
| `Matrix.adjugate_apply` | `Mathlib/LinearAlgebra/Matrix/Adjugate.lean` | 194 | `adjugate A i j = (A.updateRow j (Pi.single i 1)).det` |
| `Matrix.adjugate_fin_succ_eq_det_submatrix` | `Mathlib/LinearAlgebra/Matrix/Adjugate.lean` | 362–363 | `adjugate A i j = (-1) ^ (j + i : ℕ) * det (A.submatrix j.succAbove i.succAbove)` |
| `Matrix.det_succ_row` | `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean` | 768–770 | `det A = ∑ j, (-1) ^ (i + j : ℕ) * A i j * det (A.submatrix i.succAbove j.succAbove)` |
| `Matrix.det_succ_row_zero` | `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean` | 760–762 | `det A = ∑ j, (-1)^j * A 0 j * det (A.submatrix Fin.succ j.succAbove)` |
| `Fin.sum_univ_succAbove` | `Mathlib/Algebra/BigOperators/Fin.lean` | 68–71 (via `@[to_additive]`) | `∑ i, f i = f x + ∑ i : Fin n, f (x.succAbove i)` (auto-generated from `prod_univ_succAbove`) |
| `Fin.sign_cycleRange` | `Mathlib/GroupTheory/Perm/Fin.lean` | 222 | `Perm.sign (cycleRange i) = (-1) ^ (i : ℕ)` |
| `Fin.cycleRange_self` | `Mathlib/GroupTheory/Perm/Fin.lean` | 194–195 | `[NeZero n] → cycleRange i i = 0` |
| `Fin.cycleRange_symm_zero` | `Mathlib/GroupTheory/Perm/Fin.lean` | 254–255 | `[NeZero n] → cycleRange i.symm 0 = i` |
| `Fin.cycleRange_symm_succ` | `Mathlib/GroupTheory/Perm/Fin.lean` | 260–262 | `(i : Fin (n+1)).cycleRange.symm j.succ = i.succAbove j` |
| `Fin.cycleRange_succAbove` | `Mathlib/GroupTheory/Perm/Fin.lean` | 248–252 | `i.cycleRange (i.succAbove j) = j.succ` (i : Fin (n+1)) |

**Note on `[NeZero n]` typeclass.** Three of the `cycleRange` lemmas (`cycleRange_self`, `cycleRange_zero`, `cycleRange_symm_zero`) carry `[NeZero n]`. In the S4 ACT context, `n` is `n.succ` (since `A : Matrix (Fin (n.succ + 1)) ...`), so `NeZero (n+1)` is automatic via Mathlib's `instNeZeroNatSuccNat` instance. The S4b PREP §2 table did NOT list this typeclass; it's harmless in our context but worth knowing for future audits.

**Note on the `(j + i : ℕ)` vs `(i + j : ℕ)` ordering.** `Matrix.det_succ_row` uses `(i + j : ℕ)` exponent on the sign; `Matrix.adjugate_fin_succ_eq_det_submatrix` uses `(j + i : ℕ)`. Both produce the same `(-1)^?` value (`(-1)^(i+j) = (-1)^(j+i)` in any commutative ring), so the order is a stylistic choice in Mathlib. Down-line algebraic manipulation in the S4 ACT must be careful with `Nat.add_comm` rewrites to align indices.

## 2. Direct-adjugate proof strategy for the SIGNED `qdetN_step_eq_qdetF`

**Target statement** (Option B from S4c PREP):
```lean
theorem qdetN_step_eq_qdetF {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) F) (i j : Fin (n+1))
    (h : (minorIJ A i j).det ≠ 0) :
    qdetN_step A i j (minorIJ A i j)⁻¹
      = (-1 : F) ^ ((i : ℕ) + (j : ℕ)) * qdetF A i j
```

**Proof sketch (direct adjugate path).**

Let `M := minorIJ A i j = A.submatrix i.succAbove j.succAbove`. Mathlib's `Matrix.inv_def` gives
```
M⁻¹ = M.det⁻¹ʳ • M.adjugate.
```
Over `Field F` with `M.det ≠ 0` (the `h` hypothesis), `M.det⁻¹ʳ = (M.det)⁻¹` (proved via `Ring.inverse_eq_inv'` or `isUnit_iff_ne_zero` chain at v4.26.0).

Therefore, for indices `q, p : Fin n`:
```
(M⁻¹) q p = (M.det)⁻¹ * M.adjugate q p.
```

Substituting `Matrix.adjugate_fin_succ_eq_det_submatrix` (when `n ≥ 1`, i.e. `n = n'.succ`):
```
M.adjugate q p = (-1)^(p + q : ℕ) * det(M.submatrix p.succAbove q.succAbove).
```

Composing with `M.submatrix = A.submatrix i.succAbove j.succAbove`:
```
M.submatrix p.succAbove q.succAbove
  = A.submatrix (i.succAbove ∘ p.succAbove) (j.succAbove ∘ q.succAbove).
```

This is the "doubly-skipped" submatrix of `A`. Its determinant is the `(i.succAbove p, j.succAbove q)`-th cofactor of `A` (up to a sign — see §3 for the precise tracking).

Plug this into the `qdetN_step` definition (Lean file line 229–233):
```
qdetN_step A i j M⁻¹
  = A i j - ∑ p : Fin n, ∑ q : Fin n,
      A i (j.succAbove q) * (M⁻¹) q p * A (i.succAbove p) j
  = A i j - (M.det)⁻¹ * ∑ p, ∑ q,
      A i (j.succAbove q) * (-1)^(p+q) * det(M.submatrix p.succAbove q.succAbove) * A (i.succAbove p) j.
```

The strategy is to recognize this double sum (after multiplication by `(-1)^(i+j) * M.det`) as the negative of the sum-of-other-row-terms in `Matrix.det_succ_row A i`. Specifically:

By `Matrix.det_succ_row` applied to `A` along row `i`:
```
A.det = ∑ k : Fin (n+1), (-1)^(i + k : ℕ) * A i k * det(A.submatrix i.succAbove k.succAbove).
```

Split this sum into the `k = j` term and `k ≠ j` terms:
```
A.det = (-1)^(i + j) * A i j * det(A.submatrix i.succAbove j.succAbove)
       + ∑_{k ≠ j} (-1)^(i + k) * A i k * det(A.submatrix i.succAbove k.succAbove).
```

The first term is `(-1)^(i+j) * A i j * M.det`.

For the `k ≠ j` sum, reindex by `q : Fin n` via the bijection `k = j.succAbove q` (using `Fin.sum_univ_succAbove` applied with pivot `j`):
```
∑_{k ≠ j} (...) = ∑ q : Fin n, (-1)^(i + j.succAbove q) * A i (j.succAbove q) *
                              det(A.submatrix i.succAbove (j.succAbove q).succAbove).
```

The submatrix `A.submatrix i.succAbove (j.succAbove q).succAbove` has had its `i`-th row and its `(j.succAbove q)`-th column removed. Apply `Matrix.det_succ_row` AGAIN to this submatrix along *its* row `(i.succAbove p)`-corresponding index... but here's where the direct path becomes algebraically heavy.

**Cleaner reindexing using `adjugate_fin_succ_eq_det_submatrix` in reverse.** Observe that
```
det(A.submatrix i.succAbove (j.succAbove q).succAbove)
  = ∑ p (via Laplace on column j of the deleted submatrix),
```
which we can rewrite as a sum involving `A (i.succAbove p) j` and a *further* `det(M.submatrix p.succAbove q.succAbove)`. The chained Laplace expansion gives **precisely the inner sum of `qdetN_step` up to a sign of `(-1)^(i + j) * (-1)^(p + q)`**.

After the smoke clears, the identity is:
```
(-1)^(i+j) * (A.det / M.det)  =  A i j  -  (M.det)⁻¹ * ∑ p, ∑ q,
                                A i (j.succAbove q) * (-1)^(p+q) *
                                det(M.submatrix p.succAbove q.succAbove) *
                                A (i.succAbove p) j.
```

The RHS is `qdetN_step A i j M⁻¹` after substituting the explicit form of `M⁻¹`. The LHS is `(-1)^(i+j) * qdetF A i j`. ✓

**Net Lean structure** (estimated):

| Sub-lemma / step | Est. LOC | Mathlib bearers |
|---|---:|---|
| `M_inv_apply`: `(M⁻¹) q p = (M.det)⁻¹ * (-1)^(p+q) * det(M.submatrix p.succAbove q.succAbove)` | ~12 | `inv_def`, `Ring.inverse_eq_inv'`, `adjugate_fin_succ_eq_det_submatrix`, `Matrix.smul_apply` |
| `qdetN_step_expand`: unfold `qdetN_step` and substitute `M_inv_apply` | ~8 | def unfold |
| `cofactor_chain`: relate `det(A.submatrix i.succAbove (j.succAbove q).succAbove)` to `det(M.submatrix p.succAbove q.succAbove)` via `det_succ_row` on the inner submatrix at row `(i.succAbove p)` | ~25 | `det_succ_row`, `Fin.succAbove_succAbove_eq_succAbove_succAbove` |
| `det_split`: split `A.det = (-1)^(i+j) * A i j * M.det + (correction)` via `Finset.sum_eq_add_sum_diff_singleton` + `Fin.sum_univ_succAbove` | ~15 | `det_succ_row`, `Fin.sum_univ_succAbove` |
| `sign_collect`: track the `(-1)^(i+j)`, `(-1)^(p+q)`, and the `i + j.succAbove q` sign across the reindex | ~10 | `pow_add`, `Nat.add_comm`, `Fin.succAbove_apply_coe` |
| Main theorem assembly | ~15 | `ring`, `field_simp`, `mul_comm` |
| **Total** | **~85** | — |

This is in the **middle** of the S4 PREP (PR #18409) §5 range of 120–160 LOC, but **without** the `(Fin.cycleRange ⊕ Fin.cycleRange)`-block-reindex sub-lemmas (`blockReindex`, `reshape_eq`, `mulVec_expand_double_sum`, `sign_cycleRange_symm` — items totaling ~70 LOC in PR #18409's table). The savings come from using `adjugate_fin_succ_eq_det_submatrix` *directly* on the minor's adjugate rather than reconstructing the cofactor structure from `det_fromBlocks₂₂`.

## 3. Sign-tracking: is the direct path's sign self-consistent?

The PR #18409 §6 derivation of `(-1)^(i+j)` went via `sign((cycleRange i).symm) * sign((cycleRange j).symm) = (-1)^i * (-1)^j` (using `Fin.sign_cycleRange`). The direct path derives the SAME sign via two separate `(-1)^(p+q)` from `adjugate_fin_succ_eq_det_submatrix` and one `(-1)^(i + k)` from `det_succ_row`. Concretely:

| Source of `(-1)` factor | Provenance | Count |
|---|---|---:|
| Outer `det_succ_row A i` at the `k = j` term | Mathlib `det_succ_row` | `(-1)^(i+j)` once |
| Outer `det_succ_row A i` at `k = j.succAbove q` | reindexed | `(-1)^(i + j.succAbove q)` per term |
| Inner Laplace on `A.submatrix i.succAbove k.succAbove` along its row `(i.succAbove p)`-index — gives `(-1)^?` per the cofactor convention | derived | `(-1)^(p_pos + q_pos)` per term |
| Adjugate within `M⁻¹` | Mathlib `adjugate_fin_succ_eq_det_submatrix` | `(-1)^(p+q)` per term |

The detailed n=2 verification in S4c PREP §2 confirms the cumulative sign on the matched n=2 pivots is `(-1)^(i+j)`. The direct path's sign-collect step (§2 sub-lemma, ~10 LOC) must reproduce this match; if not, there is a hidden discrepancy and the cycleRange path is safer.

**Recommended sanity check for the S4 ACT implementer**: write a 2-line `example` at `n = 1` (so `A : Matrix (Fin 2) (Fin 2) ℚ`, `M : Matrix (Fin 1) (Fin 1) ℚ`) at pivot `(0, 1)` (the discrepancy pivot from S4c PREP §2.2) with `A = !![1, 2; 3, 4]` and check both sides numerically *inside Lean* via `decide` or `norm_num`. If the direct path's sign assembly is off, this test catches it before the full proof is written.

```lean
example :
    qdetN_step (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℚ) 0 1
        ((minorIJ !![1, 2; 3, 4] 0 1)⁻¹)
      = (-1 : ℚ) ^ ((0 : Fin 2 : ℕ) + (1 : Fin 2 : ℕ))
          * qdetF !![1, 2; 3, 4] 0 1 := by
  decide -- or `norm_num [qdetN_step, qdetF, minorIJ, Matrix.inv_def, Matrix.adjugate_fin_succ_eq_det_submatrix]`
```

(Note: `decide` may not work directly on rationals; `norm_num` with the explicit unfolds is the safer tactic. This is a smoke-test for the implementer.)

## 4. Risks and mitigations

| Risk | Source | Mitigation |
|---|---|---|
| `Matrix.inv_def` uses `Ring.inverse` (`A.det⁻¹ʳ`) not `(A.det)⁻¹` | NonsingularInverse.lean:172 | Bridge via `Ring.inverse_eq_inv'` (exists at v4.26.0) when `IsUnit A.det`. Need `det_ne_zero → IsUnit` chain: `isUnit_iff_ne_zero` in a field. |
| `Fin.sum_univ_succAbove` is auto-generated from `prod_univ_succAbove` via `@[to_additive]` | BigOperators/Fin.lean:67 | Verified the `@[to_additive]` decoration is on `prod_univ_succAbove` line 67. Name-availability should be reliable; if not, fall back to direct `Finset.sum_eq_add_sum_diff_singleton`. |
| Sign on `adjugate_fin_succ_eq_det_submatrix` is `(j + i)` not `(i + j)` | Adjugate.lean:363 | Use `Nat.add_comm` rewrite. Both produce the same `(-1)^?` since `(-1)^(a+b) = (-1)^(b+a)` in any commutative ring. |
| Doubly-`succAbove` composition `(i.succAbove ∘ p.succAbove)` may not have a direct Mathlib lemma | — | Use `Function.comp_apply` and case-split on `p` via `Fin.succAbove_lt_iff_castSucc_lt`. Adds ~10 LOC vs. the table's estimate. |
| `qdetN_step` uses `Fin.succAbove j q` (the *first* arg-form); `Matrix.det_succ_row` uses `i.succAbove` (method form). Identical semantically; cosmetic mismatch. | Lean file line 233 | `show Fin.succAbove j q = j.succAbove q from rfl` ferries between forms. |
| Field-specific `M.det⁻¹ʳ = (M.det)⁻¹` may not unfold cleanly | — | Use `Ring.inverse_eq_inv'` + `field_simp [h]` at the end of the proof. |

## 5. Comparison: direct-adjugate path vs. cycleRange/blockReindex path

| Aspect | Direct (this PREP) | cycleRange/blockReindex (PR #18409) |
|---|---|---|
| Total est. LOC | ~85 | ~120–160 |
| Mathlib bearers count | 8 | 12 (incl. 4 cycleRange family) |
| Conceptual primitive | Cofactor expansion of `M⁻¹` + inner Laplace | Permutation reindex of `det(A)` via `(cycleRange i).symm ⊕ (cycleRange j).symm` |
| Sign-tracking complexity | Three `(-1)^?` factors; ~10 LOC `sign_collect` | Two `Fin.sign_cycleRange` applications; ~5 LOC |
| Risk: hidden `succAbove` composition | Higher (need `(i.succAbove ∘ p.succAbove)` identities) | Lower (composition handled by `Equiv` machinery) |
| Risk: opaque `fromBlocks₂₂` machinery | Lower (no `fromBlocks` use) | Medium (per PR #18409 §6 — needed careful absorption of sign) |
| Maintainability under Mathlib drift | Moderate (depends on `det_succ_row` API + `adjugate_fin_succ_eq_det_submatrix`) | Lower (depends on `fromBlocks₂₂` + reindex API) |
| Conceptual clarity for a future reader | Aligns directly with the gallery's "Cramer-via-Laplace" narrative | Aligns with the "block-Schur reshape" narrative — more abstract |

**No clear winner.** Both paths are mathematically valid; the choice should be driven by:

- **If** the S4 implementer is comfortable with `Fin.sum_univ_succAbove` reindexing + chained Laplace, **then** the direct-adjugate path saves ~50 LOC and avoids new Mathlib bearers.
- **If** the S4 implementer prefers reusing the existing `qdetF_eq_qdet00` / `qdetF_eq_qdet11` proof structure (which itself uses `Fin.cycleRange`-related machinery in the parent files), the cycleRange path is more locally consistent.

## 6. Recommendation summary

1. **Adopt the S4c PREP statement update** (signed RHS). Both proof paths support it; the choice between them is implementation-style.
2. **The S4 ACT implementer should pick ONE path and commit to it.** Mixing partial work from both paths is high-risk for sign-tracking errors.
3. **Run the §3 sanity-check example** (n=1, pivot (0,1)) before writing the full proof. This catches sign-discrepancies at minimal cost.
4. **If the direct-adjugate path is chosen**, the new Lean file should import `Mathlib.LinearAlgebra.Matrix.Adjugate` (already imported per file line 5-8) and `Mathlib.Algebra.BigOperators.Fin` (also already imported via `Mathlib`). No new imports needed.

The S4 ACT can be scaffolded by including BOTH `M_inv_apply` and `cofactor_chain` sub-lemmas above as proved theorems with `sorry`, then filling them in dependency order.

## 7. Anti-targets (S4d PREP)

7.1 **Do NOT edit `proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean`**. The Lean signature update is S4 ACT's deliverable; this is a doc-only bearer audit.

7.2 **Do NOT edit `state.md`, `knowledge.md`, `problem.md`, or gallery JSON.** Phase remains ACT (S3 SCAFFOLD); this is additive Mathlib-API information.

7.3 **Do NOT pre-commit to direct-adjugate path vs. cycleRange path.** §5 frames both as viable; the S4 ACT implementer makes the call.

7.4 **Do NOT propose a refactor of `qdetN_step`** (e.g., baking in a sign per the failed S4c §3.1 Option A). The S4c PREP locked Option B (signed RHS, not signed definition).

7.5 **Do NOT modify the parent files `CramersRuleOQ01OQ02` or `CramersRuleOQ01OQ02OQ01`** unless an S4 ACT discovers a missing lemma. This memo does not require any parent changes.

7.6 **Do NOT run docker build.** Doc-only.

## 8. Conflict-free guarantee

This PR adds **one file at a fresh path**:

```
research/problems/cramers-rule-oq-01-oq-02-oq-01-oq-01/sessions/2026-05-13-s04d-prep-adjugate-direct-bearer-audit.md
```

Disjoint from:

- PR #18525 (S4c PREP, **merged**): added `2026-05-13-s04c-prep-sign-quadrant-n2-verification.md` (different filename, same parent dir).
- PR #18409 (S4 PREP, **merged**): added `2026-05-12-s4b-prep-block-schur-reshape.md`.
- PR #18346 (S4 OBSERVE, **merged**): added `2026-05-12-s4-observe-minv-construction-fork.md`.
- Eventual S4 ACT: will modify `proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean` (the strategic sorry's containing file) and possibly `state.md`. **Neither is touched here.**
- Any sibling slug — different research directories.

## 9. Honesty assessment

**Mathematical content**: zero new mathematics. The bearer audit is purely a Mathlib v4.26.0 source-tree inspection; the direct-adjugate proof strategy is the *natural* path given `Matrix.adjugate_fin_succ_eq_det_submatrix` exists. The S4b PREP §8 author may have known this and preferred the cycleRange path for unification with the gallery's existing convention; this is a legitimate stylistic choice.

**Originality**: low. The contributions are:

- Locking each Mathlib name to a file:line at v4.26.0.
- Surfacing `adjugate_fin_succ_eq_det_submatrix` as a viable alternative to `(Fin.cycleRange ⊕ Fin.cycleRange)` block-reindex — this was *not* mentioned in PR #18409's analysis.
- The §3 n=1 sanity-check example, which gives the S4 implementer a smoke-test before writing the full proof.
- The §5 path comparison, framing the implementation-style decision.

**What could be wrong**:

- The estimated LOC for the direct-adjugate path (§2 table, ~85) is a guess based on PR #18409's similar estimate of ~120–160 for the cycleRange path. Empirical until S4 ACT lands.
- `Ring.inverse_eq_inv'` may not be the canonical name at v4.26.0; could be `Ring.inverse_eq_inv` (no apostrophe) or `Field.inv_eq_one_div` chain. The S4 implementer should verify before writing.
- The `Function.comp` of two `Fin.succAbove`s may have a clean Mathlib lemma I haven't located; if so, the `cofactor_chain` LOC count drops further.
- The `[NeZero n]` typeclass annotations in §1 table may carry through to `adjugate_fin_succ_eq_det_submatrix` indirectly via `cycleRange` (since `adjugate_fin_succ` uses `det_succ_row` internally, line 364). For the S4 ACT case with `n = n'.succ ≥ 1`, this is automatic.

**Verification performed**:

- All §1 file:line citations verified by `gh api repos/leanprover-community/mathlib4/contents/<path>` + `base64 -d` reads on the current master at 2026-05-12 snapshot.
- §2 algebraic chain verified by hand on the n=1 case (4-pivot quadrant in S4c PREP §2 matches the direct-adjugate prediction).
- §3 sanity-check example is purely a smoke-test pattern; not yet run in Lean.
- §5 LOC comparison is order-of-magnitude only.

**0 axioms added, 0 sorries added/removed, 0 Lean LOC changed in this PR.** No Docker build.

## 10. Appendix A — Mathlib API verification commands

```bash
# (1) Verify Matrix.adjugate_fin_succ_eq_det_submatrix at v4.26.0:
gh api repos/leanprover-community/mathlib4/contents/Mathlib/LinearAlgebra/Matrix/Adjugate.lean \
  --jq '.content' | base64 -d | sed -n '360,370p'

# (2) Verify Matrix.det_succ_row at v4.26.0:
gh api repos/leanprover-community/mathlib4/contents/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean \
  --jq '.content' | base64 -d | sed -n '768,785p'

# (3) Verify Matrix.inv_def at v4.26.0:
gh api repos/leanprover-community/mathlib4/contents/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean \
  --jq '.content' | base64 -d | sed -n '170,180p'

# (4) Verify Fin.sum_univ_succAbove (via @[to_additive] on prod_univ_succAbove):
gh api repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/BigOperators/Fin.lean \
  --jq '.content' | base64 -d | sed -n '65,75p'

# (5) Inspect the Lean file's current state of the sorry:
sed -n '265,270p' proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean
```

## 11. References

- **PR #18525** (S4c PREP, merged 2026-05-13 ~03:48 UTC): `sessions/2026-05-13-s04c-prep-sign-quadrant-n2-verification.md` — the n=2 four-pivot quadrant verification confirming Option B's `(-1)^(i+j)` sign.
- **PR #18409** (S4 PREP, merged 2026-05-13 02:09 UTC): `sessions/2026-05-12-s4b-prep-block-schur-reshape.md` — the cycleRange/blockReindex strategy and the sign-discrepancy finding that motivated Option B.
- **PR #18346** (S4 OBSERVE, merged): `sessions/2026-05-12-s4-observe-minv-construction-fork.md` — the original `Minv`-construction fork analysis.
- **PR #18214** (S3 SCAFFOLD, merged): introduced `qdetN_step`, `qdetN_step_zero_minv`, and the strategic sorry `qdetN_step_eq_qdetF`.
- **Mathlib v4.26.0**: `Mathlib/LinearAlgebra/Matrix/Adjugate.lean`, `.../Determinant/Basic.lean`, `.../NonsingularInverse.lean`, `Mathlib/Algebra/BigOperators/Fin.lean`, `Mathlib/GroupTheory/Perm/Fin.lean`. All paths verified at master snapshot 2026-05-12 via Contents API.
- **Project memory pattern**: `feedback_researcher_12_2026_05_13_triple_mathlib_bearer_audit.md` (parent PREP under-specified Mathlib bearers → drill into actual API).
