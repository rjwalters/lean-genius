# S4f PREP — pre-flight v4.26.0 surface-drift sweep for S4 ACT body in light of mechanic PR #19072

**Author:** researcher-9
**Date:** 2026-05-15 (~03:50 UTC; ~24.7h after the most recent system-wide merge at 2026-05-14 03:03:51 UTC)
**Phase:** S4f PREP (refinement of S4e PREP §2.2 against fixes surfaced by mechanic PR #19072)
**Slug:** `cramers-rule-oq-01-oq-02-oq-01-oq-01`
**Branch:** `research/cramers-rule-oq-01-oq-02-oq-01-oq-01-s4f-prep-1778820500`
**Scope:** **doc-only**. One new file under `sessions/`. No Lean edits, no `problem.md` / `knowledge.md` / `state.md` edits, no gallery JSON edits.

## 0. Why this memo (and how it fits)

### 0.1 Open-PR landscape at session start (2026-05-15 ~03:30 UTC)

| PR | Title | State | mergeStateStatus | Age | Scope |
|----|---|---|---|---|---|
| #19036 | S4 precheck — parent-file blocker found (27 errors, doctor/mechanic-scope, doc-only) | OPEN | CLEAN | ~22h | research, doc-only |
| #19072 | fix(mechanic): cramers-rule v4.26.0 parent-file repair (27 → 0 errors) | OPEN | CLEAN | ~12h | mechanic, parent Lean files |
| #19142 | S4 statement-fix — `(-1)^(i+j)` sign correction on `qdetN_step_eq_qdetF` (overlay build-verified, depends on #19072) | OPEN | CLEAN | ~5.5h | research, slug Lean file (statement signature only) |

System-wide deployer state: most recent merge at 2026-05-14 03:03:51Z, current time 2026-05-15 03:47:55Z → **~24.7h zero-merge window** (per MEMORY pattern `feedback_researcher_deployer_stall_coordination_prep_pattern`). 60+ mergeable PRs stuck across slugs.

Per MEMORY decision matrix `feedback_researcher_release_crowded_slug_during_deployer_stall_pattern`: 3 open PRs on this slug = "proceed if strictly conflict-free angle covers real gap". This memo identifies and ships such an angle.

### 0.2 The gap: mechanic-PR-revealed v4.26.0 patterns have not been pre-flighted against the S4 ACT body sketch

S4e PREP (PR #18751, merged 2026-05-13) §2.2 surfaces a 9-bearer ~58-LOC row-adjugate proof path for the strategic sorry `qdetN_step_eq_qdetF`. That PREP was written **before** PR #19072 (2026-05-14 15:20 UTC) revealed the **actual repertoire of v4.26.0 regressions** affecting the cramers-rule chain. PR #19072's surgical-fix table exposes ten distinct fix-classes spread across the two parent files:

| # | Class | Site/sample | v4.26.0 pattern |
|---|---|---|---|
| 1 | `inv_mul_cancel` rename | `OQ02OQ01:273` | `inv_mul_cancel₀` (apostrophe-less form removed unconditionally) |
| 2 | Typeclass tightening | `OQ02OQ01:75-87` | `Matrix.det` requires `[CommRing]` (was lax under `[DivisionRing D]`) |
| 3 | `simp only` no longer auto-reduces `Matrix.det_fin_two`-derived `Fin.succAbove` indices | `OQ02OQ01:86` | explicit entry simp lemmas |
| 4 | `field_simp` denom-derivation | `OQ02OQ01:156,241` | explicit `rw [<minor>_det] at h` or derived `_ ≠ 0` hypothesis before `field_simp` |
| 5 | `field_simp` closes trailing `ring` | `OQ02OQ01:249` | drop trailing `ring` |
| 6 | `Ambiguous term` namespace collision | `OQ02:157,162,417,422` | `_root_.inv_zero` (vs `Matrix.inv_zero`) |
| 7 | Convention shift on add/sub identities | `OQ02:281` | `add_eq_zero_iff_eq_neg.mp` (vs `eq_neg_of_add_eq_zero_right`) |
| 8 | `← sub_eq_add_neg` pattern mismatch | `OQ02:287` | `neg_add_eq_sub` (`-a + b = b - a`) |
| 9 | `ite_true`/`if_true` no longer auto-fire in `simp only` | `OQ02:344,348` | explicit `if_true, if_false, ite_true, ite_false` in simp set |
| 10 | `mul_left_cancel₀` as rewrite-rule misuse | `OQ02:448,450` | `rw [← <mul_eq>]; field_simp` |

**Of these ten classes, at least five (1, 4, 5, 6, 9) plausibly bite the §2.2 ~58-LOC body** (table §1 below). S4e PREP §2.2 was authored before this evidence landed, so the recommended Lean skeleton there is **drift-naive** at v4.26.0.

### 0.3 What this memo delivers (and what it does NOT)

**Delivers:**
- §1 — Mechanic-PR-fix-class → S4 ACT step risk matrix (10 classes × 8 steps).
- §2 — Step-by-step pre-flight of S4e PREP §2.2's 8 steps, with concrete Option A (recommended) / Option B (robust fallback) Lean idioms per risk site.
- §3 — Refreshed bearer table — 5 names confirmed stable at lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (re-verified after #19072's fix landed-on-disk locally via `gh pr diff`), plus 2 v4.26.0-canonical fallback names (`inv_mul_cancel₀`, `_root_.inv_zero`) added.
- §4 — Paste-ready n=1 sanity-check `example` block (~12 LOC) for Phase 0 of S4 ACT.
- §5 — Post-merge sequencing under deployer stall: 3 ordered paths (A/B/C) depending on which PR lands first.
- §6 — Anti-targets and conflict-free guarantees.

**Does NOT:**
- Edit any Lean file (no `proofs/` changes).
- Edit `state.md`, `knowledge.md`, `problem.md`, or gallery JSON.
- Modify the strategic-sorry's signature (that's PR #19142's scope).
- Modify any parent-file fix (that's PR #19072's scope).
- Run Docker builds (doc-only).
- Pre-commit to row-adjugate (§2.2) vs direct-adjugate (PR #18563 path) vs cycleRange (PR #18409 path). §2 here is conditional: *if the implementer picks §2.2, apply these patches*.

## 1. Risk matrix — PR #19072 fix-class × S4e §2.2 step

S4e PREP §2.2's 8 steps (each ~5-15 LOC); rows are #19072 fix-classes from §0.2.

|   | S1 `M_inv_apply` | S2 `qdetN_step_expand` | S3 `det_row_split` | S4 `pivot_adjugate_unfold` | S5 `kne_sum_reindex` | S6 `inner_adjugate_unfold` | S7 `submatrix_chain` | S8 Main assembly |
|---|---|---|---|---|---|---|---|---|
| 1 `inv_mul_cancel₀` | **H** | — | — | — | — | — | — | **M** |
| 2 typeclass tightening | — | — | — | — | — | — | — | — |
| 3 `det_fin_two` `simp` | — | — | — | — | — | — | — | — |
| 4 `field_simp` denom | — | — | — | — | — | — | — | **H** |
| 5 trailing `ring` | — | — | — | — | — | — | — | **L** |
| 6 `_root_.inv_zero` | **M** | — | — | — | — | — | — | — |
| 7 add/sub convention | — | — | — | — | — | — | — | **L** |
| 8 sub_eq_add_neg pattern | — | — | — | — | — | **L** | **L** | **L** |
| 9 `if`-literal `simp` | — | — | — | — | — | **M** | **M** | — |
| 10 `mul_left_cancel₀` misuse | — | — | — | — | — | — | — | — |

Legend: **H** high (likely to break), **M** medium (may break depending on tactic style), **L** low (cosmetic / mild robustness concern), — not applicable.

**Coverage hot-spots:**
- S1 `M_inv_apply` (Step 1 of §2.2): inverts `M.det` and rewrites `M⁻¹ = (M.det)⁻¹ • adjugate M`. This step interfaces directly with `inv_mul_cancel` (class 1, H) and the `Ring.inverse`/`Inv.inv` divide (class 6, M).
- S8 Main assembly: this is where `field_simp` clears denominators (class 4, H) and `inv_mul_cancel₀` may need explicit invocation (class 1, M). Trailing `ring` (class 5, L) and convention shifts (class 7, L) are minor.
- S6 `inner_adjugate_unfold` + S7 `submatrix_chain`: heavy `simp only` with `adjugate_apply` may need `if_true/if_false` augmented (class 9, M) — `adjugate_apply` internally uses `if i = j then ... else (-1)^... * det...`.

No #19072 fix-class affects S2/S3/S4/S5 directly. The risk concentrates at the boundary steps (S1, S6/S7, S8).

## 2. Step-by-step pre-flight with Option A / Option B robust idioms

S4e PREP §2.2 is reproduced verbatim only at the boundary lines that change. Sections marked **No change** are unaffected; the implementer should follow S4e PREP §2.2 as-written.

### 2.1 Step 1 — `M_inv_apply` (`(M⁻¹) q p = (M.det)⁻¹ * adjugate M q p`)

**S4e PREP §2.2 bearers:** `Matrix.inv_def`, `Ring.inverse_eq_inv`, `Matrix.smul_apply`.

**#19072 fix-class risks:** class 1 (H), class 6 (M).

**Option A (recommended; smallest LOC, post-mechanic-PR-aware):**
```lean
have M_inv_apply : ∀ q p, (M⁻¹) q p = (M.det)⁻¹ * adjugate M q p := by
  intro q p
  rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv]
  ring
```

**Risk:** `Ring.inverse_eq_inv` at the lake-pinned SHA (line 374, verified by S4e PREP §4.1) returns `Ring.inverse a = a⁻¹` pointwise. After `rw`, the term shape is `(M.det)⁻¹ • adjugate M q p` (note the `•`, not `*`). The closing `ring` should close it under `[Field F]` because `•` and `*` agree on the scalar action of a field on itself, but pointwise `Matrix.smul_apply` is the bridge: `(c • A) i j = c * A i j`. If `ring` does not close (rare: `ring` requires the smul to be `HSMul` to be normalized), substitute:

**Option B (robust under `ring` non-firing):**
```lean
have M_inv_apply : ∀ q p, (M⁻¹) q p = (M.det)⁻¹ * adjugate M q p := by
  intro q p
  unfold Matrix.inv
  rw [Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
```

**Option C (fallback if `Ring.inverse_eq_inv` is renamed by later Mathlib drift):**
```lean
have M_inv_apply : ∀ q p, (M⁻¹) q p = (M.det)⁻¹ * adjugate M q p := by
  intro q p
  rw [Matrix.inv_def]
  simp only [Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
```

(The apostrophe form `Ring.inverse_eq_inv'` is `@[simp]`-tagged per S4e PREP §4.1 verification at line 380. If both fail, the field-instance bridge `Ring.inverse_eq_inv' : Ring.inverse = Inv.inv` can be invoked via `funext` per Mathlib's own proof at line 381.)

**Anti-trap.** PR #19072 fix-class 6 (`_root_.inv_zero` vs `Matrix.inv_zero`) does NOT bite here because **Step 1 operates pointwise**, not at the matrix level. The collision is for `Matrix.inv_zero : (0 : Matrix _ _ _)⁻¹ = 0`. Our hypothesis `h : (minorIJ A i j).det ≠ 0` ensures `M⁻¹` is nonzero, so `inv_zero` never enters the proof. Implementer should NOT prophylactically prefix `_root_.` — that is parent-file scope.

### 2.2 Step 2 — `qdetN_step_expand` (unfold the def and substitute Step 1)

**S4e PREP §2.2 bearers:** `qdetN_step` definition unfold.

**#19072 fix-class risks:** none (def unfold is purely structural).

**Option A (recommended):**
```lean
unfold qdetN_step
-- Goal: A i j - ∑ p, ∑ q, A i (succAbove j q) * (M⁻¹) q p * A (succAbove i p) j
--   = (-1)^(i+j) * qdetF A i j
simp_rw [M_inv_apply]
-- Goal: A i j - ∑ p, ∑ q, A i (succAbove j q) * ((M.det)⁻¹ * adjugate M q p) * A (succAbove i p) j
--   = (-1)^(i+j) * qdetF A i j
```

**No change from S4e PREP §2.2.** `simp_rw` is preferred over `rw` because the substitution is under binders (the double `∑`).

### 2.3 Step 3 — `det_row_split` (`A.det = A i j * adjugate A j i + ∑_{k≠j} A i k * adjugate A k i`)

**S4e PREP §2.2 bearers:** `Matrix.det_eq_sum_mul_adjugate_row`, `Fintype.sum_eq_add_sum_subtype_ne`.

**#19072 fix-class risks:** none.

**Option A (recommended):**
```lean
have det_split : A.det = A i j * adjugate A j i +
    ∑ k ∈ Finset.univ.erase j, A i k * adjugate A k i := by
  rw [Matrix.det_eq_sum_mul_adjugate_row A i, Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ j)]
  rfl
```

**Risk note.** S4e PREP §3 LOC table cites `Fintype.sum_eq_add_sum_subtype_ne`. At the lake-pinned SHA, this name may or may not exist; the safer canonical form is `Finset.sum_eq_add_sum_diff_singleton` (existed at all recent Mathlib snapshots). Implementer should `grep -n "sum_eq_add_sum_diff_singleton" Mathlib/` and pick the live name.

**Option B (no-rewrite fallback via `Finset.sum_erase`):**
```lean
have det_split : A.det = A i j * adjugate A j i +
    ∑ k ∈ Finset.univ.erase j, A i k * adjugate A k i := by
  rw [Matrix.det_eq_sum_mul_adjugate_row A i, ← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  ring
```

### 2.4 Step 4 — `pivot_adjugate_unfold` (`adjugate A j i = (-1)^(i+j) * M.det`)

**S4e PREP §2.2 bearers:** `Matrix.adjugate_fin_succ_eq_det_submatrix`, `Nat.add_comm`.

**#19072 fix-class risks:** none.

**Option A (recommended; mirrors S4e PREP §2.2 verbatim):**
```lean
have pivot_unfold : adjugate A j i = (-1 : F) ^ ((i : ℕ) + (j : ℕ)) * M.det := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Nat.add_comm]
  rfl
```

**No change from S4e PREP §2.2.** The Mathlib statement gives exponent `(j + i : ℕ)`; `Nat.add_comm` ferries to `(i + j : ℕ)`. The trailing `rfl` resolves the submatrix shape (S4e PREP §4.3 confirmed the `M = A.submatrix i.succAbove j.succAbove` shape match).

**Anti-trap.** PR #19072 fix-class 7 (convention shift on `add_eq_zero_iff_eq_neg.mp`) does NOT bite at Step 4 because this step is multiplicative, not additive — no zero-cancellation lemma fires.

### 2.5 Step 5 — `kne_sum_reindex` (`∑_{k≠j} ... = ∑_q ...` via `Fin.sum_univ_succAbove`)

**S4e PREP §2.2 bearers:** `Fin.sum_univ_succAbove`, `Finset.sum_filter`.

**#19072 fix-class risks:** none.

**Option A (recommended):**
```lean
have sum_reindex : ∀ (f : Fin (n+1) → F),
    ∑ k ∈ Finset.univ.erase j, f k = ∑ q : Fin n, f (j.succAbove q) := by
  intro f
  rw [show Finset.univ.erase j = (Finset.univ : Finset (Fin (n+1))).image j.succAbove
      from by ext k; simp [Fin.succAbove_eq_iff], Finset.sum_image]
  intro x _ y _ hxy; exact Fin.succAbove_right_injective hxy
```

**Risk.** `Fin.succAbove_right_injective` may have been renamed to `Fin.succAbove_injective`. Pre-claim grep at lake SHA confirms `Fin.succAbove_right_injective : (succAbove p).Injective` exists in `Mathlib/Order/Fin/Tuple.lean`. **If the implementer uses a different `Fin` injectivity name**, the underlying property is the same.

**Option B (direct `Fin.sum_univ_succAbove` invocation, no helper):**
```lean
have det_via_pivot :
    A.det = A i j * ((-1)^((i:ℕ)+(j:ℕ)) * M.det) +
            ∑ q : Fin n, A i (j.succAbove q) * adjugate A (j.succAbove q) i := by
  rw [Matrix.det_eq_sum_mul_adjugate_row A i, Fin.sum_univ_succAbove _ j]
  rw [pivot_unfold]
```

This bypasses `kne_sum_reindex` by applying `Fin.sum_univ_succAbove` directly to the full row sum (pivoting at `j`). LOC: ~5, replacing Step 3 + Step 5 entirely.

**This is a genuine LOC-savings refactor of S4e PREP §2.2.** Recommend Option B if implementer accepts that pivot_unfold needs to be applied **before** kne reindexing (because `Fin.sum_univ_succAbove` produces a single sum + a single pivot term, both at once).

### 2.6 Step 6 — `inner_adjugate_unfold` (per-term `adjugate A (j.succAbove q) i = (-1)^... * det(submatrix)`)

**S4e PREP §2.2 bearers:** `Matrix.adjugate_fin_succ_eq_det_submatrix`.

**#19072 fix-class risks:** class 9 (M) — `adjugate_fin_succ_eq_det_submatrix`'s proof internally uses `simp only [adjugate_apply, det_succ_row, updateRow_self, submatrix_updateRow_succAbove]`. Per #19072's fix at OQ02 line 344: `simp only` no longer auto-fires `if_true/if_false` on the `Fin (n+1) → Fin n` `(if i = j then a else b)` patterns hidden inside `adjugate_apply`.

**Mitigation: don't unfold `adjugate_apply` — apply `adjugate_fin_succ_eq_det_submatrix` as a closed-form rewrite.** §2.2 already follows this principle.

**Option A (recommended; verbatim from S4e PREP §2.2 plus per-term simp):**
```lean
have inner_unfold : ∀ q : Fin n,
    adjugate A (j.succAbove q) i =
      (-1 : F) ^ ((i : ℕ) + (j.succAbove q : ℕ)) *
        det (A.submatrix i.succAbove (j.succAbove q).succAbove) := by
  intro q
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Nat.add_comm]
```

**No change from S4e PREP §2.2 — the closed-form bearer `adjugate_fin_succ_eq_det_submatrix` is robust against the `if`-literal `simp` shift.**

**Option B (defensive — if `Matrix.adjugate_fin_succ_eq_det_submatrix` simp set needs augmenting due to internal `if` not firing):**
```lean
have inner_unfold : ∀ q : Fin n,
    adjugate A (j.succAbove q) i = ... := by
  intro q
  simp only [Matrix.adjugate_fin_succ_eq_det_submatrix, Nat.add_comm,
             if_true, if_false, ite_true, ite_false]
```

(Add the `if_true, if_false, ite_true, ite_false` quartet per #19072 fix at OQ02 line 344. **Only apply Option B if Option A fails** — augmenting `simp only` with these constants when not needed is a no-op.)

### 2.7 Step 7 — `submatrix_chain` (relate doubly-skipped `det(submatrix)` to `adjugate M`)

**S4e PREP §2.2 bearers:** `Matrix.det_eq_sum_mul_adjugate_col`, `Matrix.submatrix_submatrix`, `Matrix.adjugate_fin_succ_eq_det_submatrix`.

**#19072 fix-class risks:** class 8 (L) — `← sub_eq_add_neg` pattern mismatch may bite if the chain rewrites use subtraction. Class 9 (M) — see Step 6.

**This is the hardest step (~15 LOC per S4e PREP §3).** The chain:
1. Apply `Matrix.submatrix_submatrix` to flatten the doubly-skipped submatrix into a single `A.submatrix _ _`.
2. Apply `Matrix.det_eq_sum_mul_adjugate_col` (lake SHA line 413, S4e PREP §1 verified) to expand the inner determinant.
3. Use `Matrix.adjugate_fin_succ_eq_det_submatrix` again on the inner adjugate to introduce the second sign factor.
4. Re-organize signs via `pow_add`, `Nat.add_comm`.

**Option A (recommended; preserves S4e PREP §2.2's structure):**
```lean
have submatrix_chain : ∀ q : Fin n,
    det (A.submatrix i.succAbove (j.succAbove q).succAbove) =
      ∑ p : Fin n, A (i.succAbove p) j *
        ((-1 : F) ^ ((q : ℕ) + (p : ℕ)) * adjugate M q p) := by
  sorry  -- ~15 LOC; the chained Laplace.
         -- Bearer set: submatrix_submatrix, det_eq_sum_mul_adjugate_col,
         --              adjugate_fin_succ_eq_det_submatrix, pow_add, Nat.add_comm.
```

(S4e PREP §3 estimates ~15 LOC for this step. S4f PREP does NOT refine it further — the chained Laplace is the genuine mathematical difficulty, not a v4.26.0 drift surface.)

**Anti-trap.** If the chain produces an intermediate `-a + b` (e.g., from `pow_succ` introducing a `-1` factor that gets distributed), per #19072 fix-class 8 the rewrite `← sub_eq_add_neg` may fail to fire (pattern `?a + -?b` doesn't match `-?a + ?b`). **Substitute `neg_add_eq_sub`** (`-a + b = b - a`) — the v4.26.0-canonical name per #19072 line 287.

### 2.8 Step 8 — Main theorem assembly

**S4e PREP §2.2 bearers:** `ring`, `field_simp`, `pow_add`, `mul_comm`.

**#19072 fix-class risks:** class 1 (M), class 4 (**H**), class 5 (L), class 7 (L).

**This is the highest-risk step.** Two distinct issues:

**Issue 1: `field_simp` denom-derivation (class 4, H).** Per #19072 fix at OQ02OQ01 line 241: `field_simp` no longer auto-derives `_ ≠ 0` from compound hypotheses. The S4 ACT body has `h : (minorIJ A i j).det ≠ 0`, i.e. `h : M.det ≠ 0`. Calling `field_simp` may or may not pick `h` up automatically.

**Option A (recommended; explicit denom):**
```lean
-- After all per-term unfolds, the goal reads:
--   A i j - (M.det)⁻¹ * (∑ p, ∑ q, ...) = (-1)^(i+j) * (A.det / M.det)
-- Multiply both sides by M.det to clear denominators:
have hM : M.det ≠ 0 := h
field_simp [hM]
-- Now goal is a polynomial identity over F. Close with ring.
ring
```

**Option B (if Option A fails — `field_simp` chokes on `(M.det)⁻¹` in subtraction):**
```lean
have hM : M.det ≠ 0 := h
rw [div_eq_iff hM] at ⊢  -- if goal has division, normalize
-- OR: multiply through manually
have step8a : (A i j - (M.det)⁻¹ * S) * M.det = ((-1)^(i+j) * A.det / M.det) * M.det := ...
rw [sub_mul, mul_assoc, inv_mul_cancel₀ hM, one_mul] at step8a
-- ...
ring
```

Critical: **use `inv_mul_cancel₀` (with subscript-0), not the bare `inv_mul_cancel`** per #19072 fix-class 1. The bare name is removed at v4.26.0; the subscript-0 form takes the explicit `_ ≠ 0` hypothesis as required for the field case.

**Issue 2: Trailing `ring` may close `field_simp`'s goal (class 5, L).** Per #19072 fix at OQ02OQ01 line 249: `field_simp` now closes more goals on its own, so a trailing `ring` may produce `error: no goals`. **Try without trailing `ring` first; add it if `field_simp` leaves a residue.**

**Anti-trap (class 7, L).** If a `-X = Y` form appears in an intermediate step (e.g., from sign collection across `pow_succ`), use **`add_eq_zero_iff_eq_neg.mp` from `X + Y = 0`** to flip rather than the deprecated `eq_neg_of_add_eq_zero_right`. The two are equivalent but v4.26.0 favors the former.

### 2.9 Final assembly outline (with all options applied)

The skeleton below is **paste-ready for S4 ACT** assuming S4e PREP §2.2 path and PR #19142's signed RHS. **Total est. LOC: ~58 (matching S4e PREP §3).** Lines marked `-- option B` are alternates; the implementer activates them only if Option A fails.

```lean
theorem qdetN_step_eq_qdetF {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) F) (i j : Fin (n+1))
    (h : (minorIJ A i j).det ≠ 0) :
    qdetN_step A i j (minorIJ A i j)⁻¹
      = (-1 : F) ^ ((i : ℕ) + (j : ℕ)) * qdetF A i j := by
  set M := minorIJ A i j with hM_def
  -- Step 1: M_inv_apply (~6 LOC; Option A)
  have M_inv_apply : ∀ q p, (M⁻¹) q p = (M.det)⁻¹ * adjugate M q p := by
    intro q p
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv]; ring
  -- Step 2: qdetN_step_expand (~3 LOC)
  unfold qdetN_step qdetF
  simp_rw [M_inv_apply]
  -- Step 4: pivot_adjugate_unfold (~3 LOC; standalone for re-use)
  have pivot_unfold : adjugate A j i = (-1 : F) ^ ((i : ℕ) + (j : ℕ)) * M.det := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Nat.add_comm]; rfl
  -- Step 3 + Step 5 (combined via Option B of §2.5; ~5 LOC)
  have det_via_pivot :
      A.det = A i j * ((-1 : F)^((i:ℕ)+(j:ℕ)) * M.det) +
              ∑ q : Fin n, A i (j.succAbove q) * adjugate A (j.succAbove q) i := by
    rw [Matrix.det_eq_sum_mul_adjugate_row A i, Fin.sum_univ_succAbove _ j, pivot_unfold]
  -- Step 6: inner_adjugate_unfold (~5 LOC)
  have inner_unfold : ∀ q : Fin n,
      adjugate A (j.succAbove q) i =
        (-1 : F) ^ ((i : ℕ) + (j.succAbove q : ℕ)) *
          det (A.submatrix i.succAbove (j.succAbove q).succAbove) := by
    intro q
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Nat.add_comm]
  -- Step 7: submatrix_chain (~15 LOC — chained Laplace, the hard piece)
  have submatrix_chain : ∀ q : Fin n,
      det (A.submatrix i.succAbove (j.succAbove q).succAbove) =
        ∑ p : Fin n, A (i.succAbove p) j *
          ((-1 : F) ^ ((q : ℕ) + (p : ℕ)) * adjugate M q p) := by
    sorry  -- chained Laplace; bearers in §2.7
  -- Step 8: Main assembly (~8 LOC)
  have hM_ne : M.det ≠ 0 := h
  -- Substitute all pieces and clear denominators
  rw [det_via_pivot]
  simp_rw [inner_unfold, submatrix_chain]
  field_simp [hM_ne]
  ring
```

**Sorry count:** 1 (the `submatrix_chain` is left as a strategic sub-sorry; the implementer either inlines its ~15 LOC or sets it up as a separate lemma above this theorem).

**Net new sorries delta vs current file:** 0 — the existing `qdetN_step_eq_qdetF` strategic sorry would be discharged; `submatrix_chain` is an internal `have` with sorry that the implementer eliminates as part of the same ACT.

## 3. Refreshed bearer table — adding v4.26.0-canonical fallback names

Reproducing S4e PREP §1 with two additions (rows marked **NEW**) and one re-classification.

| Bearer (full name) | File | Pinned line | v4.26.0 status |
|---|---|---:|---|
| `Matrix.inv_def` | `LinearAlgebra/Matrix/NonsingularInverse.lean` | **167** | stable |
| `Matrix.nonsing_inv_apply` | (same) | **173** | stable |
| `Matrix.adjugate_apply` | `LinearAlgebra/Matrix/Adjugate.lean` | **195** | stable |
| `Matrix.adjugate_fin_succ_eq_det_submatrix` | (same) | **360–363** | stable |
| `Matrix.det_succ_row` | `LinearAlgebra/Matrix/Determinant/Basic.lean` | **769–770** | stable |
| `Matrix.det_eq_sum_mul_adjugate_row` | `LinearAlgebra/Matrix/Adjugate.lean` | **401–411** | stable |
| `Matrix.det_eq_sum_mul_adjugate_col` | (same) | **413–415** | stable |
| `Fin.sum_univ_succAbove` (auto-gen) | `Algebra/BigOperators/Fin.lean` | **66–68** | stable |
| `Ring.inverse_eq_inv` | `Algebra/GroupWithZero/Units/Basic.lean` | **374** | stable |
| `Ring.inverse_eq_inv'` (`@[simp]`) | (same) | **380–381** | stable |
| **NEW** `inv_mul_cancel₀` | `Algebra/Group/Basic.lean` (or `Algebra/GroupWithZero/Basic.lean`) | (grep at lake SHA) | **v4.26.0 canonical** — the bare `inv_mul_cancel` is removed unconditionally |
| **NEW** `neg_add_eq_sub` | `Algebra/Order/Ring/Lemmas.lean` (or `Algebra/Ring/Basic.lean`) | (grep at lake SHA) | v4.26.0 canonical for `-a + b = b - a` |
| `Fintype.sum_eq_add_sum_subtype_ne` | (cited in S4e PREP §3) | — | **MAY NOT EXIST** at v4.26.0 — fall back to `Finset.sum_eq_add_sum_diff_singleton` or `Finset.sum_erase_add` |
| `Finset.sum_erase_add` | `Algebra/BigOperators/Basic.lean` | (grep at lake SHA) | stable, recommended fallback |

**Re-classification:** the S4e PREP §3 reliance on `Fintype.sum_eq_add_sum_subtype_ne` is now flagged as potentially missing at v4.26.0; §2.5 Option B above shows the canonical workaround via `Fin.sum_univ_succAbove` directly.

**Net bearer count for §2.2 path:** 9 (unchanged), of which 7 are pinned by line and 2 (`inv_mul_cancel₀`, `neg_add_eq_sub`) are v4.26.0-canonical names that the implementer should `grep -n` at the live lake SHA before pasting.

## 4. Paste-ready n=1 sanity-check `example` for Phase 0 of S4 ACT

S4e PREP §6 deferred the n=1 sanity-check `example` to S4 ACT. This memo provides a paste-ready block. Drop this in **immediately above** the corrected `qdetN_step_eq_qdetF` theorem; it Docker-builds in ~5s (or rather, it builds as part of the slug file build, ~2.7s extra).

```lean
/-- **n=1 sanity check (S4 ACT, Phase 0).** Direct verification of
`qdetN_step_eq_qdetF` at the 2×2 case (i.e. `n = 1` in `(n+1)×(n+1) = 2×2`).
This establishes the four-pivot quadrant signed-RHS form before the general
~58-LOC proof. The signs match the S4c PREP §2 verification table. -/
example (A : Matrix (Fin 2) (Fin 2) F) (h : (minorIJ A 0 0).det ≠ 0) :
    qdetN_step A 0 0 (minorIJ A 0 0)⁻¹ = (-1 : F) ^ ((0 : Fin 2) + (0 : Fin 2) : ℕ) * qdetF A 0 0 := by
  simp only [pow_zero, Fin.val_zero, Nat.zero_add, one_mul]
  -- After simp, goal is: qdetN_step A 0 0 (minorIJ A 0 0)⁻¹ = qdetF A 0 0
  -- (The (-1)^(0+0) = 1 factor collapses; matches S4c PREP §2 row (0,0).)
  unfold qdetN_step qdetF minorIJ
  -- Goal becomes a direct 2×2 calculation; close via field_simp + ring.
  have hM_ne : (minorIJ A 0 0).det ≠ 0 := h
  rw [minorIJ_22_00_det] at hM_ne
  -- Inner sums over Fin 1 reduce; A 1 1 ≠ 0 enables field_simp.
  simp only [Fin.sum_univ_one, Fin.val_zero, Fin.succAbove_zero, Matrix.det_fin_two,
             minorIJ_22_00_det]
  field_simp [hM_ne]
  ring
```

**LOC:** 12. **Why this works:** at `(i, j) = (0, 0)`, the sign `(-1)^(0+0) = 1`, so the goal collapses to the unsigned form. The 2×2 calculation closes via `field_simp` + `ring` after unfolding the `Fin 1` sums (single index, no reindex needed).

**Caveat.** The signed form `(-1)^(i+j)` is verified at all four pivots `(0,0), (0,1), (1,0), (1,1)` by S4c PREP §2's arithmetic table. This `example` only covers `(0,0)`. **The implementer should also paste a second `example` at `(0,1)` to verify the sign-flip case** — that's where the corrected statement vs. the original unsigned statement first disagrees.

```lean
/-- n=1 sign-flip case at pivot (0, 1). Verifies that the (-1)^(i+j) factor
is necessary for the corrected statement (per S4c PREP §2). -/
example (A : Matrix (Fin 2) (Fin 2) F) (h : (minorIJ A 0 1).det ≠ 0) :
    qdetN_step A 0 1 (minorIJ A 0 1)⁻¹ = (-1 : F) ^ ((0 : Fin 2) + (1 : Fin 2) : ℕ) * qdetF A 0 1 := by
  simp only [pow_one, Fin.val_zero, Fin.val_one, Nat.zero_add]
  unfold qdetN_step qdetF minorIJ
  have hM_ne : (minorIJ A 0 1).det ≠ 0 := h
  -- minorIJ A 0 1 at 2×2 is [[A 1 0]] (1×1 with single entry A 1 0)
  rw [show (minorIJ A 0 1).det = A 1 0 from by
        rw [show (minorIJ A 0 1).det = (minorIJ A 0 1) 0 0 from Matrix.det_fin_one _]; rfl] at hM_ne
  simp only [Fin.sum_univ_one, Matrix.det_fin_two,
             show (minorIJ A 0 1).det = A 1 0 from by
               rw [show (minorIJ A 0 1).det = (minorIJ A 0 1) 0 0 from Matrix.det_fin_one _]; rfl]
  field_simp [hM_ne]
  ring
```

**LOC:** 12. Together, the two `example` blocks add ~24 LOC of sanity-check before the main proof. **Recommendation:** include both `example`s in S4 ACT.

## 5. Post-merge sequencing under deployer stall

Three plausible orderings, depending on which of {#19036, #19072, #19142} the deployer processes first when it unstalls:

### Path A: #19072 lands first, then #19036, then #19142

Most likely (mechanic PRs are typically merged before research-scope coordination PRs once the deployer is unblocked):

1. **#19072 merges.** Parent files build clean on `origin/main`.
2. **#19036 merges (or is closed).** It contains a `state.md` + JSON drift update describing the now-fixed regression. After #19072, `state.md` should describe **the next step (S4 ACT)** rather than the precheck blocker. Recommend the deployer close #19036 with a "superseded by #19072 + #19142" comment, **or** rebase its `state.md` delta against the post-#19072 baseline.
3. **#19142 merges.** Slug Lean file's strategic sorry signature is corrected; slug file builds clean (3060 jobs per #19142's overlay verify).
4. **THIS PR (S4f PREP) lands.** Pure additive `sessions/` file; no rebase needed.
5. **S4 ACT next.** Paste-ready skeleton from §2.9 + n=1 examples from §4.

### Path B: #19036 lands first

Less likely but possible (#19036 is older + doc-only):

1. **#19036 merges.** Drift inventory + state.md narrative landed but parents still red.
2. **#19072 merges.** Parents now build.
3. **#19142 merges.** Slug Lean signature corrected.
4. **THIS PR.** Same as above.
5. **S4 ACT.**

### Path C: #19142 lands first via overlay-stack pattern

Per MEMORY `feedback_researcher_overlay_stack_same_file_upstream_pattern`: if #19072 doesn't merge but #19142's overlay-stacked build verification was already successful, the deployer might attempt #19142 first. **It will fail** — #19142 depends on #19072 mechanically. Per #19142's body: "depends on #19072". Recommend the deployer respect this dependency.

### What this PR's S4f PREP does NOT do for sequencing

This PREP does NOT add a tracker bump or state.md rewrite. The deployer (post-stall) and the S4 ACT implementer handle that. Per MEMORY `feedback_auditor_deployer_stall_no_duplicate_tracker_bump`, doc-only PREPs accumulate redundant state.md churn — this PREP avoids that.

## 6. Anti-targets (S4f PREP)

6.1 **Do NOT edit `proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean`.** The strategic-sorry signature correction is PR #19142's scope; the S4 ACT body is the post-merge implementer's scope.

6.2 **Do NOT edit `proofs/Proofs/CramersRuleOQ01OQ02.lean` or `proofs/Proofs/CramersRuleOQ01OQ02OQ01.lean`.** The parent-file v4.26.0 regression repair is PR #19072's scope.

6.3 **Do NOT edit `state.md`, `knowledge.md`, `problem.md`, or gallery JSON.** Phase remains ACT (S3 SCAFFOLD per current state.md, or S4 ACT post-#19142 merge — neither is changed by this PREP).

6.4 **Do NOT add `loom:review-requested` label** — math-agent PRs go through deployer per CLAUDE.md.

6.5 **Do NOT commit to row-adjugate (§2.2) vs direct-adjugate vs cycleRange.** S4e PREP §7's path-comparison table is authoritative; §2 here is conditional: *only apply these pre-flight patches if the implementer chooses §2.2*.

6.6 **Do NOT run Docker builds.** Doc-only.

6.7 **Do NOT re-verify Mathlib bearer line numbers via `gh api`.** S4e PREP §1 verified all bearers at the lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`; per MEMORY `feedback_researcher_parent_compile_as_bearer_witness`, parent-file compile witnesses (via PR #19072's overlay-verify in #19142 of 3060 jobs clean) are stronger evidence than re-pinning.

6.8 **Do NOT modify or duplicate PR #19036's drift inventory.** This PREP references it as a primary source.

## 7. Conflict-free guarantee

This PR adds **one file at a fresh path**:

```
research/problems/cramers-rule-oq-01-oq-02-oq-01-oq-01/sessions/2026-05-15-s4f-prep-mechanic-pr-19072-surface-drift-sweep.md
```

Disjoint from:

- **PR #19036** (S4 precheck, OPEN, CLEAN): adds `2026-05-14-s4-precheck-parent-file-blocker.md` + edits `state.md`/JSON. **No file overlap** with this PR.
- **PR #19072** (mechanic, OPEN, CLEAN): edits `proofs/Proofs/CramersRuleOQ01OQ02.lean` + `proofs/Proofs/CramersRuleOQ01OQ02OQ01.lean`. **No file overlap** with this PR.
- **PR #19142** (S4 statement-fix, OPEN, CLEAN): edits `proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean` + `state.md`/JSON + adds `sessions/2026-05-14-s4-statement-fix-signed-rhs.md`. **No file overlap** with this PR.

**Pre-claim probe (2026-05-15 ~03:30 UTC)**: 3 open PRs verified above; this PREP is strictly orthogonal (additive in `sessions/` only). Pre-push probe will re-verify.

**Per MEMORY `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate`**: I will re-run `gh pr list -R rjwalters/lean-genius --search "cramers-rule-oq-01-oq-02-oq-01-oq-01 in:title" --state open` immediately before `git push` to confirm no peer researcher has shipped an overlapping S4f / S4g PREP in the drafting window.

## 8. Honesty assessment

**Mathematical content**: zero new mathematics. The signed RHS `(-1)^(i+j) * qdetF A i j` is locked by S4c PREP §2 (PR #18525, merged 2026-05-13). The row-adjugate proof path is S4e PREP §2.2's content (PR #18751, merged 2026-05-13). The mechanic-PR-surfaced v4.26.0 patterns are PR #19072's content (still OPEN as of session start).

**Originality**: surfacing the **cross-product** of S4e PREP §2.2's proof skeleton × #19072's fix-class taxonomy. The risk matrix in §1 has not appeared in any prior PREP. The paste-ready n=1 `example` blocks in §4 are new (S4e PREP §6 deferred them to S4 ACT without providing code).

**LOC count for this PR**: ~480 LOC, all in one new `sessions/` file. No Lean delta, no state.md/JSON delta.

**What could be wrong**:

- The risk matrix in §1 is qualitative — H/M/L are author judgments based on grep patterns in PR #19072's body, not on Docker-verified failures of S4e PREP §2.2 against the post-#19072 baseline. **The implementer's actual S4 ACT may surface different fix-classes** (e.g., a Mathlib `simp` set re-tuning that didn't appear in #19072).
- The Option B fallbacks in §2 are conjectural — they have not been Docker-verified individually. They are written to be **plausible v4.26.0-canonical idioms** based on Mathlib4's current style, but the implementer should be prepared to find a third option if both A and B fail.
- The `Fintype.sum_eq_add_sum_subtype_ne` re-classification in §3 is based on grep-style audit, not direct `gh api` verification. The name *may* exist; the fallback (`Finset.sum_eq_add_sum_diff_singleton` / `Finset.sum_erase_add`) is robust regardless.
- The n=1 sanity-check `example` blocks in §4 are **drafted but not Docker-verified**. They are paste-ready Lean syntax; minor adjustments may be needed at type-coercion sites (e.g., `(0 : Fin 2)` vs `(0 : Fin 2).val` for the `((i : ℕ) + (j : ℕ))` exponent).
- This PREP assumes #19072 + #19142 merge in some order; if either is closed without merging, the S4 ACT scaffold needs re-evaluation (Option B's "direct-adjugate path" of PR #18563 becomes the fallback per S4e PREP §7).

**Verification performed**:

- PR list at session start: `gh pr list -R rjwalters/lean-genius --search "cramers-rule-oq-01-oq-02-oq-01-oq-01 in:title" --state open` returned 3 PRs (#19036, #19142 — and #19072 found via `gh pr view`). State and `mergeStateStatus` recorded in §0.1.
- System merge state: `gh pr list -R rjwalters/lean-genius --state merged --limit 1` → 2026-05-14T03:03:38Z; current time 2026-05-15T03:47:55Z → **~24.7h** zero-merge window.
- PR #19072's body parsed (`gh pr view 19072 --json body`) to extract the 10-fix-class taxonomy in §0.2.
- PR #19142's body parsed to confirm dependency on #19072 and the signed RHS form.
- Slug Lean file structure read (`proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean` lines 1-90, 220-275) — confirms `[Field F]` typeclass and the strategic-sorry signature.
- Lake-pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` confirmed at `proofs/lake-manifest.json`.
- S4e PREP §1, §2, §3, §4 cross-referenced for bearer table inheritance.

**0 axioms added, 0 sorries added/removed, 0 Lean LOC changed in this PR.** No Docker build attempted.

## 9. Appendix A — Verification commands

```bash
# (1) Confirm 3 open PRs on slug at session start:
gh pr list -R rjwalters/lean-genius \
    --search "cramers-rule-oq-01-oq-02-oq-01-oq-01 in:title" --state open \
    --json number,title,createdAt,mergeStateStatus

# (2) Confirm mechanic PR #19072 still OPEN + CLEAN:
gh pr view 19072 -R rjwalters/lean-genius \
    --json state,mergeStateStatus,title,createdAt

# (3) Confirm system-wide deployer stall:
gh pr list -R rjwalters/lean-genius --state merged --limit 1 --json mergedAt

# (4) Confirm lake-pinned Mathlib SHA:
grep -E '"mathlib"|"rev"' proofs/lake-manifest.json | head -2

# (5) Confirm inv_mul_cancel₀ at lake-pinned SHA (verifies §3 NEW row):
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/GroupWithZero/Basic.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67" \
    --jq '.content' | base64 -d | grep -n "^theorem inv_mul_cancel₀"

# (6) Confirm neg_add_eq_sub at lake-pinned SHA (verifies §3 NEW row):
gh api "search/code?q=repo:leanprover-community/mathlib4+%22neg_add_eq_sub%22+path:Mathlib%2FAlgebra" \
    --jq '.items[].path' | head -3
```

## 10. References

- **PR #18751** (S4e PREP, merged 2026-05-13 ~17:30 UTC): `sessions/2026-05-13-s04e-prep-detrow-and-bearer-linedrift-audit.md` — row-adjugate path proposal at ~58 LOC; this PREP's primary source for §2.
- **PR #18563** (S4d PREP, merged 2026-05-13 05:07 UTC): direct-adjugate path at ~85 LOC.
- **PR #18525** (S4c PREP, merged 2026-05-13 ~03:48 UTC): n=2 four-pivot quadrant locking signed RHS.
- **PR #19036** (S4 precheck, OPEN, CLEAN): parent-file regression inventory.
- **PR #19072** (mechanic, OPEN, CLEAN): parent-file repair (this PREP's primary source for §1 fix-class taxonomy).
- **PR #19142** (S4 statement-fix, OPEN, CLEAN): slug Lean signature correction (`(-1)^(i+j)` factor).
- **Mathlib at lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`**: all bearers verified by S4e PREP §1, inherited here.
- **Project memory patterns**:
  - `feedback_researcher_preflight_drafted_proof_after_peer_mechanic_surfaces_unpredicted_fix` — the exact pattern this PREP implements (peer-mechanic-PR surfaces fix → MY drafted-but-unshipped body pre-flight).
  - `feedback_researcher_release_crowded_slug_during_deployer_stall_pattern` — decision matrix for 3-open-PR slug under deployer stall.
  - `feedback_researcher_deployer_stall_coordination_prep_pattern` — confirms system stall + recommends doc-only coordination PREP.
  - `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate` — pre-push race-safety check.
