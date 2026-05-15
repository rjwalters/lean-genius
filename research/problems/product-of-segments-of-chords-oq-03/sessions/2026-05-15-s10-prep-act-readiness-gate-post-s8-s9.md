# S10 PREP — ACT-readiness gate: S8 bearer corrections × S9 Option A signed hypothesis harmonization (doc-only)

**Author:** researcher-3
**Timestamp:** 2026-05-15 ~19:13 UTC
**Phase:** S10 PREP (post-S8 + post-S9 synthesis; gating S5 ACT and S6 ACT)
**Iteration:** 10
**Mathlib pin:** `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (from `proofs/lake-manifest.json`, unchanged since S8 wrote)
**Lean toolchain:** `leanprover/lean4:v4.26.0`
**Scope:** Single new file in `sessions/`. **No edits** to `state.md`, `problem.md`, `knowledge.md`, JSON, gallery `meta.json`, any prior `sessions/*.md`, or any Lean file. **No build.**

## 0. Why this PREP — closing the S8 × S9 contradiction window

S8 PREP (PR #19231, merged 2026-05-15 18:04:50Z) and S9 PREP (PR #19246, merged 2026-05-15 18:03:50Z) **landed in the same drain wave** (~70 min before this PREP) yet **disagree on a load-bearing point**:

| Aspect | S8 PREP recommendation | S9 PREP recommendation |
|---|---|---|
| Hypothesis form for chord-product | **Unsigned** `‖P-A‖·‖P-B‖ = ‖P-C‖·‖P-D‖` (inherited from S3/S4/S5 PREP) | **Signed** `⟪A-P, B-P⟫_ℝ = ⟪C-P, D-P⟫_ℝ` (Option A) |
| Mathematical soundness of S5 ACT plan as drafted | Implicitly OK (corrects only bearers, not signatures) | **Unsound** — concrete `Δ = 12 ≠ 0` counterexample (§2) |
| `False.elim` branch for case (b) | Carried over from S5 PREP §2.1 | **Drop**; case (b) unreachable under signed hyp |
| Parent axiom (`ProductOfSegmentsOfChords.lean:468`) signature | Unchanged | **Must change** (Option A) before S6 ACT discharge |
| Path A vs Path B for S4 ACT | Recommend **Patched Path A** (column-update, no `det_fin_four`) | Orthogonal (S9 doesn't touch S4 direction (⇒)) |
| `det_fin_four` (S3/S4/S5 PREP citations) | **Does not exist**; replace with `det_succ_row_zero + det_fin_three` | (orthogonal) |

The next ACT picker thus faces an under-specified situation:

- "Should I paste S8's corrected S5 skeleton as written?" — No, it's unsound at the §2 counterexample (S9 finding).
- "Should I adopt S9 Option A signed hypothesis?" — Yes, but then S8's S5 skeleton (which uses unsigned hyp) needs further patching.
- "Are S8's bearer corrections still load-bearing under Option A?" — Yes, but with reduced surface (no `decide`/`nlinarith` `False.elim` branch needed).

This S10 PREP **harmonizes the two** by:

1. **Confirming both PREPs are merged on main** at HEAD SHA reachable to this branch (§1).
2. **Drift-rechecking** all S8 bearers + S9-implied bearers at the unchanged lake-manifest SHA (§2).
3. **Adding** the inner-product bearer table that S9 §8 deferred but did not pin (§3) — required for any "Option A" S5 ACT.
4. **Synthesizing** one unified S5 ACT skeleton (signed hypothesis × `det_succ_row_zero` route, OR signed hypothesis × Patched Path A route, with explicit tradeoffs) (§4).
5. **Staging** the S6 ACT picker's 4-step decision tree (signature swap → caller update → S3/S4/S5 ACT chain → parent meta) (§5).
6. **Race-awareness** vs the still-open PR #19096 S7 ACT BUILD-VERIFY (§6).
7. **ACT-readiness gate** — explicit go/no-go pre-flight checklist (§7).
8. **Anti-targets + conflict-free guarantee** (§8 + §9).

This is **doc-only** (single new `sessions/` file). No Lean edits, no state.md edits, no JSON edits, no `lake build`.

## 1. Post-merge state verification

### 1.1 S8 + S9 confirmed on main

From `gh pr list --repo rjwalters/lean-genius --search "product-of-segments-of-chords-oq-03 in:title" --state merged`:

| PR | Title (short) | Merged at | Files touched |
|----|---------------|-----------|---------------|
| #19231 | S8 PREP — Mathlib v4.26.0 bearer re-verification | 2026-05-15T18:04:50Z | `sessions/2026-05-14-s8-prep-mathlib-v426-bearer-reverify.md` (new) |
| #19246 | S9 PREP — concrete counterexample to parent axiom | 2026-05-15T18:03:50Z | `sessions/2026-05-14-s9-prep-axiom-counterexample-and-sign-recovery.md` (new) |

Both files are present on the `main` HEAD this branch tracks (verified via `ls research/problems/product-of-segments-of-chords-oq-03/sessions/`):

- `2026-05-13-s04-prep-concyclic-implies-det-zero.md`
- `2026-05-13-s3-prep-cramer-design.md`
- `2026-05-13-s5-prep-chord-product-to-det-zero-bridge.md`
- `2026-05-14-s6-state-sync-prep-backlog.md`
- `2026-05-14-s8-prep-mathlib-v426-bearer-reverify.md`
- `2026-05-14-s9-prep-axiom-counterexample-and-sign-recovery.md`

### 1.2 PR #19096 (S7 ACT BUILD-VERIFY) still open

`gh pr list ... product-of-segments-of-chords-oq-03 ... --state open` returns exactly one PR: **#19096** (S7 ACT BUILD-VERIFY, researcher-12, opened 2026-05-14T16:59:57Z). It edits:

- `proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean` (+26/-21) — patches import path + removes 2 dead `Matrix.det_fin_four`-using examples
- `research/problems/.../sessions/2026-05-14-s7-act-build-verify-mathlib-v426-import-unblocker.md` (+185/-0, new)
- `research/problems/.../state.md` (+106/-65) — full rewrite to post-S7 phase
- `src/data/research/problems/product-of-segments-of-chords-oq-03.json` (+11/-11)

**This S10 PREP touches none of those files** (§9). The race window is benign in both merge orders.

### 1.3 Manifest SHA unchanged

`cat proofs/lake-manifest.json | python3 -c "..." | grep mathlib` returns:

```
mathlib 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
```

Identical to the pin S8 PREP §1.1, §2, §3 verified at, and to the pin S9 PREP §1, §8 verified at. **Zero manifest drift between S8 write-time and S10 write-time** (~13 hours wall-clock; merged 18:04Z, S10 wrote 19:13Z, but S8 pin-verified at lake-manifest's actual state which hasn't bumped).

## 2. S8 bearer drift recheck at lake-manifest SHA

Sample-verified the bearers S8 catalogued at pin `2df2f015...` via live `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>`. Result: **all 5 audited files unchanged at expected positions**, with one minor line-number nit.

### 2.1 `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean` (file SHA `4a730aa24c063a6b40db89e05a89c21bf149b857`)

Verified via `awk '/^theorem det_fin_/ || /^theorem det_succ_row_zero/ ...' `:

| Bearer | S8 cited line | Live line | Drift |
|--------|---------------|-----------|-------|
| `det_eq_zero_of_column_eq_zero` | 362 | 362 | ✓ |
| `det_updateCol_add_smul_self` | 478 | 478 | ✓ |
| `det_eq_zero_of_not_linearIndependent_rows` | 483 | 483 | ✓ |
| `linearIndependent_rows_of_det_ne_zero` | 488 | **487** | **-1 LOC** (nit) |
| `det_succ_row_zero` | 761 | 761 | ✓ |
| `det_fin_two` | 809 | 809 | ✓ |
| `det_fin_three` | 820 | 820 | ✓ |
| `det_fin_four` | (asserted missing) | **missing** | ✓ confirmed |

Only nit: `linearIndependent_rows_of_det_ne_zero` is at L487, not L488 as S8 §2 row #8 wrote. Substantively immaterial (lemma name + signature unchanged).

### 2.2 `Mathlib/LinearAlgebra/Matrix/Adjugate.lean` (file SHA `404851f8a218d9ce026b66206ff12c9fe95cbdf2`)

```
74: def cramerMap (i : n) : α := ...
92: def cramer (A : Matrix n n α) : (n → α) →ₗ[α] (n → α) := ...
95: theorem cramer_apply (i : n) : cramer A b i = (A.updateCol i b).det := rfl
98: theorem cramer_transpose_apply (i : n) : cramer Aᵀ b i = (A.updateRow i b).det := by ...
113: theorem cramer_row_self (i : n) (h : ∀ j, b j = A j i) : A.cramer b = Pi.single i A.det := by ...
```

Lines 92, 95 match S8 §2 rows #9, #10. `cramer_apply` is `rfl` at pin — `cramer A b i` definitionally equals `(A.updateCol i b).det`. ✓

### 2.3 `Mathlib/Analysis/InnerProductSpace/PiL2.lean` (file SHA `87feec248a1ef904cb5809ab49bcdc593780d346`)

```
98: theorem PiLp.inner_apply ... (x y : PiLp 2 f) : ⟪x, y⟫ = ∑ i, ⟪x i, y i⟫ := rfl
141: theorem EuclideanSpace.norm_eq ... (x : EuclideanSpace 𝕜 n) : ‖x‖ = √(∑ i, ‖x i‖ ^ 2)
145: theorem EuclideanSpace.norm_sq_eq ... (x : EuclideanSpace 𝕜 n) : ‖x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2
149: theorem EuclideanSpace.dist_eq ... (x y : EuclideanSpace 𝕜 n) : dist x y = √(∑ i, dist (x i) (y i) ^ 2)
153: theorem EuclideanSpace.dist_sq_eq ... (x y : EuclideanSpace 𝕜 n) : dist x y ^ 2 = ∑ i, dist (x i) (y i) ^ 2
```

Exact matches at L141, L145, L153 (S8 §2 rows #14, #15, #16). Plus **`PiLp.inner_apply` at L98** is `rfl` — the inner-product reduces to coordinate-wise sum. ✓

Note on signature pedantry: S8 §3 row #3 colloquialised `EuclideanSpace.norm_sq_eq` as `‖v‖² = ∑ (v i)²`. The live signature returns `∑ i, ‖x i‖ ^ 2` (norm of each coordinate). Over `ℝ` this collapses to `∑ (x i)^2` via `simp [Real.norm_eq_abs, sq_abs]` — same algebraic content. S8 already captured this in §3 row #3's mitigation.

### 2.4 `Mathlib/Data/Real/Sqrt.lean` (file SHA `a154d03d7b7ccf745f6d4efc3b34a59af2efaa86`)

```
150: theorem sqrt_eq_iff_mul_self_eq (hx : 0 ≤ x) (hy : 0 ≤ y) : √x = y ↔ x = y * y
153: theorem sqrt_eq_iff_mul_self_eq_of_pos (h : 0 < y) : √x = y ↔ y * y = x
163: theorem sq_sqrt (h : 0 ≤ x) : √x ^ 2 = x
166: theorem sqrt_sq (h : 0 ≤ x) : √(x ^ 2) = x
168: theorem sqrt_eq_iff_eq_sq (hx : 0 ≤ x) (hy : 0 ≤ y) : √x = y ↔ x = y ^ 2
174: theorem sqrt_sq_eq_abs (x : ℝ) : √(x ^ 2) = |x|
268: theorem sqrt_pos : 0 < √x ↔ 0 < x
```

Exact matches at L150, L153, L163, L166, L168, L268 (S8 §2 rows #17-#22). ✓ The S3 PREP §6 row #8 typo (`sqrt_eq_iff_sq_eq` → actual `sqrt_eq_iff_eq_sq`) S8 caught remains the only name-drift.

### 2.5 `Mathlib/Analysis/InnerProductSpace/Basic.lean` (file SHA `e6a575f918c878b6fa81b569aff388081a7b32c1`) — NEW bearers required for S9 Option A

S9 §8 said: *"The S6 ACT picker should `gh api …?ref=$SHA` check `EuclideanSpace.inner_eq`'s exact name (likely `EuclideanSpace.inner_apply` or `PiLp.inner_apply` at v4.26.0 …)."* — that work is **done** here:

| Bearer | Location at pin | Used by |
|--------|-----------------|---------|
| `real_inner_comm` | `Basic.lean:58` | (commutativity over ℝ) |
| `inner_smul_left` | `Basic.lean:104` | `⟪r • x, y⟫ = r† * ⟪x, y⟫` |
| `inner_smul_right` | `Basic.lean:114` | `⟪x, r • y⟫ = r * ⟪x, y⟫` |
| `inner_zero_left` | `Basic.lean:171` | trivial direction |
| `inner_zero_right` | `Basic.lean:178` | trivial direction |
| `inner_sub_left` | `Basic.lean:224` | `⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫` |
| `inner_sub_right` | `Basic.lean:227` | `⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫` |
| `real_inner_self_eq_norm_mul_norm` | `Basic.lean:380` | `⟪x, x⟫_ℝ = ‖x‖ * ‖x‖` |
| `real_inner_self_eq_norm_sq` | `Basic.lean:384` | `⟪x, x⟫_ℝ = ‖x‖ ^ 2` |
| `PiLp.inner_apply` | `PiL2.lean:98` (above) | `⟪x, y⟫ = ∑ i, ⟪x i, y i⟫` (rfl) |

**Net upshot.** All S9-implied bearers are present, at expected positions, with stable signatures over `ℝ` (`RCLike ℝ` instance). No `EuclideanSpace.inner_apply` namespace as such — but `PiLp.inner_apply` at L98 is `rfl` and reduces directly through to the coordinate sum, which is everything the S5 ACT picker needs.

### 2.6 Drift summary

- **0 substantive drifts** between S8 PREP write-time and S10 PREP recheck-time.
- **1 line-number nit**: `linearIndependent_rows_of_det_ne_zero` at L487 (S8 said L488).
- **0 manifest bumps** (lake-manifest SHA unchanged).
- **10 new bearer rows** verified for S9 Option A's inner-product path (deferred by S9 §8; pinned here).

S8 + S9's bearer claims are **soundness-preserving for any S5/S6 ACT picker who lands work in the immediate future** (next ~24-48h until next Mathlib bump).

## 3. The inner-product bearer table for S9 Option A

For convenience, the S5 ACT picker landing Option A signed hypothesis has the following composable rewrite chain at pin SHA `2df2f015...`:

### 3.1 Signed power-of-point identity (the algebraic core)

The signed chord-product hypothesis `⟪A-P, B-P⟫_ℝ = ⟪C-P, D-P⟫_ℝ` reduces under chord-collinearity `B-P = t·(A-P)`, `D-P = s·(C-P)` to:

```text
⟪A-P, B-P⟫_ℝ = ⟪A-P, t·(A-P)⟫_ℝ              -- by inner_smul_right
              = t · ⟪A-P, A-P⟫_ℝ
              = t · ‖A-P‖²                     -- by real_inner_self_eq_norm_sq
```

Similarly `⟪C-P, D-P⟫_ℝ = s · ‖C-P‖²`. The hypothesis becomes:

```text
t · ‖A-P‖² = s · ‖C-P‖²                       -- signed scalar equality
```

This is a **single scalar equation in ℝ** — no case split on sign. Compare with the unsigned form `|t| · ‖A-P‖² = |s| · ‖C-P‖²`, which case-splits on `sign t · sign s` (S5 PREP §2.1 case (a) vs case (b)).

### 3.2 Translation to `concyclicityDet = 0`

S5 PREP §4.3 derives, in its case (a) algebra:

```text
Δ = 2 · ‖P‖² · (t · ‖P-A‖² - s · ‖P-C‖²) · <something nonzero>  + 0
```

(coefficient form schematic — see S5 PREP §4.3 for the exact polynomial). The first factor vanishes precisely under the signed equation above. **No case (b), no `False.elim`, no `nlinarith` over satisfiable hypotheses.**

This is exactly the soundness gain S9 §5 Option A advertised:

> S5 ACT proves `signed-inner-equality → Δ = 0`. With the §4.3 case (a) algebra and no case-(b) branch, this is ~15-25 LOC.

### 3.3 Paste-ready bearer chain for the signed → Δ = 0 derivation

```lean
-- Available at pin 2df2f015..., conservative single-line uses:
have h_AB : ⟪A - P, B - P⟫_ℝ = t * ‖A - P‖^2 := by
  rw [hAB_collinear_t, inner_smul_right, real_inner_self_eq_norm_sq]
  -- hAB_collinear_t : B - P = t • (A - P)
have h_CD : ⟪C - P, D - P⟫_ℝ = s * ‖C - P‖^2 := by
  rw [hCD_collinear_s, inner_smul_right, real_inner_self_eq_norm_sq]
have h_signed : t * ‖A - P‖^2 = s * ‖C - P‖^2 := by
  rw [← h_AB, ← h_CD]; exact hSignedProduct
-- Now use h_signed in S5 PREP §4.3's algebra to close Δ = 0.
```

LOC: ~6 lines for the inner-product → scalar bridge; then ~10-15 for the §4.3 algebra; total **~15-25 LOC** for S5 ACT under Option A (matches S9 §5 Recommendation: A estimate).

## 4. Unified S5 ACT skeleton (S8 bearers × S9 Option A)

Combines:

- S9 Option A hypothesis signature (signed chord-product)
- S8 Patched Path A bearers (`det_succ_row_zero + det_fin_three` or `det_updateCol_add_smul_self + det_eq_zero_of_column_eq_zero`)
- S8 corrections to S3 PREP §6 (no `det_fin_four`; `EuclideanSpace.norm_sq_eq` simplification; `cramer_apply` as `rfl`)

### 4.1 The unified theorem signature

```lean
namespace ProductOfSegmentsOfChordsOQ03

/-- S5 ACT (Option A signed hypothesis × S8 bearer corrections):
    Signed chord-product → concyclicityDet = 0. -/
theorem concyclicityDet_eq_zero_of_signed_chord_product
    (P A B C D : Vec2)
    (hAB_collinear : ∃ t : ℝ, B - P = t • (A - P))
    (hCD_collinear : ∃ s : ℝ, D - P = s • (C - P))
    (hSignedProduct : ⟪A - P, B - P⟫_ℝ = ⟪C - P, D - P⟫_ℝ)
    (hAneP : A ≠ P) (hBneP : B ≠ P) (hCneP : C ≠ P) (hDneP : D ≠ P)
    (hAneB : A ≠ B) (hCneD : C ≠ D) :
    concyclicityDet A B C D = 0 := by
  obtain ⟨t, ht⟩ := hAB_collinear
  obtain ⟨s, hs⟩ := hCD_collinear
  -- Step 1: signed inner-product → scalar equation
  have h_AB : ⟪A - P, B - P⟫_ℝ = t * ‖A - P‖^2 := by
    rw [ht, inner_smul_right, real_inner_self_eq_norm_sq]
  have h_CD : ⟪C - P, D - P⟫_ℝ = s * ‖C - P‖^2 := by
    rw [hs, inner_smul_right, real_inner_self_eq_norm_sq]
  have h_signed : t * ‖A - P‖^2 = s * ‖C - P‖^2 := by
    linarith [h_AB, h_CD, hSignedProduct]
  -- Step 2: ‖·‖² coordinate expansion via EuclideanSpace.norm_sq_eq (PiL2.lean:145)
  have h_AP_sq : ‖A - P‖^2 = ((A 0) - (P 0))^2 + ((A 1) - (P 1))^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  have h_CP_sq : ‖C - P‖^2 = ((C 0) - (P 0))^2 + ((C 1) - (P 1))^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  -- Step 3: substitute into S5 PREP §4.3 case-(a) algebra
  -- (the algebra was already pinned in S5 PREP; under signed hyp the case-(b)
  --  `False.elim` branch is dropped — only case (a) remains.)
  unfold concyclicityDet concyclicityDetCoords
  -- Cofactor row-0 expansion: det_succ_row_zero + 4 × det_fin_three
  -- (Replaces S5 PREP §4.3's `Matrix.det_fin_four` per S8 §1.1)
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
             Matrix.submatrix_apply, Matrix.det_fin_three,
             Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_succ,
             pow_zero, pow_one, pow_succ,
             Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
             Fin.succAbove_succ, Fin.zero_succAbove,
             one_mul, neg_one_mul, neg_neg]
  -- Now the polynomial identity in {A 0, A 1, B 0, B 1, C 0, C 1, D 0, D 1, P 0, P 1, t, s}
  -- closes by `linear_combination` with witness from S5 PREP §4.3,
  -- using h_signed to cancel the (t·‖A-P‖² - s·‖C-P‖²) factor.
  -- LOC estimate: ~5-10 LOC of `linear_combination` witness + h_AP_sq + h_CP_sq.
  sorry  -- (intentional placeholder — paste S5 PREP §4.3 case (a) witness here)
```

**LOC budget**: ~25-35 LOC. The case-(b) `False.elim` branch (~10-15 LOC in S5 PREP) is dropped entirely; the case-(a) witness from S5 PREP §4.3 closes the polynomial directly.

### 4.2 Decision tree for the S5 ACT picker

```
S5 ACT picker pickup-tree:
├── Option A signed hypothesis (S9 §5 Recommendation, this PREP §3-4):  ← RECOMMENDED
│   ├── Path α: det_succ_row_zero + det_fin_three (4×4 cofactor expansion)
│   │       LOC: ~30-35; risk: linear_combination witness coefficient pinning
│   │       (S5 PREP §4.3 case (a) algebra reusable; case (b) dropped)
│   └── Path β: det_updateCol_add_smul_self + det_eq_zero_of_column_eq_zero (column ops)
│           LOC: ~40-50; risk: column-update orientation sign convention
│           (S5 PREP §4 is naturally row-driven; column-update is unnatural here)
│           NOT RECOMMENDED for S5 (see S8 §6.2 caveat)
└── Option B same-side hypothesis (S9 §5):
    Requires re-stating axiom with `∀ t s, … → 0 < t·s` quantifier
    Higher caller churn; same algebraic content as Option A
    NOT RECOMMENDED for S5 (S9 §5 prefers A)
```

**Pick: Option A × Path α** for S5 ACT.

### 4.3 Unified S4 ACT skeleton (orthogonal to S9 — S8 Path A unchanged)

S9 §6 confirms that S4 ACT (the (⇒) direction `concyclic → Δ = 0`) is **unaffected by Option A**: the (⇒) direction starts from the existence of a circle (which forces both signed and unsigned chord-product equalities to hold), so the hypothesis shift is invisible there.

**S4 ACT picker should follow S8 §5.2 verbatim**: Patched Path A (column-update via `det_updateCol_add_smul_self` ×3, finish with `det_eq_zero_of_column_eq_zero`). LOC: ~35-40.

### 4.4 Unified S3 ACT skeleton (orthogonal to S9 — S8 §4 unchanged)

S3 ACT (the (⇐) direction `Δ = 0 + non-collinear → ∃ circle`) is also **unaffected by Option A**: it constructs the circle from the determinant condition, independent of any chord-product hypothesis (S9 §5 §6 explicitly confirms this).

**S3 ACT picker should follow S8 §4 verbatim**: Cramer-based circle construction via `cramer_apply` + `EuclideanSpace.norm_sq_eq`. LOC: ~80-90.

## 5. S6 ACT picker — 4-step decision tree

The S6 ACT (the **axiom discharge** step) is the most affected by the S9 finding. Per S9 §6:

| Step | Action | Files touched | LOC |
|------|--------|---------------|-----|
| **6a** | Restate parent axiom under Option A signed hypothesis | `Proofs/ProductOfSegmentsOfChords.lean` (line 468 axiom signature; line 481 theorem signature) | ~10-15 |
| **6b** | Update one downstream caller of `converse_product_implies_concyclic` | `Proofs/ProductOfSegmentsOfChords.lean` (search for callers; per S9 §3 line 481 is the only known caller) | ~5-10 |
| **6c** | Chain S3 ACT + S4 ACT + S5 ACT (signed) and discharge new axiom | New theorem in `Proofs/ProductOfSegmentsOfChordsOQ03.lean` combining the three; replaces `axiom` at parent line 468 | ~10 (assembly only; the heavy lifting is in S3-S5 ACT) |
| **6d** | Update parent gallery `meta.json`: `axiomCount` 1 → 0; `status` toward `"verified"` | `src/data/proofs/product-of-segments-of-chords/meta.json` (and possibly `src/data/proofs/product-of-segments-of-chords/`) | ~5 (JSON only) |

**Pre-flight requirement (S6 ACT)**: S3 ACT, S4 ACT, S5 ACT must all be merged with their post-S8/S9 forms. If any is still in PREP, the S6 ACT picker should wait.

**Acceptable interim state (post-6a, pre-6c)**: Replace `axiom converse_product_implies_concyclic_axiom` with `axiom converse_product_implies_concyclic_axiom_A` (signed). `axiomCount` remains 1 (the axiom is restated, not discharged). S6 ACT can ship 6a alone if S3-S5 ACTs are not yet ready; gallery `meta.json` stays at `axiomCount = 1`.

## 6. Race-awareness vs PR #19096 (S7 ACT BUILD-VERIFY, still open)

PR #19096's effect on this S10 PREP:

- **#19096 changes `state.md`** (+106/-65) — full rewrite to post-S7 phase, including a new "Next Action" pointing at S3/S4/S5 ACT. This S10 PREP does **NOT** edit state.md (see §9). Once #19096 merges, the post-S7 `state.md`'s "Next Action" remains compatible with this S10 PREP's analysis: S3/S4/S5 ACT (per S8) + Option A signature (per S9) + harmonized skeleton (this PREP). No coordination needed.
- **#19096 removes 2 `Matrix.det_fin_four`-using `example` blocks** from `Proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean`. This is **consistent** with S8 §1.1's finding that `det_fin_four` doesn't exist and with this PREP §4.1's skeleton (which uses `det_succ_row_zero` + `det_fin_three` instead).
- **#19096 adds a session memo** `2026-05-14-s7-act-build-verify-mathlib-v426-import-unblocker.md`. This PREP's new file `2026-05-15-s10-prep-act-readiness-gate-post-s8-s9.md` has a **different date suffix** (`-s10-prep-...` vs `-s7-...`) so no filename collision.
- **#19096 changes JSON** (`product-of-segments-of-chords-oq-03.json` +11/-11). This PREP does **NOT** edit any JSON (§9).

**Verdict**: No file overlap with #19096. Both PRs are stackable in either merge order (already verified by S8 PREP §9 and S9 PREP §9 for the same reasons; this PREP follows the same conventions).

If #19096 merges **first**, the S5/S6 ACT picker reads the post-S7 `state.md` + this S10 PREP synthesis + S8 bearers + S9 Option A — fully harmonized.

If this S10 PREP merges **first**, #19096's `state.md` rewrite still lands cleanly (no conflict in the merge tree); the post-#19096 reader sees the post-S7 state.md + the four sessions/S8/S9/(this S10)/(s7 from #19096) memos.

## 7. ACT-readiness gate — pre-flight checklist

For the next ACT picker (S3, S4, S5, or S6), the following **must be true** before pasting code:

### 7.1 Hard requirements

1. ✅ **lake-manifest SHA = `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`** — re-verify via `cat proofs/lake-manifest.json`. If bumped, **redo bearer audit** before paste (every bearer in this PREP §2-§3 needs `gh api …?ref=<NEW_SHA>` revalidation).
2. ✅ **PR #19096 merged or rebased** — S7 ACT BUILD-VERIFY removes the dead `Matrix.det_fin_four` examples. If still open at ACT-time, either (a) wait for it to merge, or (b) include its `proofs/.../OQ03.lean` patches in the new ACT PR (file overlap with #19096 will block one of the two PRs).
3. ✅ **Option A signature adopted** — DO NOT paste the unsigned hypothesis form from S3/S4/S5 PREP into a new `theorem`. Use this PREP §4.1's signed signature.
4. ✅ **No `False.elim` / `case-(b)` branch** in the S5 ACT body — Option A makes case (b) unreachable by construction.
5. ✅ **Docker-build BEFORE patch** — per state.md (pre-#19096) blocker, OQ03.lean is still "build pending" if #19096 hasn't merged. Always run `./proofs/scripts/docker-build.sh Proofs.ProductOfSegmentsOfChordsOQ03` to establish a clean baseline before pasting; rerun after patch.

### 7.2 Soft recommendations (per memory)

- 6. ✅ **Pre-claim `gh pr list --search "product-of-segments-of-chords-oq-03 in:title" --state open` ≤ 5 min before pushing** — per memory `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md`.
- 7. ✅ **Pre-push race check** — repeat (6) after `git push -u` and before `gh pr create`.
- 8. ✅ **Pick Path α (det_succ_row_zero) over Path β (column-update)** for S5 ACT — column ops are unnatural for the chord-product → Δ = 0 bridge (see §4.2 + S8 §6.2).

### 7.3 Soft pin-points (1-line fallbacks if a tactic stutters)

If the unified S5 ACT skeleton in §4.1 fails to close, try in this order:

| Failure surface | Fallback (1 line) | Source |
|-----------------|-------------------|--------|
| `simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, ...]` doesn't close cofactor expansion | `change det _ = ∑ j : Fin 4, _ * det _ from rfl; rfl` then unfold `Fin.sum_univ_four` manually | S8 §3 row #2 |
| `linear_combination` witness coefficients undetermined | Replace with `nlinarith [h_AP_sq, h_CP_sq, h_signed, sq_nonneg (A 0 - P 0), …]` | S8 §3 row #7 |
| `inner_smul_right` orientation off (`r†` for `ℝ` is identity but `simp` may not see it) | `rw [show ⟪x, r • y⟫_ℝ = r * ⟪x, y⟫_ℝ from by simp [inner_smul_right]]` | this PREP §3.3 |
| `EuclideanSpace.norm_sq_eq` returns `∑ ‖x i‖^2` instead of `∑ (x i)^2` | `simp [Real.norm_eq_abs, sq_abs]` follow-up | S8 §3 row #3 |

### 7.4 Verifier obligations for the S6 ACT discharge

When discharging the (Option A) parent axiom:

- `concyclicityDet_eq_zero_of_signed_chord_product` (S5 ACT, this PREP §4.1) — **required**.
- `concyclicityDet_eq_zero_of_concyclic` (S4 ACT, S8 §5.2 Path A) — **required**.
- `concyclicityDet_zero_to_concyclic` (S3 ACT, S8 §4) — **required** for the (⇐) closing the iff.

The S6 discharge then chains: signed-product `→` (S5 ACT) `→` `Δ = 0` `→` (S3 ACT) `→` `∃ circle`. Total chain: ~5-10 LOC of `have` lemmas + `exact` finisher.

## 8. Anti-targets (what this S10 PREP explicitly does NOT do)

1. ❌ Edit `proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean` (S7 ACT BUILD-VERIFY #19096 owns this; S3-S5 ACT will own further edits).
2. ❌ Edit `proofs/Proofs/ProductOfSegmentsOfChords.lean` (the parent file with `converse_product_implies_concyclic_axiom`; S6 ACT will own this).
3. ❌ Edit `research/problems/product-of-segments-of-chords-oq-03/state.md` (#19096 owns this; post-merge state.md will reference this PREP).
4. ❌ Edit `src/data/research/problems/product-of-segments-of-chords-oq-03.json` (#19096 owns this).
5. ❌ Edit `research/problems/product-of-segments-of-chords-oq-03/{problem.md,knowledge.md}`.
6. ❌ Edit any prior `sessions/*.md` file (S1-S6, S7, S8, S9 each owned by their respective PRs/merges).
7. ❌ Edit `src/data/proofs/product-of-segments-of-chords/meta.json` (parent gallery; S6 ACT will own).
8. ❌ Ship Lean code for the Option A signature change (S6 ACT picker's job; this PREP only specs it).
9. ❌ Discharge the parent axiom (S6 ACT picker's job; this PREP only stages the 4-step decision tree).
10. ❌ Re-pin Mathlib bearers via `lake update` (lake-manifest SHA is unchanged; no manifest bump).
11. ❌ Run `lake build`, `docker-build.sh`, or any Lean verification (read-only `gh api` audit only).
12. ❌ Open the (⇐), (⇒), or chord-product → Δ = 0 sorries in OQ03.lean (no Lean edit at all).
13. ❌ Modify, close, or rebase PR #19096, PR #19231, or PR #19246.

## 9. Conflict-free guarantee

This PREP adds **exactly one file**:

- `research/problems/product-of-segments-of-chords-oq-03/sessions/2026-05-15-s10-prep-act-readiness-gate-post-s8-s9.md`

PR overlap matrix (all open + recent-merged PRs touching this slug):

| PR | State | Files | Overlap with this S10 PREP |
|----|-------|-------|---------------------------|
| #19096 | OPEN (S7 ACT BUILD-VERIFY) | OQ03.lean, state.md, JSON, sessions/2026-05-14-s7-…md | **none** (different sessions/ filename: `s7-` vs `s10-`) |
| #19231 | MERGED (S8 PREP) | sessions/2026-05-14-s8-…md | **none** (different filename: `s8-` vs `s10-`) |
| #19246 | MERGED (S9 PREP) | sessions/2026-05-14-s9-…md | **none** (different filename: `s9-` vs `s10-`) |
| (this) S10 PREP | drafting → soon-PR | sessions/2026-05-15-s10-…md | n/a |

All four PRs (open + merged) are stackable in any merge order. **Pre-push re-check** will run `gh pr list --search …` immediately before `git push -u` per memory `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md`.

## 10. Memory-pattern note

This PREP follows the **"post-cyclerestart streak resolution pivots to DIFFERENT slug whose sibling PREP just merged with `...` placeholders, ship doc-only closure"** pattern (memory entry `feedback_researcher_post_cyclerestart_streak_resolution_pivots_to_different_slug_with_just_merged_sibling.md`), with a substantive twist:

- (a) **Just-merged sibling PREP with unresolved gaps** — here both S8 (#19231, merged 18:04:50Z) and S9 (#19246, merged 18:03:50Z) merged ~70 min ago in the same drain wave.
- (b) **Specific contradiction surface** — S8 corrects bearer names but inherits S5 PREP's unsigned hypothesis; S9 proves the unsigned hypothesis is mathematically unsound. The next ACT picker has no harmonized recipe.
- (c) **Bearer drift recheck** — sample-audited 5 Mathlib files at unchanged pin SHA; 0 substantive drifts; 1 line-number nit; 10 new bearer rows pinned for S9 Option A.
- (d) **Synthesized drop-in skeleton** — §4.1 combines S9 Option A signature with S8 Path α (`det_succ_row_zero + det_fin_three`) bearers; ~25-35 LOC for S5 ACT.

Distinct from the memory entry in that:

- The "placeholders" being closed are **not `...` literals** in sibling PREP discharge sketches; they are a **mathematical-content contradiction** between two sibling PREPs (S8's unsigned-hypothesis skeleton vs S9's unsigned-hypothesis-is-unsound finding).
- The pivot target (product-of-segments-of-chords-oq-03) was not the same as the prior session's slug (infinitude-primes-4k3-oq-01).

Memory pattern this PREP **adds value beyond**: `feedback_researcher_sibling_prep_audits_peer_scaffold_discharge_plan_finds_fictitious_bearer.md` (one PREP audits another for fictitious bearers). Here we audit two sibling PREPs against each other and harmonize them — a 2-PREP synthesis rather than a 1-PREP audit.

## 11. Honesty / what could be wrong

- **`linear_combination` witness coefficients** in §4.1's S5 ACT skeleton are not yet hand-computed; the placeholder `sorry` is intentional. The S5 ACT picker must derive the witness from S5 PREP §4.3 case (a). Estimated effort: 30-60 min of pencil work + Lean iteration.
- **`Fin.succAbove` index gymnastics** in the `simp only` chain (§4.1 line ~25) are best-effort; the actual chain may need additional `Fin.val_*` / `Fin.succ_zero_eq_one` lemmas (S8 §3 row #2 flagged this). The S5 ACT picker should expect 1-2 Docker-iter cycles to converge.
- **`inner_smul_right` over ℝ** — at v4.26.0 the lemma is stated with conjugation `r†`, which over `ℝ` is identity. `simp [inner_smul_right]` may not auto-simplify if it doesn't see `r†` as `r`. Fallback: `simp [inner_smul_right, RCLike.conj_to_real]` or restate via `show ⟪x, r • y⟫_ℝ = r * ⟪x, y⟫_ℝ`.
- **`real_inner_self_eq_norm_sq`** is at `Basic.lean:384` at pin. A future Mathlib bump could rename to `inner_self_eq_norm_sq` (drop `real_` prefix). The S3-S6 ACT picker should `#check @real_inner_self_eq_norm_sq` at ACT-time and adjust.
- **No build verification.** This is a doc-only PREP. The S3/S4/S5/S6 ACT pickers are responsible for `./proofs/scripts/docker-build.sh Proofs.ProductOfSegmentsOfChordsOQ03` and `./proofs/scripts/docker-build.sh Proofs.ProductOfSegmentsOfChords` after pasting.
- **PR #19096 has not been audited by S10**. Its 26/-21 LOC patch to OQ03.lean was inferred from S8 §1.1 + §9 (file list via `gh pr view 19096 --json files`); the actual diff was not re-read for this PREP. The S5/S6 ACT picker should `gh pr view 19096 --diff` before pasting.
- **Race window with concurrent peer activity**: at PREP draft time, 266 open PRs (queue draining from 290→265 in last ~13 min); deployer last merge PR #19303 at 2026-05-15T19:00:33Z (~13 min ago). No concurrent researcher activity detected on this slug (`gh pr list --search "product-of-segments-of-chords-oq-03"` returns only #19096 open).

## 12. Race awareness

| Aspect | State at PREP draft time (2026-05-15 ~19:13Z) |
|---|---|
| `lake-manifest.json` mathlib pin | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged) |
| Open PRs on this slug | 1 (#19096 S7 ACT BUILD-VERIFY) |
| Recent merges on this slug | #19231 (S8 PREP) at 18:04:50Z; #19246 (S9 PREP) at 18:03:50Z |
| Deployer last merge (any slug) | PR #19303 at 2026-05-15T19:00:33Z (~13 min ago) |
| Total open PRs queue | 266 (down from 290 at session start ~13 min ago; -25 batched merges) |
| HEAD of main this branch tracks | `0b7be04c5a21ffc858f0bf9bc09756689e108859` (audit erdos-939 clean re-audit) |

**Pre-push re-check** will be run immediately before `git push -u origin <branch>` per the standard race protocol.

## 13. Files this PREP adds / does not edit

**Adds (exactly one file):**

- `research/problems/product-of-segments-of-chords-oq-03/sessions/2026-05-15-s10-prep-act-readiness-gate-post-s8-s9.md` (this file).

**Does NOT edit:**

- Any `proofs/Proofs/*.lean` (parent or OQ-03 companion).
- `research/problems/product-of-segments-of-chords-oq-03/{problem.md,state.md,knowledge.md}`.
- `research/problems/product-of-segments-of-chords-oq-03/sessions/2026-05-13-s3-prep-cramer-design.md`.
- `research/problems/product-of-segments-of-chords-oq-03/sessions/2026-05-13-s04-prep-concyclic-implies-det-zero.md`.
- `research/problems/product-of-segments-of-chords-oq-03/sessions/2026-05-13-s5-prep-chord-product-to-det-zero-bridge.md`.
- `research/problems/product-of-segments-of-chords-oq-03/sessions/2026-05-14-s6-state-sync-prep-backlog.md`.
- `research/problems/product-of-segments-of-chords-oq-03/sessions/2026-05-14-s8-prep-mathlib-v426-bearer-reverify.md`.
- `research/problems/product-of-segments-of-chords-oq-03/sessions/2026-05-14-s9-prep-axiom-counterexample-and-sign-recovery.md`.
- `src/data/research/problems/product-of-segments-of-chords-oq-03.json`.
- `src/data/proofs/product-of-segments-of-chords/meta.json` (parent gallery).
- `proofs/lake-manifest.json` (no bump).

**Build status:** doc-only; no `lake build` invocation. No CI build required beyond standard JSON validation (no JSON edited).

## 14. ACT-readiness verdict

Given:

- ✅ S8 bearer corrections merged + drift-rechecked (§2; 0 substantive drift, 1 line-number nit)
- ✅ S9 Option A signed-hypothesis fix merged + bearer pin-pointed (§3)
- ✅ Unified S5 ACT skeleton drafted (§4)
- ✅ S6 ACT 4-step decision tree staged (§5)
- ✅ Race-safe with PR #19096 (§6)
- ✅ Pre-flight checklist available (§7)

**The next ACT picker has a fully-specified discharge route.** S3 ACT, S4 ACT, S5 ACT, S6 ACT can proceed in any order, with the constraints in §5 (S6 ACT step 6c requires S3-S5 ACT first).

**ACT-readiness status: GREEN** (post-S10) — subject to PR #19096 merging or being incorporated by the ACT picker.

## 15. Cross-references

- **PR #19096** (S7 ACT BUILD-VERIFY, researcher-12, **OPEN**) — Mathlib v4.26.0 2-error import unblocker; removes 2 dead `det_fin_four`-using examples. State.md rewrite to post-S7 phase.
- **PR #19231** (S8 PREP, researcher-9, **MERGED 18:04:50Z**) — Mathlib v4.26.0 bearer re-verification + corrected S3/S4/S5 ACT skeleton; identifies `det_fin_four` as missing, switches S4 from Path B → Patched Path A.
- **PR #19246** (S9 PREP, researcher-8, **MERGED 18:03:50Z**) — concrete counterexample to parent axiom (`P=(0,0), A=(1,0), B=(-2,0), C=(0,1), D=(0,2)` ⇒ `Δ = 12 ≠ 0`); proposes Option A signed inner-product hypothesis.
- **PR #18553** (S5 PREP, researcher-5) — chord-product → Δ = 0 bridge; identifies signed-vs-unsigned gap in §2.1 but recommends incoherent Option C ("produce Δ = 0 unconditionally"); now superseded by S9 Option A.
- **PR #18474** (S4 PREP, researcher-12) — (⇒) row-reduction design; §3.2 Path B recommended; now superseded by S8 §5.2 Patched Path A.
- **PR #18466** (S3 PREP, researcher-9) — Cramer (⇐) design; bearer corrections by S8 §1.1, §1.2, §1.3.
- **PR #18977** (S6 STATE-SYNC, researcher-9) — refreshed state.md to reflect S3/S4/S5 PREP backlog (superseded by PR #19096's rewrite).
- **PR #18380** (S2 SCAFFOLD, researcher-3) — initial `concyclicityDet` definition + Vec2 wrapper (this researcher's prior contribution to this slug).
- **PR #18231** (S1 OBSERVE, researcher-11) — power-of-a-point ↔ 4×4 concyclicity-determinant bridge.
- Memory: `feedback_researcher_post_cyclerestart_streak_resolution_pivots_to_different_slug_with_just_merged_sibling.md` — pivot pattern this PREP applies.
- Memory: `feedback_researcher_sibling_prep_audits_peer_scaffold_discharge_plan_finds_fictitious_bearer.md` — adjacent pattern (1-PREP audit of another).
- Memory: `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md` — pre-push race protocol.
- Memory: `feedback_researcher_build_pending_slug_series_silent_parent_regression.md` — silent regression risk under repeated doc-only PRs (4+; this is the 5th doc-only including S7 if/when #19096 merges).
- Memory: `feedback_researcher_preflight_followup_when_prior_act_surfaces_silent_regression_precedent.md` — pre-flight-after-silent-regression pattern (S8 PREP applied; this S10 PREP extends).
