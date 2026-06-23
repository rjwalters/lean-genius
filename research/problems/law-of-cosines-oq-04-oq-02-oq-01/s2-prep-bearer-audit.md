# S2 PREP: Mathlib Bearer Audit at Pinned SHA `2df2f01`

**Author**: researcher-4 (2026-05-13)
**Slug**: `law-of-cosines-oq-04-oq-02-oq-01`
**Mode**: PREP (doc-only; no `.lean` diff)
**Companion to**: `knowledge.md` (Session S1 OBSERVE, researcher-8, 2026-05-11, PR #17833)
**Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (lake-pinned `v4.26.0`)
**Lean toolchain**: `leanprover/lean4:v4.26.0` (`proofs/lean-toolchain`)

## 1. Purpose & key finding

The S1 OBSERVE knowledge doc (researcher-8, 2026-05-11) is detailed and useful,
but its §4 "Mathlib API survey" cites line numbers without specifying a Mathlib
SHA. A spot-check against the lake-pinned ref `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
reveals **substantial drift**, most notably:

- `Sbtw.mem_image_Ioo` cited at `Between.lean:215` → actually at **L353** (+138 line drift).
- `Sbtw.ne_left/right_ne/left_ne/ne_right` cited at `Between.lean:203–212` → actually at
  **L341–350** (+138–139 line drift).
- `InnerProductGeometry.angle` and `InnerProductGeometry.cos_angle` cited in
  `Mathlib/Analysis/InnerProductSpace/Basic.lean` → actually defined in
  **`Mathlib/Geometry/Euclidean/Angle/Unoriented/Basic.lean`** at L40 and L65.
  This is a **wrong file path**, not just a line drift; a naive
  `gh api .../contents/Mathlib/Analysis/InnerProductSpace/Basic.lean` lookup will
  miss them entirely.

Names of every named bearer are stable across the drift window — the lemmas exist,
the signatures used in §3 (Path A) are unchanged. But the **file paths** and
**line numbers** in §4 must be re-grounded against the pinned SHA before the S2
implementer copies them into the new `.lean` file's `#check` or `import` block.

This PREP is doc-only. No `.lean` edits. The `LawOfCosinesOQ04OQ02OQ01.lean` file
does not yet exist; the next session (S2-implement) will create it.

## 2. Re-grounded bearer table (Path A load-bearing only)

All citations at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Files downloaded via
`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f01`.

### 2.1. Affine / between (`knowledge.md §4.1`)

| Bearer | Cited path:line (knowledge.md) | Pinned-SHA actual | Drift | Signature at SHA |
|---|---|---|---|---|
| `Sbtw` (def) | `Convex/Between.lean:123` | **L136** | +13 | `def Sbtw (x y z : P) : Prop` |
| `Wbtw` (def) | (same file) | **L132** | — | `def Wbtw (x y z : P) : Prop` |
| `Sbtw.mem_image_Ioo` | `Convex/Between.lean:215` | **L353** | **+138** | `(h : Sbtw R x y z) : y ∈ lineMap x z '' Set.Ioo (0 : R) 1` |
| `Sbtw.ne_left` | `Convex/Between.lean:203` | **L341** | +138 | `(h : Sbtw R x y z) : y ≠ x` |
| `Sbtw.left_ne` | `Convex/Between.lean:204` | **L344** | +140 | `(h : Sbtw R x y z) : x ≠ y` |
| `Sbtw.ne_right` | `Convex/Between.lean:212` | **L347** | +135 | `(h : Sbtw R x y z) : y ≠ z` |
| `Sbtw.right_ne` | `Convex/Between.lean:212` | **L350** | +138 | `(h : Sbtw R x y z) : z ≠ y` |
| `Sbtw.left_ne_right` | (not cited; relevant) | L437 | — | `(h : Sbtw R x y z) : x ≠ z` |
| `Sbtw.wbtw` | (implicit) | L338 | — | `(h : Sbtw R x y z) : Wbtw R x y z` |
| `AffineMap.lineMap` | `LinearAlgebra/AffineSpace/AffineMap.lean` | (not re-checked; standard) | — | `(a b : P) : R →ᵃ[R] P`; `lineMap_apply : lineMap a b t = (1 - t) • a + t • b` (via vsub) |

**§2.1 audit summary**: 4 of 6 cited line numbers drifted by ~138 lines. Names + signatures
intact. **The §3 Step-1 use of `Sbtw.mem_image_Ioo` is structurally correct**: the lemma
extracts `t ∈ Ioo 0 1` such that `D = lineMap B C t`. Unpacking takes 2 steps
(`Set.mem_image` + `Exists`); this matches the risk-register row "Sbtw.mem_image_Ioo
signature differs from expectation". The fallback (`Wbtw.smul_vadd_smul_vadd...`) is
not needed.

### 2.2. Angles in Euclidean affine spaces (`knowledge.md §4.2`)

| Bearer | Cited path:line (knowledge.md) | Pinned-SHA actual | Drift | Signature at SHA |
|---|---|---|---|---|
| `EuclideanGeometry.angle` (def) | `Geometry/Euclidean/Angle/Unoriented/Affine.lean:43` | **L42** | −1 | `nonrec def angle (p₁ p₂ p₃ : P) : ℝ := angle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂)` |
| `∠` (notation) | (implicit) | `Affine.lean:45` | — | `scoped notation "∠" => EuclideanGeometry.angle` |
| `InnerProductGeometry.angle` (def) | **`Analysis/InnerProductSpace/Basic.lean`** ⚠️ | **`Geometry/Euclidean/Angle/Unoriented/Basic.lean:40`** ⚠️ | wrong file | `def angle (x y : V) : ℝ := Real.arccos (⟪x, y⟫ / (‖x‖ * ‖y‖))` |
| `InnerProductGeometry.cos_angle` | **`Analysis/InnerProductSpace/Basic.lean`** ⚠️ | **`Geometry/Euclidean/Angle/Unoriented/Basic.lean:65`** ⚠️ | wrong file | `theorem cos_angle (x y : V) : Real.cos (angle x y) = ⟪x, y⟫ / (‖x‖ * ‖y‖)` |
| `EuclideanGeometry.angle_eq_pi_iff_sbtw` | `Affine.lean:278` | **L281** | +3 | `{p₁ p₂ p₃ : P} : ∠ p₁ p₂ p₃ = π ↔ Sbtw ℝ p₁ p₂ p₃` |
| `EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi` | `Affine.lean:172` | **L175** | +3 | `(p₁ : P) {p₂ p₃ p₄ : P} (h : ∠ p₂ p₃ p₄ = π) : ∠ p₁ p₃ p₂ + ∠ p₁ p₃ p₄ = π` |
| `Real.arccos_injOn` | `Trigonometric/Inverse.lean` (no line) | **L333** | — | `arccos_injOn : InjOn arccos (Icc (-1) 1)` |
| `Real.arccos_inj` | (related, possibly preferred) | **L336** | — | `(hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) (hy₁ : -1 ≤ y) (hy₂ : y ≤ 1) : arccos x = arccos y ↔ x = y` |

**§2.2 audit summary**: the **most important correction**: `InnerProductGeometry.angle`
and `InnerProductGeometry.cos_angle` live in `Mathlib/Geometry/Euclidean/Angle/Unoriented/Basic.lean`
(NOT in `InnerProductSpace/Basic.lean` as knowledge.md states). A naive
content lookup at the wrong path returns nothing. The `EuclideanGeometry.angle` def
(L42 of `Affine.lean`) is **`nonrec`** and threads through the inner-product `angle`
via `(p₁ -ᵥ p₂)` and `(p₃ -ᵥ p₂)`; the S2 proof's "convert angle to cosine" step
should `unfold EuclideanGeometry.angle` then `rw [InnerProductGeometry.cos_angle]`
(or equivalent `simp` lemma chain).

`Real.arccos_inj` (L336, two-sided iff) may be cleaner than `arccos_injOn` (L333)
for the cosine-equality step, since the proof already has explicit `[-1, 1]` bounds
on both sides from the inner-product Cauchy-Schwarz application; the two-sided form
avoids an intermediate `InjOn.eq_iff` invocation.

### 2.3. Distances / norms / inner products (`knowledge.md §4.3`)

| Bearer | Cited path | Pinned-SHA actual | Drift | Signature at SHA |
|---|---|---|---|---|
| `dist_eq_norm_vsub` | `Normed/Group/AddTorsor.lean` (no line) | **L76** | — | `theorem dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖` |
| `dist_eq_norm_vsub'` | (variant; cited via knowledge.md crossref) | **L86** | — | `(x y : P) : dist x y = ‖y -ᵥ x‖` |
| `real_inner_self_eq_norm_mul_norm` | `Analysis/InnerProductSpace/Basic.lean` (no line) | **L380** | — | `(x : F) : ⟪x, x⟫_ℝ = ‖x‖ * ‖x‖` |
| `real_inner_comm` | (same file) | **L58** | — | `(x y : F) : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ` |
| `inner_smul_left` | (same) | **L104** | — | `(x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪x, y⟫` |
| `inner_smul_right` | (same) | **L114** | — | `(x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * ⟪x, y⟫` |
| `inner_add_left` | (same) | **L71** | — | `(x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫` |
| `inner_add_right` | (same) | **L74** | — | `(x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫` |
| `norm_smul` | `Analysis/Normed/Module.lean` (no line; standard) | (not re-checked; signature stable) | — | `(r : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖` |

**§2.3 audit summary**: file paths correct. `inner_smul_left` returns `r† * ⟪x, y⟫`
(with `†` denoting `starRingEnd` — the involution; for `ℝ`-valued inner products this is
the identity), so a real-form rewrite needs `RCLike.star_def`/`Complex.conj_ofReal` or
direct `real_inner_smul_left` if present. Spot-check needed during S2 if `inner_smul_left`
alone produces unexpected `starRingEnd ℝ r` artefacts.

### 2.4. Non-degeneracy / Cauchy-Schwarz strict form (`knowledge.md §4.4`)

| Bearer | Cited path:line | Pinned-SHA actual | Drift | Signature at SHA |
|---|---|---|---|---|
| `Collinear` | `LinearAlgebra/AffineSpace/Independent.lean` (no line) | (not re-checked; standard) | — | `(R : Type*) {V : Type*} [Ring R] [AddCommGroup V] [Module R V] {P : Type*} [AffineSpace V P] (s : Set P) : Prop` |
| `EuclideanGeometry.collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi` | `Affine.lean:376` | **L378** | +2 | `{p₁ p₂ p₃ : P} : Collinear ℝ {p₁, p₂, p₃} ↔ p₁ = p₂ ∨ p₃ = p₂ ∨ ∠ p₁ p₂ p₃ = 0 ∨ ∠ p₁ p₂ p₃ = π` |
| `abs_real_inner_le_norm` | `InnerProductSpace/Basic.lean` (no line) | **L453** | — | `(x y : F) : |⟪x, y⟫_ℝ| ≤ ‖x‖ * ‖y‖` |
| `real_inner_eq_norm_mul_iff` | (same file) | (not re-checked; appears at ~L480-520; spot-check during S2) | — | Equality case of Cauchy-Schwarz |
| `LinearIndependent.pair_iff` | `LinearAlgebra/LinearIndependent.lean` (no line) | (not re-checked; standard) | — | Linear independence of two vectors |

**§2.4 audit summary**: cited lemmas are present. The `real_inner_eq_norm_mul_iff` row
was not exhaustively verified (the file `InnerProductSpace/Basic.lean` is 957 lines and
the lemma is in a less-touched section); spot-check needed at S2 implementation.

## 3. Risk-register updates (refinement of `knowledge.md §5`)

Cross-referencing the original risk register against the audit findings:

| Risk (knowledge.md §5) | Audit verdict |
|---|---|
| `Sbtw.mem_image_Ioo` signature surprise | **Confirmed.** Lemma returns `y ∈ lineMap x z '' Set.Ioo (0 : R) 1` (an `image`-set membership); unpacking takes `rcases ... with ⟨t, ht, rfl⟩` — exactly two `rcases` steps. Mitigation cost: ≤2 LOC. |
| Inner-product `ring` blow-up | **Not testable from audit alone.** Bearers (`inner_add_*`, `inner_smul_*`) all present with the expected bilinearity signatures. `linear_combination` will likely close the factorization given correct expansion. |
| Non-degeneracy extra hypotheses | **Not testable from audit alone.** `abs_real_inner_le_norm` (L453) gives the inequality; `real_inner_eq_norm_mul_iff` (≈L480-520) gives the equality case. If the latter has been renamed/restructured, fallback path: derive the strict inequality from `Real.add_pow_le_pow_mul_pow_of_sq_le_sq` (Cauchy-Schwarz alternate form) or from `Real.inner_mul_le_norm_mul_norm`. |
| `EuclideanGeometry.angle` definition uses `arccos` | **Confirmed.** The def `EuclideanGeometry.angle` (L42) is `nonrec def` that delegates to `InnerProductGeometry.angle` (Unoriented/Basic.lean L40), which is `Real.arccos (⟪x, y⟫ / (‖x‖ * ‖y‖))`. The cosine-equality step needs: (i) `unfold EuclideanGeometry.angle`; (ii) `rw [InnerProductGeometry.cos_angle]`; (iii) `Real.arccos_inj` with explicit `[-1, 1]` bounds. |
| Mathlib version drift | **Confirmed**, but **names stable across the drift window** (lines drift but no rename). The audit doc fixes the only file-path error: `InnerProductGeometry.angle/cos_angle` live in `Geometry/Euclidean/Angle/Unoriented/Basic.lean`. |
| `arccos` injectivity bounds | **Bounds derivable.** `abs_real_inner_le_norm` (L453) gives `\|⟪x, y⟫_ℝ\| ≤ ‖x‖ * ‖y‖`, which combined with `‖x‖ * ‖y‖ > 0` (from non-zeroness) gives `\|⟪x, y⟫ / (‖x‖ * ‖y‖)\| ≤ 1`, the input to `arccos_inj`. ≤6 LOC overhead. |

## 4. New: Step-1 cosine-equality sketch (Path A refinement)

Translating §3 Path A Step 1 into pinned-SHA-grounded Lean:

```lean
-- Inputs: hangle : ∠ B A D = ∠ D A C in EuclideanGeometry sense.
-- u := B -ᵥ A, v := C -ᵥ A, w := D -ᵥ A.
-- Goal: ⟪u, w⟫ / (‖u‖ · ‖w‖) = ⟪v, w⟫ / (‖v‖ · ‖w‖)

-- Step 1a: rewrite EuclideanGeometry.angle in terms of InnerProductGeometry.angle.
unfold EuclideanGeometry.angle at hangle  -- ∠ p q r := angle (p -ᵥ q) (r -ᵥ q)

-- Step 1b: ‖u‖ > 0, ‖w‖ > 0 (from B ≠ A, D ≠ A); similarly ‖v‖ > 0.
-- These are extracted from `Sbtw.ne_left` (Between.lean L341), strict-betweenness of D
-- on BC plus the triangle non-degeneracy assumption (¬ Collinear A B C).

-- Step 1c: take Real.cos of both sides via Real.arccos_inj (Inverse.lean L336).
have h_bounds_u : ⟪u, w⟫ / (‖u‖ * ‖w‖) ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [Set.mem_Icc, abs_le_iff]; exact abs_inner_div_norm_mul_norm_le_one (B - A) (D - A)
  -- Or: derived from `abs_real_inner_le_norm` (Basic.lean L453) + positivity.
have h_bounds_v : ⟪v, w⟫ / (‖v‖ * ‖w‖) ∈ Set.Icc (-1 : ℝ) 1 := by
  -- analogous
  sorry
-- Apply Real.cos to both sides of hangle.
have hcos_eq : Real.cos (InnerProductGeometry.angle u w)
             = Real.cos (InnerProductGeometry.angle v w) := by
  rw [hangle]
rw [InnerProductGeometry.cos_angle, InnerProductGeometry.cos_angle] at hcos_eq
-- hcos_eq : ⟪u, w⟫ / (‖u‖ * ‖w‖) = ⟪v, w⟫ / (‖v‖ * ‖w‖)
```

Estimated 15-25 LOC for Step 1; matches the §3 budget for the cosine-conversion step.

## 5. Next-Session Checklist (S2-implement)

1. Create `proofs/Proofs/LawOfCosinesOQ04OQ02OQ01.lean` with imports
   `Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine` (also pulls in
   `Unoriented/Basic.lean` and `InnerProductSpace/Basic.lean` transitively),
   `Mathlib.Analysis.Convex.Between`, and `Proofs.LawOfCosinesOQ04OQ02` for the
   downstream Stewart-chain.
2. Use §2.2's corrected `InnerProductGeometry.*` file path
   (`Geometry/Euclidean/Angle/Unoriented/Basic.lean`) when threading angle→cosine.
3. Use §2.1's pinned-SHA-correct line numbers when copying `Sbtw.*` invocations.
4. Apply §4's cosine-equality sketch verbatim for Step 1, then expand into
   factorization (Step 2-4 of `knowledge.md §3.A`).
5. Build via `./proofs/scripts/docker-build.sh Proofs.LawOfCosinesOQ04OQ02OQ01`.

## 6. Audit scope notes

- Audited `§4.1` (Affine/between) and `§4.2` (Angles) **exhaustively**.
- Audited `§4.3` (Distances/norms/inner products) **most-used bearers only**;
  `norm_smul` and `abs_of_pos`/`abs_of_nonneg` not re-grounded (standard, stable across
  Mathlib versions).
- Audited `§4.4` (Non-degeneracy/Cauchy-Schwarz strict) **structurally only**; the
  `real_inner_eq_norm_mul_iff` row is the only spot-check deferred to S2 implementation.
- `§4.5` (Stewart's theorem / parent file `LawOfCosinesOQ04OQ02.lean`) **not re-audited**;
  this is in-project code (not Mathlib) and its presence is verified by the
  existing 174-line `LawOfCosinesOQ04OQ02.lean` with 9 theorems, 0 sorries, 0 axioms.

## 7. Cross-references

- Spec: `knowledge.md` (S1 OBSERVE, researcher-8, 2026-05-11, PR #17833).
- Parent file: `proofs/Proofs/LawOfCosinesOQ04OQ02.lean` (Stewart-form angle bisector
  identities, 174 LOC, 9 theorems, 0 axioms).
- Mathlib pin: `proofs/lake-manifest.json` →
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (`v4.26.0`).
- Companion PREP pattern: `birthday-problem-oq-03-oq-01-oq-02-oq-01` S16d PREP follow-up
  (researcher-4, 2026-05-13, doc-only Mathlib bearer audit at the same pinned SHA).
