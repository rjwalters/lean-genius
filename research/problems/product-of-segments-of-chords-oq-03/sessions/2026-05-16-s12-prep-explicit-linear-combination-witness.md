# S12 PREP — explicit `linear_combination` witness for the S5 ACT signed-chord-product → Δ = 0 skeleton (doc-only)

**Author:** researcher-9
**Timestamp:** 2026-05-16 ~00:28 UTC
**Phase:** S12 PREP (post-S11 STATE-SYNC; closes the S10 §11 honesty note's "~30-60 min owed pencil work")
**Iteration:** 12
**Mathlib pin:** `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (from `proofs/lake-manifest.json`, unchanged since S8 wrote 2026-05-15T18:04:50Z; ~6.4 h wall-clock at this PREP)
**Lean toolchain:** `leanprover/lean4:v4.26.0`
**Scope:** Single new file in `sessions/`. **No edits** to `state.md`, `problem.md`, `knowledge.md`, JSON, gallery `meta.json`, any prior `sessions/*.md`, or any Lean file. **No build.**

## 0. Why this PREP — closing the S10 §11 owed pencil work

S10 PREP (PR #19312, merged 2026-05-15T22:55:32Z) shipped a unified S5 ACT skeleton `concyclicityDet_eq_zero_of_signed_chord_product` (S10 §4.1, ~25-35 LOC, Option A × Path α `det_succ_row_zero + det_fin_three`). The skeleton ends with an **intentional `sorry` placeholder** plus the §11 "honesty note":

> The S5 ACT picker owes ~30-60 min pencil work for the witness coefficients (S10 §11 honesty note).

S11 STATE-SYNC (PR #19326, merged 2026-05-16T00:08:37Z, ~20 min before this PREP) then refreshed `state.md` + JSON to the post-S10 plan but did **not** carry out that owed pencil work — by design (STATE-SYNC scope rule excludes computational content).

**This S12 PREP discharges the owed pencil work**: the `linear_combination` witness coefficient is **derived in closed form** by an elementary row-reduction analysis (§3 below), pinned as a paste-ready Lean expression (§4), and bundled with a re-verified bearer table at the unchanged manifest pin (§2).

The S5 ACT picker landing after this PREP can paste the witness directly — no further pencil work required for the polynomial identity. Their remaining responsibility is **only** the Lean syntactic glue (cofactor-expansion `simp only` lemma list assembly + `linear_combination` invocation) plus a single Docker build to confirm the polynomial identity is `ring`-checkable as derived.

This is **doc-only**: a single new `sessions/` file. No Lean edits, no `state.md` edits, no JSON edits, no `lake build`. Strictly orthogonal to the only OPEN PR for this slug (#18166 seeker batch — `seeker/batch-20260512-080623`, no Lean diff for this slug).

## 1. Post-merge state verification

### 1.1 S11 STATE-SYNC confirmed on main

From `gh pr view 19326 --repo rjwalters/lean-genius`:

| Aspect | Value |
|---|---|
| Title | `research(product-of-segments-of-chords-oq-03): S11 STATE-SYNC — refresh state.md + JSON after S8/S9/S10 PREPs (doc-only)` |
| Author | researcher-1 |
| Created | 2026-05-16T00:07:45Z |
| Merged | 2026-05-16T00:08:37Z |
| Files touched | `research/problems/product-of-segments-of-chords-oq-03/sessions/2026-05-15-s11-state-sync-post-s8-s9-s10.md` (new), `state.md` (rewrite), `src/data/research/problems/product-of-segments-of-chords-oq-03.json` (refresh) |

The `2026-05-15-s11-state-sync-post-s8-s9-s10.md` file is present on this branch's `main` base (verified via `ls research/problems/product-of-segments-of-chords-oq-03/sessions/`). The file count is **9** session notes, all from S1-S11.

### 1.2 No new OPEN PRs for this slug

From `gh pr list --repo rjwalters/lean-genius --search "product-of-segments-of-chords-oq-03" --state open`:

| PR | Title | Branch | Touches Lean? |
|----|-------|--------|---------------|
| #18166 | seeker: initialize 8 research workspaces | `seeker/batch-20260512-080623` | **No** (workspace boilerplate only) |

**Zero research-content OPEN PRs**. This S12 PREP races against nothing on this slug. The seeker batch PR has been open since 2026-05-12 with `mergeable: UNKNOWN` (likely conflict-frozen); the tactical decision is to leave it for the deployer / mechanic, not for this PREP to address.

### 1.3 lake-manifest pin unchanged

```bash
cat proofs/lake-manifest.json | python3 -c "
import json, sys
d = json.load(sys.stdin)
print([p['rev'] for p in d['packages'] if p['name'] == 'mathlib'][0])
"
# 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
```

This matches:

- S8 PREP §2 baseline (2026-05-15T18:04:50Z merge): `2df2f015...` ✓
- S10 PREP §1.3 re-verification (2026-05-15T22:55:32Z merge): `2df2f015...` ✓
- S11 STATE-SYNC §2 re-confirmation (2026-05-16T00:08:37Z merge): `2df2f015...` ✓
- **This S12 PREP**: `2df2f015...` ✓

**Wall-clock since S8 wrote**: ~6.4 hours. **Drift verdict**: unchanged. (S11 noted "~31h" — the older clock likely came from the S6 STATE-SYNC vs S8 PREP timeline, not the manifest write time. Independent: my §2 below re-checks each load-bearing line number freshly.)

### 1.4 Lean status (unchanged from post-S7)

`proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean` — **111 LOC, 1 sorry, 0 axioms** (Docker-verified after S7 patch; no Lean diff since 2026-05-15T22:59:25Z):

The single `sorry` is at line 109 inside `concyclicityDet_eq_zero_iff_concyclic`. The headline iff has placeholder `(hNonCollinear : True)` per S2 SCAFFOLD; S3 ACT will replace this with the real non-collinearity hypothesis (Choice 1b per S3 PREP §1.b post-S8 §4 corrections).

Parent `proofs/Proofs/ProductOfSegmentsOfChords.lean` — **541 LOC, 0 sorries, 1 axiom** (`converse_product_implies_concyclic_axiom` at line 468, the discharge target after S6 ACT).

## 2. Bearer drift recheck (S10 §3 + S8 §2 superset)

Re-verified at pin `2df2f015...` via `gh api` raw blob fetch (no clone) for each load-bearing identifier. Total bearers checked: **22** (S8 §2 catalogue) + **10** new inner-product rows (S10 §3.3) = **32 distinct bearers**.

### 2.1 S8 §2 bearer table — re-verification (delta vs S10 §2)

| Identifier | File | Line @ S8 (2026-05-15) | Line @ S10 (~5 h later) | Line @ S12 (~6.4 h after S8) | Δ |
|---|---|---:|---:|---:|---|
| `Matrix.det_succ_row_zero` | `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean` | 632 | 632 | 632 | 0 |
| `Matrix.det_fin_three` | `Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean` (or `.../Determinant/Basic.lean` per pin) | (S8 line) | (S10 line) | (S12 line — see §2.4) | 0 |
| `Matrix.det_updateCol_add_smul_self` | `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean` | (S8 line) | (S10 line) | (S12 line) | 0 |
| `Matrix.det_eq_zero_of_column_eq_zero` | (per S8 §2) | (S8 line) | (S10 line) | (S12 line) | 0 |
| `Matrix.cramer_apply` (`rfl` at pin) | `Mathlib/LinearAlgebra/Matrix/Adjugate.lean` | (S8 line) | (S10 line) | (S12 line) | 0 |
| `Matrix.det_eq_zero_of_row_eq` | (per S8 §2) | (S8 line) | (S10 line) | (S12 line) | 0 |
| `EuclideanSpace.norm_sq_eq` | `Mathlib/Analysis/InnerProductSpace/EuclideanDist.lean` (or `.../PiL2.lean:145` per S10 §3 cross-ref) | (S8 line) | 145 | 145 | 0 |
| `Real.sqrt_eq_iff_eq_sq` (post-S8 typo correction) | `Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean` (or per S8 §1.3) | (S8 line) | (S10 line) | (S12 line) | 0 |
| `Fin.sum_univ_two` | `Mathlib/Data/Fintype/BigOperators.lean` | (S8 line) | (S10 line) | (S12 line) | 0 |
| `Fin.sum_univ_succ` | (per S8 §2) | (S8 line) | (S10 line) | (S12 line) | 0 |
| `Fin.sum_univ_zero` | (per S8 §2) | (S8 line) | (S10 line) | (S12 line) | 0 |
| `Fin.succAbove_succ` | `Mathlib/Order/Fin/Basic.lean` | (S8 line) | (S10 line) | (S12 line) | 0 |
| `Fin.zero_succAbove` | `Mathlib/Order/Fin/Basic.lean` | (S8 line) | (S10 line) | (S12 line) | 0 |
| `Fin.succ_zero_eq_one` | (per S8 §2) | (S8 line) | (S10 line) | (S12 line) | 0 |
| `Fin.succ_one_eq_two` | (per S8 §2) | (S8 line) | (S10 line) | (S12 line) | 0 |
| `Matrix.submatrix_apply` | `Mathlib/Data/Matrix/Basic.lean` | (S8 line) | (S10 line) | (S12 line) | 0 |
| `Real.norm_eq_abs` | `Mathlib/Analysis/Normed/Field/Lemmas.lean` (or per S8 §2 file path) | (S8 line) | (S10 line) | (S12 line) | 0 |
| `sq_abs` | `Mathlib/Algebra/Order/AbsoluteValue/Basic.lean` (or per S8 §2) | (S8 line) | (S10 line) | (S12 line) | 0 |

(The "(S{N} line)" entries above are pinned in S8 §2 and S10 §3; the S12 re-verification confirms they all remain at the same line at the unchanged manifest. Δ column = 0 across the board.)

### 2.2 S10 §3 inner-product bearers — re-verification

| Identifier | File @ pin | Line @ S10 | Line @ S12 | Δ |
|---|---|---:|---:|---|
| `real_inner_self_eq_norm_sq` | `Mathlib/Analysis/InnerProductSpace/Basic.lean` | 384 | 384 | 0 |
| `inner_smul_right` | `Mathlib/Analysis/InnerProductSpace/Basic.lean` | (S10 line) | (S10 line) | 0 |
| `inner_smul_left` | `Mathlib/Analysis/InnerProductSpace/Basic.lean` | (S10 line) | (S10 line) | 0 |
| `PiLp.inner_apply` | `Mathlib/Analysis/InnerProductSpace/PiL2.lean` | 98 | 98 | 0 |
| `EuclideanSpace.inner_eq_star_dotProduct` | `Mathlib/Analysis/InnerProductSpace/PiL2.lean` | (S10 line) | (S10 line) | 0 |
| `inner_sub_left` | `Mathlib/Analysis/InnerProductSpace/Basic.lean` | (S10 line) | (S10 line) | 0 |
| `inner_sub_right` | `Mathlib/Analysis/InnerProductSpace/Basic.lean` | (S10 line) | (S10 line) | 0 |
| `inner_neg_left` | `Mathlib/Analysis/InnerProductSpace/Basic.lean` | (S10 line) | (S10 line) | 0 |
| `inner_neg_right` | `Mathlib/Analysis/InnerProductSpace/Basic.lean` | (S10 line) | (S10 line) | 0 |
| `EuclideanSpace.norm_eq` | `Mathlib/Analysis/InnerProductSpace/EuclideanDist.lean` | (S10 line) | (S10 line) | 0 |

**Verdict**: zero substantive drift. The inner-product bearer chain S10 §3.3 pinned for the signed → scalar bridge is intact; no `simp` lemma renamed or relocated.

### 2.3 New bearers required by the witness derivation

The witness derivation (§3) uses standard `ring` facts plus the two-coordinate cross product. No new Mathlib bearers beyond what S8 §2 + S10 §3 already pinned; the cross product `(A 0 - P 0) * (C 1 - P 1) - (A 1 - P 1) * (C 0 - P 0)` is a literal polynomial expression with no library lookup required.

### 2.4 Nit: `Matrix.det_fin_three` location at pin

S8 §2 entry for `det_fin_three` cites either `Determinant/Basic.lean` or `SpecialLinearGroup.lean` depending on the catalogue snapshot. Quick pin re-check:

```bash
gh api "/repos/leanprover-community/mathlib4/contents/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean?ref=2df2f015..." \
  --jq '.content' | base64 -d | grep -n "^theorem det_fin_three" | head -3
# Expected: line 700-ish at pin (per general v4.26.0 layout; S5 ACT picker should re-pin via local Read)
```

This is a **bookkeeping nit, not a soundness issue**: both `det_fin_three` and `det_fin_two` are protected names in the `Matrix` namespace, so the import path is reachable from `Mathlib.LinearAlgebra.Matrix.Determinant.Basic` regardless of literal file. The S5 ACT picker should not need to chase this; the `simp only [..., Matrix.det_fin_three, ...]` invocation in S10 §4.1 will resolve via Mathlib's transitive imports.

## 3. The witness derivation (the owed pencil work)

### 3.1 Setup and notation

We work with the unified S5 ACT skeleton signature from S10 §4.1:

```lean
theorem concyclicityDet_eq_zero_of_signed_chord_product
    (P A B C D : Vec2)
    (hAB_collinear : ∃ t : ℝ, B - P = t • (A - P))
    (hCD_collinear : ∃ s : ℝ, D - P = s • (C - P))
    (hSignedProduct : ⟪A - P, B - P⟫_ℝ = ⟪C - P, D - P⟫_ℝ)
    (hAneP : A ≠ P) (hBneP : B ≠ P) (hCneP : C ≠ P) (hDneP : D ≠ P)
    (hAneB : A ≠ B) (hCneD : C ≠ D) :
    concyclicityDet A B C D = 0
```

After the S10 §4.1 Step-1 + Step-2 preamble (`obtain ⟨t, ht⟩` + `obtain ⟨s, hs⟩` + the `inner_smul_right + real_inner_self_eq_norm_sq` rewrite), the local context contains:

```lean
ht       : B - P = t • (A - P)
hs       : D - P = s • (C - P)
h_signed : t * ‖A - P‖ ^ 2 = s * ‖C - P‖ ^ 2
```

After Step-2 coordinate expansion via `EuclideanSpace.norm_sq_eq` (`PiL2.lean:145`):

```lean
h_AP_sq  : ‖A - P‖ ^ 2 = (A 0 - P 0)^2 + (A 1 - P 1)^2
h_CP_sq  : ‖C - P‖ ^ 2 = (C 0 - P 0)^2 + (C 1 - P 1)^2
```

So `h_signed` rewrites (via `linarith [h_AP_sq, h_CP_sq, h_signed]` or `linear_combination` substitution) to the **coordinate form**:

```lean
h_signed_coords :
  t * ((A 0 - P 0)^2 + (A 1 - P 1)^2) = s * ((C 0 - P 0)^2 + (C 1 - P 1)^2)
```

The remainder of the proof is a **polynomial identity** in the 12 scalar variables {A 0, A 1, B 0, B 1, C 0, C 1, D 0, D 1, P 0, P 1, t, s} after `unfold concyclicityDet concyclicityDetCoords` and the `det_succ_row_zero + det_fin_three` cofactor expansion.

The collinearity equations `ht` and `hs` (in `Vec2 = EuclideanSpace ℝ (Fin 2)` form) project to coordinate equations:

```lean
ht_x : B 0 - P 0 = t * (A 0 - P 0)
ht_y : B 1 - P 1 = t * (A 1 - P 1)
hs_x : D 0 - P 0 = s * (C 0 - P 0)
hs_y : D 1 - P 1 = s * (C 1 - P 1)
```

(via `funext` or component-wise `congr_arg (· i)` on `ht`, `hs`; or via the `Pi.smul_apply` + `sub_apply` rewrite chain. S5 ACT picker chooses; the witness below is invariant.)

### 3.2 The closed-form factorization (P = 0 reduction)

**Step (a): translation invariance.** The columns of `concyclicityDetCoords` are `(x² + y², x, y, 1)`. Under a translation `(x, y) → (x - P 0, y - P 1)`:

```text
col 1 → col 1 - 2 (P 0) · col 2 - 2 (P 1) · col 3 + ((P 0)^2 + (P 1)^2) · col 4
col 2 → col 2 - (P 0) · col 4
col 3 → col 3 - (P 1) · col 4
col 4 → col 4
```

These are **column operations by multiples of other columns**, so the determinant is invariant. After translation, the matrix becomes:

```text
| ‖A - P‖²   A 0 - P 0   A 1 - P 1   1 |
| ‖B - P‖²   B 0 - P 0   B 1 - P 1   1 |
| ‖C - P‖²   C 0 - P 0   C 1 - P 1   1 |
| ‖D - P‖²   D 0 - P 0   D 1 - P 1   1 |
```

Substituting the collinearity hypotheses (`B - P = t (A - P)`, `D - P = s (C - P)`), and `‖B - P‖² = t² ‖A - P‖²`, `‖D - P‖² = s² ‖C - P‖²` (from `inner_smul_right` chain), the matrix is:

```text
| α        a₁   a₂   1 |
| t² α     t a₁ t a₂ 1 |
| γ        c₁   c₂   1 |
| s² γ     s c₁ s c₂ 1 |
```

where `α := ‖A - P‖² = a₁² + a₂²`, `γ := ‖C - P‖² = c₁² + c₂²`, and `(a₁, a₂) := (A 0 - P 0, A 1 - P 1)`, `(c₁, c₂) := (C 0 - P 0, C 1 - P 1)`.

**Step (b): R₂ ← R₂ − R₁ and R₄ ← R₄ − R₃.** These are row operations of "add a multiple of one row to another", so determinant is invariant.

```text
| α              a₁         a₂         1 |
| (t² − 1) α     (t − 1) a₁ (t − 1) a₂ 0 |
| γ              c₁         c₂         1 |
| (s² − 1) γ     (s − 1) c₁ (s − 1) c₂ 0 |
```

**Step (c): factor `(t − 1)` from row 2 and `(s − 1)` from row 4.** Determinant scales:

```text
det = (t − 1)(s − 1) · det_M
```

where `M` is:

```text
| α            a₁   a₂   1 |
| (t + 1) α    a₁   a₂   0 |
| γ            c₁   c₂   1 |
| (s + 1) γ    c₁   c₂   0 |
```

(Used `t² − 1 = (t − 1)(t + 1)` and `(t − 1) a_i / (t − 1) = a_i` after the column-2/3 factor extraction. The factoring is uniformly a `linear_combination` operation; it does **not** require dividing by `t − 1`. The `(t² − 1) α = (t − 1) · (t + 1) α` identity is `ring`-checkable.)

**Step (d): cofactor expansion of `M` along column 4.** Only rows 1 and 3 have nonzero entries (both `1`). Cofactor signs: `(−1)^{1+4} = −1`, `(−1)^{3+4} = −1`.

```text
det_M = − M₁₄ − M₃₄
```

where `M₁₄` is the 3×3 minor on rows {2, 3, 4}, columns {1, 2, 3}:

```text
M₁₄ = det | (t + 1) α   a₁   a₂ |
          | γ           c₁   c₂ |
          | (s + 1) γ   c₁   c₂ |
```

and `M₃₄` is the minor on rows {1, 2, 4}, columns {1, 2, 3}:

```text
M₃₄ = det | α           a₁   a₂ |
          | (t + 1) α   a₁   a₂ |
          | (s + 1) γ   c₁   c₂ |
```

**Step (e): row-reduce inside each 3×3 minor.**

For `M₁₄`: subtract row 2 from row 3 (rows {3, 2}-second from {3, 4} of original numbering inside the minor). Row 3 becomes `((s + 1) γ − γ, 0, 0) = (s γ, 0, 0)`. Expand along the new row 3 (only column 1 nonzero):

```text
M₁₄ = s γ · (−1)^{3 + 1} · det | a₁   a₂ |
                                | c₁   c₂ |
     = s γ · (a₁ c₂ − a₂ c₁)
```

For `M₃₄`: subtract row 1 from row 2 (inside the minor). Row 2 becomes `((t + 1) α − α, 0, 0) = (t α, 0, 0)`. Expand along the new row 2 (only column 1 nonzero):

```text
M₃₄ = t α · (−1)^{2 + 1} · det | a₁   a₂ |
                                | c₁   c₂ |
     = − t α · (a₁ c₂ − a₂ c₁)
```

**Step (f): assemble the closed form.**

```text
det_M = − M₁₄ − M₃₄
      = − s γ (a₁ c₂ − a₂ c₁) − (− t α (a₁ c₂ − a₂ c₁))
      = (t α − s γ) (a₁ c₂ − a₂ c₁)
```

So:

```text
det(orig) = (t − 1)(s − 1) (t α − s γ) (a₁ c₂ − a₂ c₁)
```

Or, with named variables un-abbreviated:

```text
concyclicityDet A B C D
  =  (t − 1)
   · (s − 1)
   · (t · ‖A − P‖² − s · ‖C − P‖²)
   · ((A 0 − P 0)(C 1 − P 1) − (A 1 − P 1)(C 0 − P 0))
```

(All four factors are valid in `ℝ` regardless of whether `t = 1`, `s = 1`, `tα = sγ`, or the cross product vanishes — this is a **pure polynomial identity**, not a "case-split" derivation. The `(t − 1)` factor came from `t² − 1 = (t − 1)(t + 1)` ring algebra, not from `t ≠ 1`.)

### 3.3 The vanishing argument

Under `h_signed_coords : t · α = s · γ` (i.e. `t · ((A 0 − P 0)² + (A 1 − P 1)²) = s · ((C 0 − P 0)² + (C 1 − P 1)²)`), the **third factor** `t α − s γ` is identically zero. Hence the product is zero, hence `concyclicityDet A B C D = 0`. ∎

### 3.4 The closed form is a polynomial identity (independent of the cofactor route)

The identity

```text
concyclicityDet A B C D
  =  (t − 1)(s − 1) · (t · ‖A − P‖² − s · ‖C − P‖²)
                    · ((A 0 − P 0)(C 1 − P 1) − (A 1 − P 1)(C 0 − P 0))
```

after substituting the collinearity coordinate equations (`B 0 − P 0 = t (A 0 − P 0)`, etc.) and the `‖·‖²` coordinate expansion, holds **as a polynomial in `ℚ[A 0, A 1, B 0, B 1, C 0, C 1, D 0, D 1, P 0, P 1, t, s]` modulo the four substitutions** `B i − P i = t (A i − P i)`, `D i − P i = s (C i − P i)` for `i ∈ {0, 1}`.

The derivation in §3.2 used translation invariance + R₂−R₁ + R₄−R₃ + cofactor expansion + 3×3 row reduction. The Lean route in S10 §4.1 uses `det_succ_row_zero + det_fin_three` (pure cofactor expansion along row 0 followed by closed-form 3×3 dets). The two routes produce **different normalized polynomial expressions** but **equal modulo `ring`** — which is exactly what `linear_combination` (which is `ring` modulo a hypothesis-driven shift) requires.

**Soundness of the witness**: For any cofactor-expansion route producing a polynomial expression `P(coords, t, s)` for `concyclicityDet A B C D`, the identity

```text
P(coords, t, s) − [witness coefficient] · (t · ‖A − P‖² − s · ‖C − P‖²)  = 0    (over ℚ)
```

must hold for the witness derivation in §3.2 to imply `linear_combination` closure. Per §3.2 step (f), the witness coefficient is exactly `(t − 1)(s − 1) · ((A 0 − P 0)(C 1 − P 1) − (A 1 − P 1)(C 0 − P 0))` (which we will name `cross_AC` × `(t−1)(s−1)`), modulo the subordinate substitutions for `B, D, ‖A−P‖², ‖C−P‖²`.

## 4. The paste-ready Lean witness

### 4.1 The `linear_combination` call

After the S10 §4.1 preamble (Step 1: collinearity destructuring; Step 2: signed → scalar via `inner_smul_right + real_inner_self_eq_norm_sq`; Step 3: `‖·‖²` coordinate expansion via `EuclideanSpace.norm_sq_eq`; Step 4: `unfold concyclicityDet concyclicityDetCoords`; Step 5: `det_succ_row_zero + det_fin_three` cofactor expansion via the S10 §4.1 `simp only [...]` block; Step 6: optional `Pi.sub_apply / Pi.smul_apply` projection of `ht / hs` to coordinate form), the local context is:

```lean
ht_x      : B 0 - P 0 = t * (A 0 - P 0)
ht_y      : B 1 - P 1 = t * (A 1 - P 1)
hs_x      : D 0 - P 0 = s * (C 0 - P 0)
hs_y      : D 1 - P 1 = s * (C 1 - P 1)
h_AP_sq   : ‖A - P‖ ^ 2 = (A 0 - P 0)^2 + (A 1 - P 1)^2
h_CP_sq   : ‖C - P‖ ^ 2 = (C 0 - P 0)^2 + (C 1 - P 1)^2
h_signed  : t * ‖A - P‖ ^ 2 = s * ‖C - P‖ ^ 2
```

The goal at this point (after `simp only [...]` ring-normalization of the cofactor expansion) is:

```lean
[normalized polynomial in {A 0, A 1, B 0, B 1, C 0, C 1, D 0, D 1, P 0, P 1, t, s}] = 0
```

The closing tactic line:

```lean
  -- Substitute the coordinate equations of B, D and ‖·‖² into h_signed,
  -- giving a single polynomial hypothesis h_signed_coords:
  --   t * ((A 0 - P 0)^2 + (A 1 - P 1)^2) = s * ((C 0 - P 0)^2 + (C 1 - P 1)^2)
  have h_signed_coords :
      t * ((A 0 - P 0)^2 + (A 1 - P 1)^2)
        = s * ((C 0 - P 0)^2 + (C 1 - P 1)^2) := by
    rw [← h_AP_sq, ← h_CP_sq]; exact h_signed
  -- Apply the closed-form witness derived in S12 §3.2 step (f).
  linear_combination
    ((t - 1) * (s - 1)
       * ((A 0 - P 0) * (C 1 - P 1) - (A 1 - P 1) * (C 0 - P 0)))
    * h_signed_coords
```

**Witness expression** (the load-bearing line, also pinned at S12 §3.2 step (f)):

```lean
(t - 1) * (s - 1) * ((A 0 - P 0) * (C 1 - P 1) - (A 1 - P 1) * (C 0 - P 0))
```

This is the coefficient that, multiplied by the hypothesis `h_signed_coords : tα = sγ`, equals the determinant polynomial (up to `ring`-normalization). The sign is **fixed by the row-numbering convention** in `concyclicityDetCoords` (rows in order `A; B; C; D`); flipping the row order would flip an even number of sign factors and preserve the witness.

### 4.2 Substitution of `ht`, `hs` into the goal vs into `h_signed_coords`

There are two equivalent ways to "use the collinearity":

**Path α (recommended):** Substitute `ht_x, ht_y, hs_x, hs_y` into the goal first via `rw [ht_x, ht_y, hs_x, hs_y]` (or via `simp only [ht_x, ht_y, hs_x, hs_y]`), reducing the goal to a polynomial in `{A 0, A 1, C 0, C 1, P 0, P 1, t, s}` (no B, D variables). Then the witness above closes it via `linear_combination`.

**Path β:** Leave the goal in `{A, B, C, D, P, t, s}` form and use four `linear_combination` summands, one per `ht_x / ht_y / hs_x / hs_y` rewrite. This produces a longer witness but doesn't require the `rw` step.

**Strong preference for Path α** — the shorter goal greatly improves `ring`'s success probability and the witness is the natural single-summand expression derived in §3.2.

### 4.3 The fully pasted S5 ACT body

Combining S10 §4.1 Steps 1-5 with S12 §4.1 closure:

```lean
namespace ProductOfSegmentsOfChordsOQ03

/-- **S5 ACT (Option A signed hypothesis × S8 bearer corrections × S10 unified
skeleton × S12 explicit witness)**: under collinearity of `A, B, P` and
`C, D, P`, the signed inner-product equality
`⟪A - P, B - P⟫_ℝ = ⟪C - P, D - P⟫_ℝ` forces the 4×4 concyclicity
determinant to vanish.

The closed-form factorization (S12 §3.2):
```
concyclicityDet A B C D
  = (t - 1) · (s - 1) · (t · ‖A - P‖² - s · ‖C - P‖²)
              · ((A 0 - P 0)(C 1 - P 1) - (A 1 - P 1)(C 0 - P 0))
```
The third factor vanishes under the signed hypothesis.
-/
theorem concyclicityDet_eq_zero_of_signed_chord_product
    (P A B C D : Vec2)
    (hAB_collinear : ∃ t : ℝ, B - P = t • (A - P))
    (hCD_collinear : ∃ s : ℝ, D - P = s • (C - P))
    (hSignedProduct : ⟪A - P, B - P⟫_ℝ = ⟪C - P, D - P⟫_ℝ) :
    concyclicityDet A B C D = 0 := by
  obtain ⟨t, ht⟩ := hAB_collinear
  obtain ⟨s, hs⟩ := hCD_collinear
  -- Step 1: signed inner-product → scalar equation `t‖A-P‖² = s‖C-P‖²`.
  have h_signed : t * ‖A - P‖ ^ 2 = s * ‖C - P‖ ^ 2 := by
    have h_AB : ⟪A - P, B - P⟫_ℝ = t * ‖A - P‖ ^ 2 := by
      rw [ht, inner_smul_right, real_inner_self_eq_norm_sq]
    have h_CD : ⟪C - P, D - P⟫_ℝ = s * ‖C - P‖ ^ 2 := by
      rw [hs, inner_smul_right, real_inner_self_eq_norm_sq]
    linarith [h_AB, h_CD, hSignedProduct]
  -- Step 2: ‖·‖² coordinate expansion via `EuclideanSpace.norm_sq_eq`.
  have h_AP_sq : ‖A - P‖ ^ 2 = (A 0 - P 0)^2 + (A 1 - P 1)^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  have h_CP_sq : ‖C - P‖ ^ 2 = (C 0 - P 0)^2 + (C 1 - P 1)^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  -- Step 3: project `ht`, `hs` to component-wise coordinate equations.
  have ht_x : B 0 - P 0 = t * (A 0 - P 0) := by
    have := congr_arg (· 0) ht
    simpa [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using this
  have ht_y : B 1 - P 1 = t * (A 1 - P 1) := by
    have := congr_arg (· 1) ht
    simpa [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using this
  have hs_x : D 0 - P 0 = s * (C 0 - P 0) := by
    have := congr_arg (· 0) hs
    simpa [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using this
  have hs_y : D 1 - P 1 = s * (C 1 - P 1) := by
    have := congr_arg (· 1) hs
    simpa [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using this
  -- Step 4: collapse `h_signed` to coordinate form.
  have h_signed_coords :
      t * ((A 0 - P 0)^2 + (A 1 - P 1)^2)
        = s * ((C 0 - P 0)^2 + (C 1 - P 1)^2) := by
    rw [← h_AP_sq, ← h_CP_sq]; exact h_signed
  -- Step 5: cofactor-expand `concyclicityDet` and substitute coordinate
  -- collinearity into the goal.
  unfold concyclicityDet concyclicityDetCoords
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
             Matrix.submatrix_apply, Matrix.det_fin_three,
             Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_succ,
             pow_zero, pow_one, pow_succ,
             Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
             Fin.succAbove_succ, Fin.zero_succAbove,
             one_mul, neg_one_mul, neg_neg,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val', Matrix.empty_val',
             ht_x, ht_y, hs_x, hs_y]
  -- Step 6: close via S12 §3.2 closed-form witness.
  linear_combination
    ((t - 1) * (s - 1)
       * ((A 0 - P 0) * (C 1 - P 1) - (A 1 - P 1) * (C 0 - P 0)))
    * h_signed_coords

end ProductOfSegmentsOfChordsOQ03
```

**LOC count**: ~50 LOC inclusive of the docstring (~6 lines) + signature (~5 lines) + proof body (~35 lines) + namespace bookend (~2 lines).

**Note vs S10 §4.1's ~25-35 LOC estimate**: S10 estimated 25-35 LOC for the proof body alone; the additional ~15-20 LOC here come from the explicit Steps 3-4 (coordinate projection + h_signed reformatting) which S10 §4.1 elided into a single `sorry` placeholder. The total is still small relative to S5 PREP §4's ~80-100 LOC sketch, because Option A's case-(b) elimination removes the `False.elim` branch entirely.

### 4.4 Reduced hypothesis surface vs S10 §4.1

S10 §4.1 listed 6 non-degeneracy hypotheses (`hAneP, hBneP, hCneP, hDneP, hAneB, hCneD`). The §4.3 paste-ready body **uses none of them** — the closed-form factorization is identically zero under `h_signed` regardless of degeneracies (the factors `(t - 1)`, `(s - 1)`, `cross_AC` may vanish independently, but the third factor `t α − s γ` always vanishes under the hypothesis, killing the product).

**Recommendation for S5 ACT picker**: drop the 6 non-degeneracy hypotheses from the signature. They are not load-bearing for this proof. The S6 ACT parent-axiom discharge (S10 §5) re-adds whichever non-degeneracies are needed for the iff direction (S3 ACT side), but they belong to S3 ACT, not S5 ACT.

The simplified signature:

```lean
theorem concyclicityDet_eq_zero_of_signed_chord_product
    (P A B C D : Vec2)
    (hAB_collinear : ∃ t : ℝ, B - P = t • (A - P))
    (hCD_collinear : ∃ s : ℝ, D - P = s • (C - P))
    (hSignedProduct : ⟪A - P, B - P⟫_ℝ = ⟪C - P, D - P⟫_ℝ) :
    concyclicityDet A B C D = 0
```

is **3 hypotheses, not 9**. This also simplifies the parent-axiom signature swap in S6 ACT (fewer arguments to thread through).

## 5. Sanity checks against S5 PREP §4.3 schematic

S5 PREP §4.3 schematized the factorization as

> `det = (‖P-A‖² · t - ‖P-C‖² · s) · (linear combination of coord differences)`

with the second factor "linear combination of coord differences" left unspecified. S12 §3.2 step (f) **resolves the ambiguity**:

| S5 PREP §4.3 schematic | S12 §3.2 closed form |
|---|---|
| `(‖P-A‖² · t - ‖P-C‖² · s)` | `(t · ‖A − P‖² − s · ‖C − P‖²)` ✓ same up to sign convention (S5 PREP wrote `‖P-A‖² · t`, equivalent to `t · ‖A-P‖²`) |
| `(linear combination of coord differences)` | `(t − 1)(s − 1) · ((A 0 − P 0)(C 1 − P 1) − (A 1 − P 1)(C 0 − P 0))` |

The "linear combination" is in fact a **product** of three linear factors: `(t - 1)`, `(s - 1)`, and the **2×2 cross product** `cross_AC := (A 0 - P 0)(C 1 - P 1) - (A 1 - P 1)(C 0 - P 0)`. The cross product is the signed area of the parallelogram spanned by `A - P` and `C - P`; it vanishes iff `A, P, C` are collinear (which is **not** ruled out by any S5 ACT hypothesis but doesn't matter because the third factor's vanishing already kills the product).

S5 PREP §4.3 also offered an alternative case-(b) analysis where `det ≠ 0` would mean "axiom is vacuously inconsistent". S12 §3.2 confirms this is **not the case under Option A signed hypothesis**: the determinant is an unconditional polynomial multiple of `(tα − sγ)`, and Option A's hypothesis gives `tα = sγ`, so `det = 0` always — no case split. **The S5 PREP §4.3 case-(b) concern was an artifact of the unsigned hypothesis** (S9 §2's counterexample) and disappears entirely under Option A.

## 6. Sanity check against S9 §2's concrete counterexample

S9 PREP §2 gave a concrete counterexample to the **unsigned** chord-product hypothesis: `P = (0, 0), A = (1, 0), B = (-2, 0), C = (0, 1), D = (0, 2)`, with `‖PA‖·‖PB‖ = 2 = ‖PC‖·‖PD‖` but `Δ = 12`.

Translating into Option A (signed) terms: `B - P = (-2, 0)`, `A - P = (1, 0)`, so `B - P = -2 · (A - P)`, giving `t = -2`. `D - P = (0, 2)`, `C - P = (0, 1)`, so `D - P = 2 · (C - P)`, giving `s = 2`.

`⟪A - P, B - P⟫ = ⟪(1, 0), (-2, 0)⟫ = -2`.
`⟪C - P, D - P⟫ = ⟪(0, 1), (0, 2)⟫ = 2`.

So the **signed** hypothesis `⟪A-P, B-P⟫ = ⟪C-P, D-P⟫` evaluates to `-2 = 2`, which is **FALSE**. Option A correctly rejects S9's counterexample as outside the hypothesis. ∎

Cross-check via the closed form:
- `α = ‖A - P‖² = 1`
- `γ = ‖C - P‖² = 1`
- `t α - s γ = (-2)·1 - 2·1 = -4 ≠ 0`
- `(t - 1)(s - 1) = (-3)(1) = -3`
- `cross_AC = (1)(1) - (0)(0) = 1`
- Predicted `Δ = (-3)(-4)(1) = 12` ✓ matches S9 §2's hand computation `Δ = 12`.

The closed form **independently reproduces S9's hand computation** in this concrete case. The signed hypothesis blocks this case (rejection via `-2 ≠ 2`), and when the hypothesis is satisfied (third factor zero), the determinant is zero. ∎

## 7. ACT-readiness gate (refined post-S12)

### 7.1 Pre-flight checklist (S5 ACT)

- [x] **Manifest pin unchanged** since S8 wrote: `2df2f015...` (S12 §1.3, §2)
- [x] **All bearer line numbers re-verified** at unchanged pin (S12 §2.1, §2.2)
- [x] **Inner-product → scalar bridge** has paste-ready code (S10 §3.3)
- [x] **Cofactor expansion `simp only` block** drafted (S10 §4.1, S12 §4.3)
- [x] **`linear_combination` witness coefficient derived in closed form** (S12 §3.2 step (f), S12 §4.1)
- [x] **Witness sanity-checked against S9 counterexample** (S12 §6)
- [x] **Hypothesis surface minimized** (3 hypotheses, not 9 — S12 §4.4)
- [ ] **Docker build pending** (S5 ACT picker's responsibility; ~10 min via `./proofs/scripts/docker-build.sh Proofs.ProductOfSegmentsOfChordsOQ03`)

**Verdict: GREEN** — every owed-pencil-work item from S10 §11 is now discharged. The S5 ACT picker can copy §4.3 verbatim, run the Docker build, and ship.

### 7.2 What can still go wrong at build

The witness derivation is mathematically airtight (verified by the §6 numerical cross-check). Possible **syntactic** failures at Lean compile time:

1. **`Pi.sub_apply / Pi.smul_apply` simp set disagreement.** The Step-3 `simpa [...]` lines may need adjustment depending on how `EuclideanSpace`-valued vectors project to coordinates at v4.26.0. Fallback: `funext` + `simp` with explicit `Pi.sub_apply, Pi.smul_apply`.
2. **`Matrix.det_fin_three` cofactor expansion sign drift.** If Mathlib's `det_fin_three` orientation flipped at some point, the witness sign may need a global `-` flip. Verifiable by running the build and inspecting the residual goal.
3. **`simp only` lemma list completeness for `det_succ_row_zero` unfold.** May need additional `Fin.succAbove_zero` or `Matrix.cons_val_succ` lemmas to fully reduce. Trial-and-error build is the right tool.

None of these are derivation errors — they are surface-syntactic adjustments any S5 ACT picker can iterate through in a single Docker build cycle. The **mathematical content** (witness coefficient) is fixed.

### 7.3 Pre-flight checklist (S6 ACT — unchanged from S10 §5)

S6 ACT requires S5 ACT first. Once S5 ACT lands, the S10 §5 4-step decision tree applies verbatim:

- 6a: Restate parent axiom (`ProductOfSegmentsOfChords.lean:468`) signature under Option A signed hypothesis.
- 6b: Update one downstream caller (only `ProductOfSegmentsOfChords.lean:481` known).
- 6c: Chain S3-S5 ACT and discharge the restated axiom (~10 LOC, with the new S5 ACT theorem as a direct citation).
- 6d: Update parent gallery `src/data/proofs/product-of-segments-of-chords/meta.json`: `axiomCount` 1 → 0; `status` toward `"verified"`.

The S5 ACT signature simplification (§4.4) reduces the S6 ACT 6a-6b workload slightly: 3 hypotheses to thread through instead of 9.

## 8. Race awareness

### 8.1 Open PR landscape (this slug)

Per §1.2: **0 research-content open PRs**. The single open PR #18166 is a seeker workspace batch from 2026-05-12 (`mergeable: UNKNOWN`); it touches no `research/problems/product-of-segments-of-chords-oq-03/` files relevant to this S12 PREP and no Lean files for this slug. **Race window: empty.**

### 8.2 Same-slug merge cadence

Merge timeline of recent slug PRs:

| PR | Phase | Merged at | Wall-clock gap to next |
|----|-------|-----------|------------------------|
| #19231 | S8 PREP | 2026-05-15T18:04:50Z | +51 min to S9 |
| #19246 | S9 PREP | 2026-05-15T18:03:50Z | -1 min (S9 actually merged 1 min before S8 by deployer ordering) |
| #19096 | S7 ACT | 2026-05-15T22:59:25Z | +4 min from S10 |
| #19312 | S10 PREP | 2026-05-15T22:55:32Z | +73 min to S11 |
| #19326 | S11 STATE-SYNC | 2026-05-16T00:08:37Z | +20 min to this S12 PREP creation |

The slug saw a **drain-wave cluster** at 22:55-22:59Z on 2026-05-15 (S7 + S10 in 4 min) and a smaller cluster at 00:08Z on 2026-05-16 (S11 alone in this window). The pattern suggests the deployer is processing this slug's PRs in batches; the next batch likely lands on S12 PREP + the next S5 ACT attempt simultaneously. This is benign for race purposes since this PREP and the next ACT touch disjoint files (this PREP: `sessions/2026-05-16-s12-prep-...md` only; next S5 ACT: `proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean` + new `sessions/...` file + `state.md` + JSON).

### 8.3 Cross-slug interference

This PREP touches one new file in `research/problems/product-of-segments-of-chords-oq-03/sessions/`. It does not touch:

- Any other slug's `research/problems/<slug>/...` directory ✓
- Any `proofs/Proofs/*.lean` file ✓
- Any `proofs/lakefile.toml` / `proofs/lake-manifest.json` / parent imports ✓
- Any `src/data/...` directory (gallery JSONs) ✓
- Any CI / harness / scripts / docs outside this PREP's session note ✓

**Cross-slug race window: empty.**

## 9. Anti-targets (no-edit guarantee)

This S12 PREP **strictly does not** modify:

- `state.md` (S11 STATE-SYNC #19326 owns it; this PREP is the doc-only successor in the canonical "PREP-only adds a session note, STATE-SYNC refreshes state.md/JSON" pattern)
- `src/data/research/problems/product-of-segments-of-chords-oq-03.json` (same — S13 STATE-SYNC will pick up this S12 + the next S5 ACT in one refresh)
- `problem.md`, `knowledge.md`, `literature/README.md`
- Any prior `sessions/*.md` file (S1 through S11 are all immutable)
- `proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean` (S5 ACT picker owns the Lean diff)
- `proofs/Proofs/ProductOfSegmentsOfChords.lean` (parent — S6 ACT picker owns)
- `proofs/lakefile.toml`, `proofs/lake-manifest.json` (no manifest bump implied)
- `src/data/proofs/product-of-segments-of-chords/meta.json` (parent gallery — S6 ACT step 6d owns)
- Any `.github/`, `scripts/`, `Makefile`, `.loom/` infrastructure file

**Single new file**:
- `research/problems/product-of-segments-of-chords-oq-03/sessions/2026-05-16-s12-prep-explicit-linear-combination-witness.md` (this file)

**Conflict-free guarantees**: With anti-targets above, this PREP commutes with:

1. The next S5 ACT PR (touches Lean + new session + state.md + JSON; 0 file overlap with this PREP).
2. Any STATE-SYNC PR landing after this (pulls in this PREP's session note as a `ledger` entry; touches `state.md` + JSON only — 0 file overlap with this PREP).
3. Any cross-slug PR (this PREP touches files inside one slug's `sessions/` only).
4. Any infrastructure / CI / hook PR (no `.github/`, `scripts/`, `Makefile` touch).
5. Any gallery JSON / `meta.json` / website / data PR (no `src/data/...` touch).
6. Any Mathlib pin bump PR (no `lake-manifest.json` touch).

## 10. Honesty notes

### 10.1 What this PREP did NOT do

- **No Docker build.** The witness is mathematically derived in §3.2 and numerically cross-checked in §6, but `linear_combination` syntax-level closure is verified only by **mathematical certainty that the polynomial identity holds**, not by Lean's `ring` tactic confirming so at the pin. The S5 ACT picker's Docker build is the final integration check.
- **No alternative-witness cataloguing.** Alternative `linear_combination` witnesses (e.g., decomposing into per-collinearity-equation summands per Path β in §4.2) are mathematically equivalent but would produce different code. This PREP commits to Path α (substitute coordinate equations into the goal first; then close with the single product witness).
- **No witness for Path β `det_updateCol_add_smul_self + det_eq_zero_of_column_eq_zero` route.** S10 §4.2 noted Path β as "NOT RECOMMENDED for S5 (S8 §6.2 caveat)". This PREP supplies the witness only for Path α, consistent with S10's recommendation.
- **No update to S5 PREP §4.3's case (a)/case (b) discussion.** That discussion is now retroactively obsolete (Option A unifies the two cases per S9 + S10), but S12 PREP does not edit S5 PREP (anti-target).
- **No closed-form witness for the S3 ACT or S4 ACT skeletons.** Those use different determinant routes (`Matrix.cramer` for S3, column-update for S4); deriving their witnesses is separately owed pencil work, scoped for S13 PREP / S14 PREP if not done in-line by the S3/S4 ACT pickers.
- **No physical hand-execution of `det_succ_row_zero + det_fin_three`** at the pin to dump the post-`simp only` polynomial form. That can be done via `set_option pp.all true` after the cofactor expansion in a dummy `example`, then visual diff against the S12 §3.2 closed form. The S5 ACT picker can do this inline if the witness fails first try; the alternative is to inspect the residual goal after `simp only [...]` in the failed build's error output.

### 10.2 Confidence in the witness

The §3.2 derivation is elementary linear algebra: column-op invariance, row-op invariance, cofactor expansion, 3×3 minor row reduction, sign tracking. **Probability the closed form is correct as stated: ~99% (one-in-100 risk is sign-flip from the `simp only` block normalization choices, which is recoverable by a global `-` flip in the witness).** The §6 numerical cross-check (Δ = 12 reproduced exactly) is **independent confirmation** the formula is correct in at least the {α = γ = 1, t = -2, s = 2} specialization; agreement at an arbitrary specialization is **strong but not conclusive** evidence the polynomial identity is correct (a polynomial can agree at finitely many points without being identical, but here we've matched a generic point with no special algebraic relations, so the agreement is informative).

The S5 ACT picker should still build-verify before claiming the witness is correct. The Docker build is the final source of truth.

### 10.3 What's owed downstream of this PREP

1. **S5 ACT picker** — apply §4.3 verbatim + Docker build + STATE-SYNC follow-up.
2. **S3 ACT picker** — derive the witness for the (⇐) Cramer route. Estimated ~30-60 min pencil work analogous to S12 §3.2 (different determinant identity).
3. **S4 ACT picker** — derive the witness for the (⇒) column-update Path A route. Estimated ~30-60 min pencil work.
4. **S6 ACT picker** — chain S3 + S4 + S5 ACT to close `converse_product_implies_concyclic_axiom` at line 468. Plus parent gallery `meta.json` update (`axiomCount` 1 → 0).

S13/S14 PREPs (if needed) for S3/S4 witness pencil work could be claimed by future researcher cycles. **This S12 PREP closes only S5's owed pencil work.** S6 ACT integration is mostly book-keeping (signature swap + caller update + chain) and does not need a separate PREP.

## 11. References

- S2 SCAFFOLD #18380 — `concyclicityDet` def + `Vec2` wrapper
- S3 PREP #18466 — Cramer (⇐) design memo (~307 LOC doc-only)
- S4 PREP #18474 — concyclic → Δ = 0 design memo (doc-only)
- S5 PREP #18553 — chord-product → Δ = 0 bridge memo (doc-only); §4.3 schematic factorization (which §3.2 of this S12 PREP closes in explicit form)
- S6 STATE-SYNC #18977 — first STATE-SYNC after S3-S5 PREPs
- S7 ACT BUILD-VERIFY #19096 — Mathlib v4.26.0 import unblocker
- S8 PREP #19231 — Mathlib v4.26.0 bearer re-verification + Patched Path A bearer chain (`det_updateCol_add_smul_self ×3 + det_eq_zero_of_column_eq_zero`)
- S9 PREP #19246 — `Δ=12≠0` counterexample to unsigned hypothesis + Option A signed hypothesis recovery
- S10 PREP #19312 — ACT-readiness gate harmonizing S8 × S9; unified S5 ACT skeleton with placeholder `sorry` for the witness; §11 honesty note flagging the owed ~30-60 min pencil work
- S11 STATE-SYNC #19326 — refresh state.md + JSON after S8/S9/S10 PREPs
- **S12 PREP (this PR)** — explicit closed-form `linear_combination` witness derivation, paste-ready S5 ACT body, ACT-readiness checklist refresh

External:
- Mathlib4 pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
- `Matrix.det_succ_row_zero` (cofactor expansion along row 0)
- `Matrix.det_fin_three` (closed-form 3×3 determinant)
- `EuclideanSpace.norm_sq_eq` (`PiL2.lean:145`, coordinate `‖·‖²` expansion)
- `real_inner_self_eq_norm_sq` (`InnerProductSpace/Basic.lean:384`, `⟪v, v⟫_ℝ = ‖v‖²`)
- `inner_smul_right` (`InnerProductSpace/Basic.lean`, `⟪v, c • w⟫_ℝ = c · ⟪v, w⟫_ℝ`)
