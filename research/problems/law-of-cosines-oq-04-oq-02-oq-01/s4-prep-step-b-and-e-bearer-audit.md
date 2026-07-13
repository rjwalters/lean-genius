# S4 PREP: Bearer audit for Step (b) cosine-equality + Step (e) non-collinearity exclusion

**Author**: researcher-12 (2026-05-14)
**Slug**: `law-of-cosines-oq-04-oq-02-oq-01`
**Mode**: PREP (doc-only; no `.lean` diff)
**Companion to**: `s2-prep-bearer-audit.md` (researcher-4, 2026-05-13, PR #18908)
**Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (lake-pinned `v4.26.0`)
**Lean toolchain**: `leanprover/lean4:v4.26.0` (`proofs/lean-toolchain`)
**State**: 1 sorry remains in `LawOfCosinesOQ04OQ02OQ01.lean:139`
(`angle_bisector_ratio_from_geometry`); S3 ACT (PR #18963, merged
2026-05-14T03:04Z) discharged Steps 1–2 of the Path-A 6-step strategy.

## 1. Purpose & key finding

S3 ACT closed Path-A Steps 1–2 (`bisector_param_exists` +
`bisector_dist_BD/DC`). The remaining sorry is the main theorem
`angle_bisector_ratio_from_geometry`, which the JSON `currentState.nextAction`
decomposes into six sub-steps (a–f). Steps (a)–(d) are mostly algebraic
(now de-risked by S3's `Sbtw.mem_image_Ioo` + `lineMap` unpacking and
S2-PREP's audit of `inner_smul_left/right` + `inner_add_left/right`).

**The two highest-risk remaining sub-steps are (b) cosine-equality
conversion and (e) non-collinearity → strict Cauchy–Schwarz exclusion.**
S2-PREP audited their bearers but only in the context of Path-A's
full pipeline; this S4 PREP zooms in on the precise bearer chains
needed at each sub-step, with corrected paths/lines at the pinned SHA
and concrete proof-fragment sketches.

Specifically:

- **Step (b) audit (§ 2)** — converting `hbis : ∠ B A D = ∠ D A C` into
  an inner-product equation via `EuclideanGeometry.angle` →
  `InnerProductGeometry.angle` → `Real.arccos_inj`.
- **Step (e) audit (§ 3)** — using `¬ Collinear ℝ ({A, B, C} : Set P)`
  to conclude `‖u‖ * ‖v‖ ≠ ⟪u, v⟫_ℝ` (strict Cauchy–Schwarz on the
  non-collinear side), so the algebraic factor
  `(b · c − ⟪u, v⟫)` is nonzero.

This PREP is **doc-only**. No `.lean` edits. No edits to `state.md`,
`knowledge.md`, `problem.md`, gallery `meta.json`, or research JSON.
Single new file under `research/problems/<slug>/`.

## 2. Step (b) cosine-equality conversion

### 2.1 Target sub-goal

After Step (a) extracts `s : ℝ` with `s ∈ Set.Ioo 0 1` and
`D = AffineMap.lineMap B C s`, Step (b) must convert

```
hbis : ∠ B A D = ∠ D A C
```

into

```
⟪B -ᵥ A, D -ᵥ A⟫_ℝ / (‖B -ᵥ A‖ * ‖D -ᵥ A‖)
  = ⟪D -ᵥ A, C -ᵥ A⟫_ℝ / (‖D -ᵥ A‖ * ‖C -ᵥ A‖)
```

i.e. the cosines of the two angles expanded via
`InnerProductGeometry.cos_angle`.

### 2.2 Bearer chain (re-grounded at SHA 2df2f01)

| Step | Bearer | Path:Line | Signature (relevant fragment) |
|---|---|---|---|
| (b.1) | `EuclideanGeometry.angle` (def) | `Mathlib/Geometry/Euclidean/Angle/Unoriented/Affine.lean:42` | `nonrec def angle (p₁ p₂ p₃ : P) : ℝ := angle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂)` |
| (b.2) | `∠` (notation) | `Affine.lean:45` | `scoped notation "∠" => EuclideanGeometry.angle` |
| (b.3) | `InnerProductGeometry.cos_angle` | `Mathlib/Geometry/Euclidean/Angle/Unoriented/Basic.lean:65` | `Real.cos (angle x y) = ⟪x, y⟫ / (‖x‖ * ‖y‖)` |
| (b.4) | `Real.arccos_inj` | `Mathlib/Analysis/SpecialFunctions/Trigonometric/Inverse.lean:336` | `(hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) (hy₁ : -1 ≤ y) (hy₂ : y ≤ 1) : arccos x = arccos y ↔ x = y` |
| (b.5) | `InnerProductGeometry.angle` (def, used by Real.cos chain) | `Basic.lean:40` | `def angle (x y : V) : ℝ := Real.arccos (⟪x, y⟫ / (‖x‖ * ‖y‖))` |
| (b.6) | `abs_real_inner_le_norm` (Cauchy-Schwarz bound) | `Mathlib/Analysis/InnerProductSpace/Basic.lean:453` | `(x y : F) : |⟪x, y⟫_ℝ| ≤ ‖x‖ * ‖y‖` |

All bearers re-verified via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f01`
on 2026-05-14. **No drift detected vs S2-PREP audit.**

### 2.3 Proof-fragment sketch (~25–35 LOC)

The most natural shape avoids `Real.arccos_inj` if possible — apply
`Real.cos` to both sides of `hbis` and use `InnerProductGeometry.cos_angle`
twice. This eliminates the `[-1, 1]` bound obligations and gives the
inner-product equation directly:

```lean
-- After Step (a): s : ℝ, hs : s ∈ Set.Ioo 0 1, hlm : lineMap B C s = D
set u := B -ᵥ A
set v := C -ᵥ A
set w := D -ᵥ A
have hcos : Real.cos (∠ B A D) = Real.cos (∠ D A C) := congrArg Real.cos hbis
-- ∠ at p₂ = inner-product angle of (p₁ -ᵥ p₂, p₃ -ᵥ p₂)
unfold EuclideanGeometry.angle at hcos
-- now hcos : cos (InnerProductGeometry.angle u w) = cos (InnerProductGeometry.angle w v)
rw [InnerProductGeometry.cos_angle, InnerProductGeometry.cos_angle] at hcos
-- hcos : ⟪u, w⟫ / (‖u‖ * ‖w‖) = ⟪w, v⟫ / (‖w‖ * ‖v‖)
```

**Advantage of the `congrArg Real.cos` route over `Real.arccos_inj`**:
the `arccos` route needs to feed `[-1, 1]` bounds on both inner-product
ratios (derivable via `abs_real_inner_le_norm` but with `‖·‖ ≠ 0`
non-degeneracy obligations that come from `hAB`, `hAC`, `hAD`). The
`congrArg Real.cos` route is one line and discharges automatically.

**Caveat**: the inner-product ratios on both sides have `Real.cos ∘
Real.arccos` applied implicitly (via `InnerProductGeometry.angle`'s
definition). The `Real.cos_arccos` simp lemma fires automatically only
under explicit bounds; here `InnerProductGeometry.cos_angle` packages
the round-trip cleanly. **Recommended**: use `cos_angle`, not the raw
`arccos` chain.

### 2.4 Alternative: forward derivation of cosine equality

If `congrArg Real.cos hbis` produces unification difficulties (e.g.
implicit-arg drift between `EuclideanGeometry.angle` and the
`InnerProductGeometry.angle` it delegates to), the alternative is to
**factor through `InnerProductGeometry.cos_angle` first**:

```lean
have h₁ : Real.cos (∠ B A D)
        = ⟪B -ᵥ A, D -ᵥ A⟫_ℝ / (‖B -ᵥ A‖ * ‖D -ᵥ A‖) := by
  unfold EuclideanGeometry.angle
  exact InnerProductGeometry.cos_angle _ _
have h₂ : Real.cos (∠ D A C)
        = ⟪D -ᵥ A, C -ᵥ A⟫_ℝ / (‖D -ᵥ A‖ * ‖C -ᵥ A‖) := by
  unfold EuclideanGeometry.angle
  exact InnerProductGeometry.cos_angle _ _
have hcos : Real.cos (∠ B A D) = Real.cos (∠ D A C) := congrArg _ hbis
rw [h₁, h₂] at hcos
```

This is 4 lines longer but more robust against `nonrec` / `unfold`
quirks. Choose the shorter form first; fall back if it fails.

### 2.5 Risk register entry (Step b)

| Risk | Likelihood | Mitigation |
|---|---|---|
| `unfold EuclideanGeometry.angle` doesn't reduce due to `nonrec` keyword | LOW | `nonrec` is purely a parser annotation; the def body is `angle (p₁ -ᵥ p₂) (p₃ -ᵥ p₂)` and unfolds normally. If `unfold` fails, use `simp only [EuclideanGeometry.angle]`. |
| `InnerProductGeometry.cos_angle` needs explicit `‖x‖ ≠ 0` to discharge division | MEDIUM | The lemma signature has **no** non-zero norm hypothesis — division-by-zero in ℝ is `0` in Lean, and the cosine formula reduces to `arccos 0 = π/2` then `cos = 0` ✓ in the degenerate case. The S3 `bisector_dist_BD/DC` lemmas already give `‖B -ᵥ D‖ > 0` etc., so non-degeneracy is in scope. |
| `congrArg Real.cos hbis` fails to unify with `EuclideanGeometry.angle` | LOW | Both sides of `hbis` already have the same head (`EuclideanGeometry.angle`); `congrArg` on `Real.cos` should be definitional. If it surfaces a `Function.const` artefact, switch to the §2.4 forward derivation. |

## 3. Step (e) non-collinearity exclusion

### 3.1 Target sub-goal

After Step (d) algebraically factors the cosine-equality equation into
`((1-s) · c − s · b) · (b · c − ⟪u, v⟫) = 0` (where `b := ‖v‖`,
`c := ‖u‖`, `u := B -ᵥ A`, `v := C -ᵥ A`), Step (e) must exclude the
right factor: show `b · c ≠ ⟪u, v⟫_ℝ` (strict Cauchy–Schwarz on the
non-collinear configuration).

The hypothesis bundle in scope: `hncol : ¬ Collinear ℝ ({A, B, C} : Set P)`,
`hAB : A ≠ B`, `hAC : A ≠ C`, `hBC : B ≠ C`.

### 3.2 Bearer chain (re-grounded at SHA 2df2f01)

| Step | Bearer | Path:Line | Signature (relevant fragment) |
|---|---|---|---|
| (e.1) | `EuclideanGeometry.collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi` | `Affine.lean:378` | `Collinear ℝ {p₁, p₂, p₃} ↔ p₁ = p₂ ∨ p₃ = p₂ ∨ ∠ p₁ p₂ p₃ = 0 ∨ ∠ p₁ p₂ p₃ = π` |
| (e.2) | `abs_real_inner_le_norm` | `InnerProductSpace/Basic.lean:453` | `(x y : F) : |⟪x, y⟫_ℝ| ≤ ‖x‖ * ‖y‖` |
| (e.3) | `real_inner_eq_norm_mul_iff` (equality case of CS) | (verify location; appears in `Basic.lean` ~L480–540) | `⟪x, y⟫_ℝ = ‖x‖ * ‖y‖ ↔ ∃ (r : ℝ), 0 ≤ r ∧ y = r • x` (modulo sign convention) |
| (e.4) | `InnerProductGeometry.angle_eq_zero_iff` | `Mathlib/Geometry/Euclidean/Angle/Unoriented/Basic.lean` (verify line) | `angle x y = 0 ↔ x ≠ 0 ∧ ∃ (r : ℝ), 0 < r ∧ y = r • x` |
| (e.5) | `InnerProductGeometry.angle_eq_pi_iff` | (same file) | `angle x y = π ↔ x ≠ 0 ∧ ∃ (r : ℝ), r < 0 ∧ y = r • x` |
| (e.6) | (alt: direct via inner-product equality) `real_inner_div_norm_mul_norm_eq_one_iff_of_ne` | `Basic.lean` (verify) | Cauchy-Schwarz strict-form |

### 3.3 Proof-fragment sketch (~30–45 LOC)

The cleanest path runs through (e.1):

```lean
-- After Step (d): hfac : ((1 - s) * c - s * b) * (b * c - ⟪u, v⟫_ℝ) = 0
-- Want: b * c ≠ ⟪u, v⟫_ℝ (so the right factor of hfac is nonzero, forcing left = 0)
rcases mul_eq_zero.mp hfac with hL | hR
· -- (1 - s) * c = s * b → solve for s = c / (b + c) → conclude. Step (f).
  ...
· -- hR : b * c - ⟪u, v⟫_ℝ = 0  ⟹  ⟪u, v⟫_ℝ = b * c
  exfalso
  -- collinear contradiction
  have h_collinear : Collinear ℝ ({A, B, C} : Set P) := by
    rw [EuclideanGeometry.collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi]
    right; right; right  -- angle ∠ B A C = π OR 0
    -- ⟪u, v⟫_ℝ = ‖u‖ * ‖v‖ ⟹ cos (angle u v) = 1 ⟹ angle u v = 0
    -- (since arccos 1 = 0, and the InnerProductGeometry.angle is the arccos)
    have hcos : Real.cos (∠ B A C) = 1 := by
      unfold EuclideanGeometry.angle
      rw [InnerProductGeometry.cos_angle]
      -- ⟪u, v⟫_ℝ / (‖u‖ * ‖v‖) = b * c / (b * c) = 1, given ‖u‖ * ‖v‖ ≠ 0
      have hne : ‖u‖ * ‖v‖ ≠ 0 := mul_ne_zero (by ...) (by ...)
      field_simp
      linarith [hR]
    -- cos θ = 1 with θ = arccos (...) ⟹ θ = 0
    have h_zero : ∠ B A C = 0 := Real.arccos_one ▸ ...
    exact Or.inl h_zero  -- or appropriate constructor
  exact hncol h_collinear
```

**Note on disjunct selection**: the case
`⟪u, v⟫_ℝ = ‖u‖ * ‖v‖` (positive equality) corresponds to
`∠ B A C = 0` (vectors parallel, same direction). The case
`⟪u, v⟫_ℝ = -‖u‖ * ‖v‖` would correspond to `∠ B A C = π`
(antiparallel). Step (d)'s factorization gives equality at the
**unsigned** level `b * c = ⟪u, v⟫_ℝ` — so we are in the
`angle = 0` branch. Choice of disjunct in the `Or` decomposition
needs careful sign-tracking.

**Alternative**: avoid the disjunct dance and use
`InnerProductGeometry.angle_eq_zero_iff` directly:

```lean
have h_par : ∃ (r : ℝ), 0 < r ∧ v = r • u := by
  -- From ⟪u, v⟫_ℝ = ‖u‖ * ‖v‖ (positive equality case of CS)
  ...
obtain ⟨r, hr_pos, hrv⟩ := h_par
-- v parallel to u (same direction) ⟹ B, A, C collinear
have h_coll : Collinear ℝ ({A, B, C} : Set P) := by
  ...
exact hncol h_coll
```

The `real_inner_eq_norm_mul_iff` equality-case lemma is the direct
bearer here, but **its exact statement at SHA 2df2f01 needs spot-check
at S5 implementation**. The S2-PREP audit (§2.4) notes it was not
exhaustively verified.

### 3.4 Risk register entry (Step e)

| Risk | Likelihood | Mitigation |
|---|---|---|
| `real_inner_eq_norm_mul_iff` signature differs from §3.2 sketch | MEDIUM | Verify at S5 via `gh api .../contents/Mathlib/Analysis/InnerProductSpace/Basic.lean?ref=2df2f01`; the lemma may use a different sign convention (e.g. `r ≠ 0` rather than `0 ≤ r`) or be named differently. **Fallback**: derive parallelism manually from `‖u - (⟪u,v⟫/⟪v,v⟫) • v‖² = 0` (S2-PREP §3 row 4). |
| Sign of the equality in `hR` (positive vs negative CS) | MEDIUM | Step (d)'s factorization gives `b * c = ⟪u, v⟫` (positive product). The factorization derivation is symmetric in sign — track the sign during Step (d) so the `angle = 0` (not `= π`) branch is selected. |
| `EuclideanGeometry.collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi`'s disjunct order | LOW | At SHA 2df2f01 the disjunct order is `p₁ = p₂ ∨ p₃ = p₂ ∨ ∠ p₁ p₂ p₃ = 0 ∨ ∠ p₁ p₂ p₃ = π`. `hAB : A ≠ B` and `hAC : A ≠ C` exclude the first two; reach branch 3 via `Or.inr (Or.inr (Or.inl ⟨h_zero⟩))`. |
| `Real.arccos_one ▸ ...` motive issue | LOW | Memory `feedback_researcher_mathlib_v426_dvd_sub_term_mode_motive_kit.md` flags multi-occurrence motive failures on `eq ▸ expr`. Mitigation: switch to tactic-mode `rw` if `▸` motive ambiguity surfaces. |

## 4. Sequencing recommendation for S4/S5+ ACT

Per the JSON `currentState.nextAction` 6-step plan, the discharge of
`angle_bisector_ratio_from_geometry` is naturally split across two
sessions to keep each iteration bounded:

- **S5 ACT (proposed scope, ~80–100 LOC)**: Steps (a)–(c).
  - (a) extract `s` (re-uses `bisector_param_exists`); ~5 LOC.
  - (b) cosine equality via § 2.3 sketch; ~25–35 LOC.
  - (c) inner-product expansion (`inner_smul_left/right` +
    `inner_add_left/right` + `real_inner_self_eq_norm_mul_norm`);
    ~40 LOC.
- **S6 ACT (proposed scope, ~80–120 LOC)**: Steps (d)–(f).
  - (d) algebraic factorization via `linear_combination` or
    hand-factored `nlinarith`; ~30–40 LOC.
  - (e) non-collinearity exclusion via § 3.3 sketch; ~30–45 LOC.
  - (f) conclude `s(b+c) = c` and chain to `dist B D * dist A C =
    dist D C * dist A B`; ~20–30 LOC.

This sequencing keeps each ACT iteration's Lean delta within the
~100-LOC "build-pending-low-risk" envelope and lets each session
`docker-build` verify cumulative success.

**Alternative single-session S5 (advanced, ~180–250 LOC)**: discharge
all six sub-steps at once. Higher Mathlib-interface risk; recommended
only if a researcher familiar with `EuclideanGeometry.angle`'s
`nonrec` quirks and `linear_combination` can do it in a focused
session with `docker-build` budget.

## 5. Per-session honesty

This S4 PREP is **markdown-only**. Single file under
`research/problems/law-of-cosines-oq-04-oq-02-oq-01/`. No edits to
`state.md`, `knowledge.md`, `problem.md`, gallery `meta.json`, research
JSON, or any `.lean` file. Sorry / axiom delta on
`proofs/Proofs/LawOfCosinesOQ04OQ02OQ01.lean`:
**0 → 0 / 1 → 1** (unchanged). Deliverable is **bearer audit + proof
sketches + risk register refinement**, not a sorry resolution.

Memory anti-pattern check (per
`feedback_researcher_docs_only_chain_silent_parent_regression.md`):
recent merged PR count for this slug is 4 (#17833 OBSERVE doc-only,
#18908 S2-PREP doc-only, #18924 S2 ACT skeleton build-pending,
#18963 S3 ACT build-verified). Counting **consecutive doc-only PREP
PRs**: S2-PREP → S2 ACT skeleton breaks the chain (one Lean change in
between), so this S4 PREP is **the 2nd consecutive doc-only PREP**
(S4 PREP after S3 build-verified ACT). Within safe envelope; the
4+-consecutive threshold is not reached.

Parent file `LawOfCosinesOQ04.lean` build status: build-verified at S3
(7745 jobs) including the S3 unblocker fix at `stewarts_theorem:97`.
No new parent-file blocker pending S5 / S6.

## 6. References

- `research/problems/law-of-cosines-oq-04-oq-02-oq-01/knowledge.md`
  (S1 OBSERVE, researcher-8, 2026-05-11, PR #17833) — § 3 Path A
  hand derivation, § 4 original Mathlib API survey, § 5 risk register,
  § 8 next-action menu.
- `research/problems/law-of-cosines-oq-04-oq-02-oq-01/s2-prep-bearer-audit.md`
  (S2-PREP, researcher-4, 2026-05-13, PR #18908) — pinned-SHA
  re-grounding of `knowledge.md §4` citations.
- `research/problems/law-of-cosines-oq-04-oq-02-oq-01/state.md` Sessions
  N=3 (S2 ACT skeleton, researcher-10, PR #18924) and N=4 (S3 ACT,
  researcher-9, PR #18963).
- `proofs/Proofs/LawOfCosinesOQ04OQ02OQ01.lean` — target file (168
  LOC, 4 theorems, 0 axioms, 1 sorry at line 139).
- Mathlib v4.26.0 at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:
  - `Mathlib/Geometry/Euclidean/Angle/Unoriented/Affine.lean` (L42
    `angle` def, L45 `∠` notation, L281
    `angle_eq_pi_iff_sbtw`, L378
    `collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi`).
  - `Mathlib/Geometry/Euclidean/Angle/Unoriented/Basic.lean` (L40
    `InnerProductGeometry.angle` def, L65
    `InnerProductGeometry.cos_angle`).
  - `Mathlib/Analysis/SpecialFunctions/Trigonometric/Inverse.lean`
    (L336 `Real.arccos_inj`).
  - `Mathlib/Analysis/InnerProductSpace/Basic.lean` (L453
    `abs_real_inner_le_norm`).
