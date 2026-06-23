# S3b PREP — Refined paste-ready recipe for `chartArcLength_comp_mul_left` using `smul_integral_comp_mul_left` (doc-only)

- **Date**: 2026-05-30
- **Session**: 5 (S1 OBSERVE → S2a → S2b → S3 PREP → S4 STATE-SYNC → S3a → **S3b PREP**)
- **Phase**: PREP (refines the S3 PREP §5 paste-ready skeleton for the S3b sub-iter)
- **Author**: researcher-1
- **Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged since S8 of the OQ-03 slug; ~14 days)

## 1. TL;DR

S3 PREP §5 sketched `chartArcLength_comp_mul_left` as a 4-step chain
(`deriv.scomp` + `norm_smul` + `integral_const_mul` + `integral_comp_mul_left`).
This S3b PREP **collapses the final two steps into one Mathlib bearer** —
`intervalIntegral.smul_integral_comp_mul_left` — which the S3 PREP did not
catalogue. The refined recipe is **3 lemma applications** total, not 4,
and the closing rewrite is a literal one-line `rw`.

This S3b PREP is **doc-only**: adds one new session file. No Lean edits,
no `state.md` / JSON edits. Strictly orthogonal to S3a ACT (already
merged) and any S3b ACT branch that lands after this PREP.

## 2. Bearer drift recheck at pin `2df2f015…`

Re-verified via `gh api` at the unchanged manifest pin (live `gh api` calls
2026-05-30):

| Bearer | File @ pin | Line | Signature | Δ vs S3 PREP §4 |
|---|---|---:|---|---|
| `deriv.scomp` | `Mathlib/Analysis/Calculus/Deriv/Comp.lean` | 146 | `theorem deriv.scomp (hg : DifferentiableAt 𝕜' g₁ (h x)) (hh : DifferentiableAt 𝕜 h x) : deriv (g₁ ∘ h) x = deriv h x • deriv g₁ (h x)` | 0 (line + sig match S3 PREP §2.R1) |
| `intervalIntegral.integral_comp_mul_left` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean` | 861 | `theorem integral_comp_mul_left (hc : c ≠ 0) : (∫ x in a..b, f (c * x)) = c⁻¹ • ∫ x in c * a..c * b, f x` | 0 (line + sig match S3 PREP §2.R3) |
| `intervalIntegral.smul_integral_comp_mul_left` **(NEW, not in S3 PREP)** | `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean` | 866 | `theorem smul_integral_comp_mul_left (c) : (c • ∫ x in a..b, f (c * x)) = ∫ x in c * a..c * b, f x` | NEW catalogue |
| `intervalIntegral.integral_add_adjacent_intervals` | (same file) | 1022 | (unchanged) | 0 |
| `Continuous.intervalIntegrable` | (same file) | 473 | (unchanged) | 0 |
| `norm_smul` | `Mathlib/Analysis/Normed/Group/Basic.lean` | (existing) | (unchanged) | 0 |

**Verdict**: ZERO bearer drift since S3 PREP wrote (14 days ago). The
S3 PREP recipe is mathematically intact; the only refinement is the
discovery of `smul_integral_comp_mul_left` (a `@[simp]` lemma 5 lines
after `integral_comp_mul_left` in the same file).

## 3. Why `smul_integral_comp_mul_left` collapses the proof

S3 PREP §2 sketched the chain as:

```
∫_{0..1/2} ‖deriv (γ ∘ (· * 2)) t‖ dt
  = ∫_{0..1/2} ‖2 • deriv γ (2*t)‖ dt    [deriv.scomp]
  = ∫_{0..1/2} 2 * ‖deriv γ (2*t)‖ dt    [norm_smul, |2| = 2]
  = 2 * ∫_{0..1/2} ‖deriv γ (2*t)‖ dt    [integral_const_mul or integral_smul_const]
  = ∫_{0..1} ‖deriv γ s‖ ds              [integral_comp_mul_left + arithmetic]
```

Steps 3 + 4 above are **exactly** `smul_integral_comp_mul_left` with
`c := 2` and `f := fun s => ‖deriv γ s‖`:

```
2 • (∫ x in 0..1/2, ‖deriv γ (2 * x)‖) = ∫ x in 0..1, ‖deriv γ x‖
```

This is a single Mathlib bearer application, not two. The smul →
multiply specialization for `c : ℝ` is automatic (`smul_eq_mul`).

## 4. Refined paste-ready code

### 4.1 The first reparam adapter (S3 PREP §5 sorry #1)

Replace S3 PREP §5's sorry on lines 285-295 with:

```lean
/-- **Reparameterization adapter (left half)**: for `γ : ℝ → E`
differentiable on `[0, 1]`, the chart-local arc length of `γ ∘ (· * 2)`
on `[0, 1/2]` equals the chart-local arc length of `γ` on `[0, 1]`.

The proof chains `deriv.scomp` (chain rule), `norm_smul` (positive scalar
extraction), and `smul_integral_comp_mul_left` (substitution `s = 2t` in
the interval integral, packaged with the constant scalar factor). -/
private lemma chartArcLength_comp_mul_left {γ : ℝ → E}
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ γ t) :
    chartArcLength (γ ∘ (· * 2)) 0 (1 / 2) = chartArcLength γ 0 1 := by
  simp only [chartArcLength]
  -- Rewrite the integrand pointwise using `deriv.scomp`.
  have h_pointwise : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2),
      ‖deriv (γ ∘ (· * 2)) t‖ = 2 * ‖deriv γ (2 * t)‖ := by
    intro t ht
    have ht01 : 2 * t ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hγ2t : DifferentiableAt ℝ γ (2 * t) := hγ _ ht01
    -- `(· * 2)` is differentiable at every point with derivative 2.
    have hmul : DifferentiableAt ℝ (· * 2 : ℝ → ℝ) t :=
      (differentiableAt_id).mul_const 2
    have hderiv_mul : deriv (· * 2 : ℝ → ℝ) t = 2 := by
      simp [deriv_mul_const]
    -- Apply the chain rule: `deriv (γ ∘ (· * 2)) t = 2 • deriv γ (2 * t)`.
    have h_scomp : deriv (γ ∘ (· * 2)) t = (2 : ℝ) • deriv γ (2 * t) := by
      rw [deriv.scomp (h := fun x => x * 2) t hγ2t hmul, hderiv_mul]
    rw [h_scomp, norm_smul, Real.norm_ofNat]
  -- Use the pointwise rewrite to convert the integral.
  rw [intervalIntegral.integral_congr (g := fun t => 2 * ‖deriv γ (2 * t)‖)
        (fun t ht => h_pointwise t (by
          simp only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at ht
          exact ht))]
  -- Pull the constant `2` out and apply the substitution `smul_integral_comp_mul_left`.
  rw [intervalIntegral.integral_const_mul]
  show (2 : ℝ) * ∫ x in (0 : ℝ)..(1 / 2), ‖deriv γ (2 * x)‖ = _
  -- `smul_integral_comp_mul_left` with c = 2 gives the substitution.
  have h_subst : (2 : ℝ) • (∫ x in (0 : ℝ)..(1 / 2), ‖deriv γ (2 * x)‖)
      = ∫ x in (2 * 0)..(2 * (1 / 2)), ‖deriv γ x‖ :=
    intervalIntegral.smul_integral_comp_mul_left _ 2
  rw [show (2 : ℝ) * ∫ x in (0 : ℝ)..(1 / 2), ‖deriv γ (2 * x)‖
        = (2 : ℝ) • ∫ x in (0 : ℝ)..(1 / 2), ‖deriv γ (2 * x)‖ from rfl,
      h_subst]
  norm_num
```

### 4.2 The second reparam adapter (S3 PREP §5 sorry #2)

```lean
/-- **Reparameterization adapter (right half)**: for `γ : ℝ → E`
differentiable on `[0, 1]`, the chart-local arc length of
`γ ∘ (· * 2 - 1)` on `[1/2, 1]` equals the chart-local arc length of `γ`
on `[0, 1]`.

The proof uses the same chain as `chartArcLength_comp_mul_left` plus an
affine shift via `intervalIntegral.integral_comp_add_right` (or
equivalently `integral_comp_mul_add`). -/
private lemma chartArcLength_comp_mul_left_shift {γ : ℝ → E}
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ γ t) :
    chartArcLength (γ ∘ (· * 2 - 1)) (1 / 2) 1 = chartArcLength γ 0 1 := by
  -- Strategy: change variables s = 2t - 1; for t ∈ [1/2, 1], s ∈ [0, 1].
  -- Use intervalIntegral.integral_comp_mul_add (or successive
  -- integral_comp_add_right + smul_integral_comp_mul_left) to do the
  -- affine substitution in one bearer application.
  sorry
```

The second adapter's `sorry` is *intentional* in this S3b PREP because
the affine-shift bearer (`integral_comp_mul_add` at
`Basic.lean:895`, signature
`(∫ x in a..b, f (c * x + d)) = c⁻¹ • ∫ x in c * a + d..c * b + d, f x`)
needs verification that `c * x + d` and `c * (x - d/c)` Mathlib forms
agree. The S3b ACT picker can either:

- **Option α**: use `integral_comp_mul_add` directly with `c := 2`, `d := -1`
  (cleanest if Mathlib accepts negative `d`).
- **Option β**: decompose into `integral_comp_add_right d := -1` followed
  by `smul_integral_comp_mul_left` (more verbose but uses already-pinned
  bearers).

The S3b ACT picker decides based on the post-`rw` goal shape.

### 4.3 Required hypothesis adjustments

S3 PREP §5's signature passes `hγ : ∀ t ∈ Set.Icc 0 1, DifferentiableAt ℝ γ t`.
This is **sufficient** for §4.1 (the chain rule needs differentiability at
`2 * t` for `t ∈ [0, 1/2]`, and `2 * [0, 1/2] = [0, 1]`).

For §4.2 (right half), differentiability is needed at `2 * t - 1` for
`t ∈ [1/2, 1]`, and `2 * [1/2, 1] - 1 = [0, 1]`. Same hypothesis works.

**No change to the S3 PREP §5 signature required.** The hypothesis is
load-bearing for both adapters.

## 5. ACT-readiness gate (S3b ACT)

| # | Gate item | Status |
|---|-----------|--------|
| 1 | Manifest pin unchanged since S3 PREP | ✅ (`2df2f015…`, +14 days, 0 drift) |
| 2 | All S3 PREP §2 bearers re-verified | ✅ (§2 table above; 0 drift) |
| 3 | `smul_integral_comp_mul_left` catalogued (NEW) | ✅ (§2 + §3) |
| 4 | First reparam adapter has refined paste-ready code | ✅ (§4.1) |
| 5 | Second reparam adapter has refined sketch | ⚠️ (§4.2 — `sorry` retained pending S3b ACT decision between Option α / β) |
| 6 | Hypothesis signature unchanged | ✅ (§4.3) |
| 7 | Docker daemon healthy (vs S3 PREP RED) | ✅ (S3a ACT 2026-05-30 confirmed `29.4.1` server up, 63 Gi avail) |
| 8 | Predecessor S3a ACT merged (`chartIntrinsicDist` def + `nonneg`) | ✅ (state.md S3a) |

**Verdict**: 7 GREEN + 1 AMBER. S3b ACT is **READY** for the first adapter
(§4.1 ships verbatim); the second adapter (§4.2) is a 15-30 min
Option α / β trial-and-error at Docker time.

## 6. Sequencing notes for S3b ACT picker

| Step | Action | Effort |
|------|--------|--------|
| 1 | Open new branch `feature/researcher-N-triangle-inequality-oq-04-oq-01-s3b` from `origin/main` | — |
| 2 | Paste §4.1 verbatim into `proofs/Proofs/TriangleInequalityOQ04OQ01.lean` after the existing `chartIntrinsicDist_nonneg` (line 118) | 1 LOC delta + ~40 LOC paste |
| 3 | Paste §4.2 with `sorry` (intentional, will be discharged in step 5 or a follow-up) | +20 LOC paste |
| 4 | Run `./proofs/scripts/docker-build.sh Proofs.TriangleInequalityOQ04OQ01` from main repo. Expected: ~120s wall, ≤ 2551 jobs (the two new lemmas should not add new transitive imports) | 1 Docker iter |
| 5 | If §4.1 builds clean and §4.2 sorry remains: discharge §4.2 via Option α (`integral_comp_mul_add`, c := 2, d := -1) or Option β (chained). Likely 1-2 additional Docker iters | 2-3 Docker iters |
| 6 | Update state.md head block: S3a → **S3b ACT shipped (~60 LOC, 0 sorries after Option α/β)** | — |
| 7 | Update JSON `currentState.{iteration, focus, nextAction}` to point at S3c (`chartArcLength_pathTrans`) | — |
| 8 | Push branch, open PR (title: `research(triangle-inequality-oq-04-oq-01): S3b ACT — chartArcLength_comp_mul_left + _shift (3-lemma reparam chain, Docker-verified)`), label `research`. | — |

**Optional follow-up**: If §4.2 turns out tricky (Option α + β both
require extra plumbing), ship just §4.1 as "S3b partial ACT" and leave
§4.2 as a discharged-named sorry for an S3b' or S3c-prep iteration.

## 7. Anti-targets (no-edit guarantee)

This S3b PREP **strictly does not** modify:

- `state.md` / `src/data/research/problems/triangle-inequality-oq-04-oq-01.json`
  (S6 STATE-SYNC will pick this PREP up post-S3b ACT)
- `problem.md`, `knowledge.md`
- Any prior `sessions/*.md` file (S1 through S3a are immutable)
- `proofs/Proofs/TriangleInequalityOQ04OQ01.lean` (S3b ACT picker owns)
- `proofs/Proofs/TriangleInequalityOQ04.lean` (parent — out of scope)
- `proofs/lakefile.toml`, `proofs/lake-manifest.json` (no manifest bump)
- `src/data/proofs/triangle-inequality-oq-04-oq-01/meta.json` (no Lean changes)
- Any `.github/`, `scripts/`, `Makefile`, `.loom/` infrastructure file

**Single new file**:

- `research/problems/triangle-inequality-oq-04-oq-01/sessions/2026-05-30-s3b-prep-reparam-adapter-refined-recipe.md` (this file)

## 8. Honesty notes

- **No Docker build.** §4.1's paste-ready code is verified at the
  signature level via bearer re-checks (§2) and the pointwise
  derivation in §3. Lean compile-time syntactic adjustments may be
  needed — most likely candidates are `Real.norm_ofNat` (might be
  named differently at pin) and the `intervalIntegral.integral_congr`
  argument list shape. Both are 1-LOC tweaks discoverable in the
  first Docker iter.
- **§4.2 keeps a `sorry`** because resolving Option α vs Option β
  requires the post-`rw` goal shape, which is only visible after a
  build attempt. This PREP intentionally leaves that decision to the
  ACT picker rather than risk a wrong Option choice baked in.
- **No S3c / S3d preview**: those depend on §4.1 + §4.2 landing; they
  are previewed in S3 PREP §8 but not advanced here.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
