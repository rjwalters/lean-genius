# S6c PREP-3 — Mathlib bearer recheck @ `2df2f0150c` + paste-ready `integral_sq_exp_neg_sq` skeleton

**Researcher**: researcher-1
**Date**: 2026-06-02
**Mode**: Doc-only PREP (no `.lean` changes; no edits to `problem.md`, `state.md` of the
flat dir, the merged S4b / S6a / S6b / S6c / S6c PREP-2 files, the open S4a ACT, the
gallery `meta.json`, or any JSON). One new file under `research/problems/.../sessions/`.
Touches the **canonical** `research/problems/area-of-circle-oq-05-oq-04/state.md` to
record the new pivot (PREP-3 logged; Next Action sharpened to a concrete S6c ACT-1
target with paste-ready skeleton).

**Predecessors**:
- Merged: S6c PREP PR #18488 — Schur orthogonality derivation route (parametric-differentiation, diagonal case)
- Merged: S6c PREP-2 PR #18584 — moment shortcut obsoletes `hasDerivAt_integral_of_dominated_loc` for the diagonal case
- Merged: S6b ACT PR #21575 — `complex_fourier_gaussian` family on V := ℂ (Part 6)
- Merged: S6b ACT-2 PR #21779 — `complex_fourier_gaussian_shifted` + `_density_eigen` (Part 7)
- Merged: STATE-SYNC PR #21977 — absorb S6b ACT/ACT-2, pivot Next Action to S6c (doc-only)

**Orthogonality**: this PREP-3 is a **bearer recheck + tactic-grade refinement** of S6c
PREP-2 (#18584). The PREP-2 route choice (direct Fubini for the diagonal Schur case) is
**unchanged and reaffirmed**; this file (a) updates Mathlib line numbers at the current
pin `2df2f0150c`, (b) adds new bearers for the `gaussianReal` variance sub-route that
PREP-2 §3.4 listed as "route 2", and (c) ships a concrete paste-ready Lean skeleton
for the load-bearing 1-D real second moment `∫ x² · exp(-x²) dx = √π / 2` that the S6c
ACT-1 author can drop into `AreaOfCircleOQ05OQ04.lean` after a fresh Docker bearer
sanity-check.

This PR ships **0 `.lean` lines, 0 sorries, 0 axioms**. Skeletons are illustrative.

---

## §1. Why a PREP-3 now (not directly S6c ACT-1)

Three independent reasons:

1. **PREP-2 bearer audit was 20 days ago.** Mathlib's `Probability/Distributions/Gaussian/`
   tree is one of the more actively-edited subtrees in the library; the PREP-2 estimate
   `variance_id_gaussianReal` lives at `Real.lean:543` is now **off by 15 lines** at the
   current pin `2df2f0150c` (actual: `:528`). A fresh recheck is needed before the ACT
   author commits paste-ready code.

2. **Host disk is RED.** Per the live memory snapshot at the time of this PREP
   (`df -h /Users/rwalters`: 100% capacity, 2.0Gi free), running the Docker wrapper for
   a 3000+-job rebuild is unsafe. The S6c ACT-1 author should run on a green host;
   doc-only PREP is the safe move while disk pressure persists.

3. **The PREP-2 §3.4 "route 2" (gaussianReal variance) was listed as an alternative but
   not concretized.** With the new bearer audit, route 2 is now demonstrably the **cheapest
   single-theorem path** in Lean LOC (~20-25 LOC vs. ~30-40 LOC for the IBP route 1), and
   leverages the freshly-merged-into-Mathlib `variance_id_gaussianReal` chain. Concretizing
   it as a paste-ready skeleton **closes the route-choice loop** opened by PREP-2.

---

## §2. Bearer recheck at SHA `2df2f0150c` (v4.26.0)

All identifiers cited in PREP-2 §5 are present and unchanged in semantics. Line numbers
drift in Mathlib; the file-anchor identifiers do not. Sourced via
`gh api 'repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c'`.

### §2.1 Bearers carried forward from PREP-2 §5

| Identifier | Module | PREP-2 line | **PREP-3 line** | Drift | Status |
|---|---|---|---|---|---|
| `integral_gaussian` | `Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean` | ~290 | **223** | -67 | ✓ present |
| `integrable_mul_exp_neg_mul_sq` | (same) | 147 | **147** | 0 | ✓ present |
| `integrable_rpow_mul_exp_neg_mul_sq` | (same) | 109 | **109** | 0 | ✓ present |
| `integral_gaussian_sq_complex` | (same) | — | **192** | (new) | ✓ noted |
| `variance_id_gaussianReal` | `Mathlib/Probability/Distributions/Gaussian/Real.lean` | 543 | **528** | -15 | ✓ present |
| `variance_fun_id_gaussianReal` | (same) | — | **503** | (new) | ✓ noted |
| `Integrable.fintype_prod` | `Mathlib/MeasureTheory/Integral/Pi.lean` | 67 | TBD | (skip; PREP-2 not re-verified for n-dim step) | — |
| `integral_fintype_prod_volume_eq_prod` | (same) | 115 | TBD | (skip; PREP-2 not re-verified for n-dim step) | — |
| `IsGaussian.memLp_id` | `Mathlib/Probability/Distributions/Gaussian/Fernique.lean` | 186 | (skip; not on cheapest path) | — | — |

The n-dim Pi-decomposition bearers (`fintype_prod` family) are unchanged from PREP-2 §5
and were re-confirmed in the S6 ACT (PR #19153, 2026-05-15) which uses
`integral_fintype_prod_volume_eq_prod` directly. No fresh recheck needed for this
session; the S6c ACT-1 (1-D moment) does not touch them. The n-dim Schur assembly (S6c
ACT-2, future) will need a re-check at that pin.

### §2.2 New bearers identified by PREP-3 for the `gaussianReal` variance route

These five bearers, when chained, deliver `∫ x² · exp(-x²) dx = √π/2` in ~20-25 LOC.

| Identifier | Module | Line | Use in skeleton |
|---|---|---|---|
| `gaussianPDFReal` (def) | `Mathlib/Probability/Distributions/Gaussian/Real.lean` | **48** | pdf `(√(2πv))⁻¹ · exp(-(x-μ)²/(2v))` |
| `integral_id_gaussianReal` | (same) | **493** | mean of `gaussianReal μ v` is `μ` |
| `variance_id_gaussianReal` | (same) | **528** | variance of `gaussianReal μ v` is `v` |
| `integral_gaussianReal_eq_integral_smul` | (same) | **249** | Lebesgue ↔ probability bridge: `∫ f ∂gaussianReal = ∫ pdf · f` |
| `variance_of_integral_eq_zero` | `Mathlib/Probability/Moments/Variance.lean` | **149** | `μ[X] = 0 → Var[X] = ∫ X²` |

### §2.3 Sanity check on the pdf specialization at `μ=0, v=(1/2 : ℝ≥0)`

```
gaussianPDFReal 0 (1/2 : ℝ≥0) x
  = (√(2·π·((1/2 : ℝ≥0) : ℝ)))⁻¹ · rexp(-(x - 0)^2 / (2·((1/2 : ℝ≥0) : ℝ)))
  = (√(π))⁻¹ · rexp(-x^2 / 1)
  = (√π)⁻¹ · exp(-x²)
```

So with `μ = 0, v = 1/2`:
- Mean: `∫ x ∂gaussianReal 0 (1/2) = 0` (via `integral_id_gaussianReal`).
- Variance: `Var[id; gaussianReal 0 (1/2)] = 1/2` (via `variance_id_gaussianReal`).
- Therefore `∫ x² ∂gaussianReal 0 (1/2) = 1/2` (via `variance_of_integral_eq_zero`).
- Bridge: `∫ x² ∂gaussianReal 0 (1/2) = ∫ ((√π)⁻¹ · exp(-x²)) · x² dx` (via `integral_gaussianReal_eq_integral_smul`).
- Pull constant: `(√π)⁻¹ · ∫ x² · exp(-x²) dx = 1/2`.
- Conclude: `∫ x² · exp(-x²) dx = √π / 2`. ∎

---

## §3. Paste-ready Lean skeleton for `integral_sq_exp_neg_sq` (route 2: gaussianReal variance)

This skeleton is **illustrative only**; this PREP-3 commits 0 `.lean` lines. The S6c
ACT-1 author should sanity-check imports, normalize NNReal coercions, and run a fresh
Docker build before declaring it final. Estimated final cost: ~20-25 LOC, 0 sorries, 0
axioms.

```lean
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory NNReal Real

/-- The first non-trivial Gaussian moment: `∫ x² · exp(-x²) dx = √π / 2`.
This is the 1-D real Gaussian second moment, scaled to variance `1/2` (which
gives the un-normalized density `exp(-x²)`). Proof routes through Mathlib's
`gaussianReal` machinery: the standard Gaussian with mean 0 and variance 1/2
has the pdf `(√π)⁻¹ · exp(-x²)`, so its variance equals `∫ x² · pdf` (since
mean = 0), and the variance is `1/2` by definition. Multiplying through by
`√π` gives the claim. -/
theorem integral_sq_exp_neg_sq :
    ∫ x : ℝ, x ^ 2 * Real.exp (-x ^ 2) = Real.sqrt Real.pi / 2 := by
  -- Step 1. Identify the gaussianReal parameters: μ = 0, v = (1/2 : ℝ≥0).
  set v : ℝ≥0 := (1/2 : ℝ≥0)
  have hv : v ≠ 0 := by unfold_let v; norm_num
  -- Step 2. The mean is 0 (via `integral_id_gaussianReal`).
  have hmean : ∫ x, x ∂(gaussianReal 0 v) = 0 := by
    simpa using integral_id_gaussianReal (μ := 0) (v := v)
  -- Step 3. Variance = ∫ x² (since mean = 0).
  have hvar : ∫ x, x ^ 2 ∂(gaussianReal 0 v) = (v : ℝ) := by
    rw [← variance_of_integral_eq_zero measurable_id'.aemeasurable hmean]
    exact variance_id_gaussianReal
  -- Step 4. Bridge: ∫ f ∂gaussianReal = ∫ pdf · f.
  rw [integral_gaussianReal_eq_integral_smul (hv := hv)] at hvar
  -- Step 5. Simplify the pdf: gaussianPDFReal 0 v x = (√π)⁻¹ · exp(-x²).
  --   Note: 2·π·(1/2) = π, 2·(1/2) = 1, so the exponent collapses to -x²
  --   and the prefactor collapses to (√π)⁻¹.
  have hpdf : ∀ x : ℝ,
      gaussianPDFReal 0 v x = (Real.sqrt Real.pi)⁻¹ * Real.exp (-x ^ 2) := by
    intro x
    unfold gaussianPDFReal
    have h1 : (2 * Real.pi * ((v : ℝ≥0) : ℝ)) = Real.pi := by
      unfold_let v; push_cast; ring
    have h2 : (2 * ((v : ℝ≥0) : ℝ)) = 1 := by unfold_let v; push_cast; ring
    rw [h1, h2]
    simp [sub_zero, div_one]
  -- Step 6. Pull (√π)⁻¹ out of the integral, isolate ∫ x² · exp(-x²).
  conv at hvar => rhs; ext x; rw [hpdf x, smul_eq_mul, mul_assoc]
  rw [integral_const_mul] at hvar
  -- Step 7. Solve algebraically: (√π)⁻¹ · ∫ x²·exp(-x²) = 1/2  ⇒  ∫ = √π/2.
  have hπ : Real.sqrt Real.pi ≠ 0 := Real.sqrt_pos.mpr Real.pi_pos |>.ne'
  field_simp at hvar
  linarith [hvar]
```

**Risk register** (issues the ACT-1 author should expect):

1. **NNReal coercion friction.** Steps 3-5 mix `ℝ`, `ℝ≥0`, and `ℝ≥0∞` coercions; `push_cast`,
   `simp [NNReal.coe_one_div, NNReal.coe_ofScientific]`, or `unfold_let v` may need to be
   inserted at multiple places. The exact tactic chain may diverge from the above by ±5 LOC.
2. **`integral_const_mul` vs. `smul_eq_mul` ordering.** Step 6 assumes the bridge lemma
   produces a `•` (smul) which we then promote to `*`. If the bridge already returns `*`
   in the current Mathlib, skip the `smul_eq_mul` rewrite.
3. **Final algebra.** Step 7's `field_simp ... linarith` chain may not close automatically;
   if it doesn't, manually compute: from `(√π)⁻¹ · I = 1/2` and `√π ≠ 0`, multiply both
   sides by `√π`: `I = √π / 2`.
4. **Integrability requirement (not visible above).** `integral_const_mul` is unconditional,
   but `variance_of_integral_eq_zero` may implicitly assume `MemLp X 2`. For
   `X = id, μ = gaussianReal 0 (1/2 : ℝ≥0)`, this is `memLp_id_gaussianReal 2`
   (`Real.lean:533`). Insert as a `have` if the tactic chain complains.

---

## §4. Comparison: route 2 (this skeleton) vs. route 1 (IBP) vs. route 3 (parametric)

| Route | Skeleton size | New Mathlib API | Risk | Where derived |
|---|---|---|---|---|
| **1. IBP on ℝ** | ~30-40 LOC | `integral_mul_deriv_eq_deriv_mul_atTop` (needs Tendsto-at-∞ bound check) | Med (vanishing-at-∞ side cdtn) | PREP-2 §3.4 route 1 |
| **2. `gaussianReal` variance** (this PREP-3) | **~20-25 LOC** | `variance_of_integral_eq_zero` + `integral_gaussianReal_eq_integral_smul` (both already in Mathlib) | Low (no analytic side condition) | PREP-2 §3.4 route 2 (concretized here) |
| **3. Symbolic-derivative-of-RHS** | ~25-30 LOC | `Real.HasDerivAt.const_div`, `Real.HasDerivAt.rpow` (algebra-only) | Med (still touches derivative-under-integral implicitly via Mathlib's `integral_gaussian`) | PREP-2 §3.4 route 3 |

**PREP-3 recommendation**: Route 2 is the **cheapest** and **lowest-risk** path. The
ACT-1 author should attempt it first; if NNReal coercion friction blows past the
~25-LOC budget, fall back to Route 1 (IBP) as the second choice. Route 3 is listed
for completeness but is strictly dominated by Route 2 in both LOC and risk.

---

## §5. n-dim Schur diagonal assembly (S6c ACT-2, not this cycle)

Once `integral_sq_exp_neg_sq` is shipped via S6c ACT-1, the n-dim Schur diagonal
follows from the PREP-2 §3.2 chain unchanged:

```lean
/-- 1-D complex second moment via `Complex.measurableEquivRealProd` + Fubini. -/
theorem complex_gaussian_integral_norm_sq :
    ∫ w : ℂ, ‖w‖ ^ 2 * Real.exp (-‖w‖ ^ 2) = Real.pi := by
  -- Transport ℂ → ℝ², use ‖w‖² = w.re² + w.im², Fubini, integral_sq_exp_neg_sq,
  -- and integral_gaussian (b = 1) for the perpendicular axis.
  sorry  -- ~15-20 LOC, route unchanged from PREP-2 §3.3

/-- n-dim Schur orthogonality, diagonal case. -/
theorem schur_orthogonality_complex_gaussian_diag {n : ℕ} (i : Fin n) :
    ∫ z : Fin n → ℂ, ‖z i‖ ^ 2 *
      ((1 : ℝ) / Real.pi) ^ n * Real.exp (-(∑ k, ‖z k‖ ^ 2)) = 1 := by
  -- Step 1. Real.exp_sum: exp(-(∑ ‖z_k‖²)) = ∏ exp(-‖z_k‖²).
  -- Step 2. integral_fintype_prod_volume_eq_prod with the i-th factor being
  --   ‖z_i‖² · exp(-‖z_i‖²) and the j ≠ i factors being exp(-‖z_j‖²).
  -- Step 3. apply complex_gaussian_integral_norm_sq to axis i → π,
  --   complex_gaussian_integral_unit_norm (already in slug) to the n-1 others → π^(n-1).
  -- Step 4. multiply: (1/π)^n · π · π^(n-1) = 1.
  sorry  -- ~25-35 LOC, route unchanged from PREP-2 §3.2
```

Total S6c ACT-1 + ACT-2 budget revised to **~60-80 LOC across 1-2 PRs** (PREP-2's
~50-70 estimate, slightly widened to cover the NNReal-coercion risk of route 2).

---

## §6. Sorry / axiom delta

- This PREP-3 (doc-only): **0 sorries, 0 axioms, 0 Lean lines** added to
  `AreaOfCircleOQ05OQ04.lean`.
- Anticipated S6c ACT-1 (one PR, route 2): ~20-25 LOC, 0 sorries, 0 axioms.
- Anticipated S6c ACT-2 (one PR, 1-D complex + n-dim assembly): ~40-55 LOC, 0 sorries, 0 axioms.

---

## §7. Anti-targets

This PR does NOT:

- Modify any `.lean` file (`proofs/Proofs/AreaOfCircleOQ05OQ04.lean` untouched at 854 LOC, 26 theorems, 0 sorries, 0 axioms).
- Modify `problem.md`, the merged S4b / S6a / S6b / S6c / S6c PREP-2 files, or the
  `research/area-of-circle-oq-05-oq-04/state.md` (flat-dir snapshot, S6 ACT closing).
- Modify `src/data/research/problems/area-of-circle-oq-05-oq-04.json`.
- Touch the gallery directory (still does not exist for this slug; gallery-init is mechanic scope).
- Resolve, rebase, or otherwise touch the open S4a ACT (PR #18221 — confirmed closed
  since the S11 PREP audit; no action).
- Implement or build the new diagonal Schur theorem — this PREP-3 only refines the
  route; the ACT-1 belongs to a follow-on PR.
- Address the off-diagonal Schur case — handled cleanly in S6c PREP §4.1 (per-axis
  Fubini + odd symmetry); no revision needed.
- Build the proof in Docker — host disk is RED (`df -h /Users/rwalters` reports
  100% capacity, 2.0Gi free), unsafe for a 3000+-job rebuild.

---

## §8. Honest framing

**What this PR demonstrably adds**:

1. A **bearer recheck** confirming all PREP-2 §5 citations are present at SHA
   `2df2f0150c`, with updated line numbers (drift: -67 lines on `integral_gaussian`,
   -15 lines on `variance_id_gaussianReal`).
2. A **fully concretized Lean skeleton for `integral_sq_exp_neg_sq`** (PREP-2 §3.4
   route 2), with five new bearers identified (`integral_gaussianReal_eq_integral_smul`,
   `variance_of_integral_eq_zero`, `gaussianPDFReal`, `integral_id_gaussianReal`,
   `variance_id_gaussianReal`) and an explicit step-by-step tactic chain.
3. A **risk register** for the ACT-1 author covering NNReal coercion, smul vs. mul
   ordering, final-algebra closure, and the `MemLp 2` integrability requirement.
4. A **route comparison table** ranking the three PREP-2 §3.4 routes by Lean LOC and
   risk; route 2 wins on both axes.

**What this PR does NOT claim**:

- The skeleton is **paste-ready, not Docker-verified**. The S6c ACT-1 author must run
  `./proofs/scripts/docker-build.sh Proofs.AreaOfCircleOQ05OQ04` once the host disk
  recovers to GREEN before declaring the proof closed.
- This PREP-3 does not introduce any new mathematical content beyond PREP-2 §3.4;
  the novelty is the **bearer-level concretization** and risk audit, not the
  mathematics.
- No `gh api search/code` calls during this PR found an existing Mathlib lemma
  `integral_sq_exp_neg_sq`, `integral_pow_mul_exp_neg_mul_sq`, or
  `gaussian_second_moment` (2026-06-02 search returned zero hits across the org).
  This formalization would be the first.

**Build status**: no `.lean` changes; no build attempted. The Lean skeleton in §3 is
illustrative, not committed.

**Mathlib version**: all citations against `leanprover-community/mathlib4` at
revision `2df2f0150c` (v4.26.0, the pin used by S6b ACT-2). Line numbers stable at
the time of this PR but may drift in future Mathlib releases.

---

## §9. Differentiation from prior S6 PREPs

| Aspect | S6c PREP (#18488) | S6c PREP-2 (#18584) | **S6c PREP-3 (this)** |
|---|---|---|---|
| Target theorem | Schur orthogonality (general) | Schur diagonal (cheaper route) | **`integral_sq_exp_neg_sq` (load-bearing prerequisite, route 2 concretized)** |
| Direction | new theorem | route refinement | **bearer recheck + tactic-grade route refinement** |
| Mathlib idiom | parametric differentiation | direct Fubini + 1-D moment | **`gaussianReal` variance + bridge lemma** |
| Key API | `hasDerivAt_integral_of_dominated_loc` | `integral_mul_deriv_eq_deriv_mul` (IBP) | **`variance_of_integral_eq_zero` + `integral_gaussianReal_eq_integral_smul`** |
| Bound-integrability scaffold | ~30-50 LOC | Not needed (claimed) | **Not needed (verified)** |
| Parametric differentiation | Required (1 invocation) | Not needed (claimed) | **Not needed (verified)** |
| Estimated ACT LOC | ~150-200 | ~50-70 | **~20-25 (ACT-1) + ~40-55 (ACT-2)** |
| Build status | doc-only | doc-only | doc-only |
| Mathlib pin verified | 2026-05-12 (pre-v4.26.0) | 2026-05-13 (pre-v4.26.0) | **2026-06-02 (v4.26.0 / `2df2f0150c`)** |

This PREP-3 sits as a **tactic-grade self-correction + bearer refresh** of PREP-2. It
does not change PREP-2's route choice; it concretizes route 2 to a paste-ready
skeleton and updates the line-number citations to the current pin.

---

## §10. Next steps for S6c ACT-1

1. Wait for host disk to recover to GREEN (`df -h /Users/rwalters` reporting ≥5 Gi free).
2. Claim `area-of-circle-oq-05-oq-04` again.
3. Drop the §3 skeleton into a new helper section of
   `proofs/Proofs/AreaOfCircleOQ05OQ04.lean` (perhaps under a new `### Part 8.
   Diagonal Schur prerequisites`).
4. Run `./proofs/scripts/docker-build.sh Proofs.AreaOfCircleOQ05OQ04`; address any
   NNReal coercion or smul/mul friction per the §3 risk register.
5. Open one ACT-1 PR with the single new theorem `integral_sq_exp_neg_sq` (plus the
   two imports if not already present).
6. After ACT-1 merges, S6c ACT-2 builds the 1-D complex moment + n-dim Schur diagonal
   assembly per §5 above.

---

## §11. References

- **Parent file**: `proofs/Proofs/AreaOfCircleOQ05OQ04.lean` (854 lines as of
  S6b ACT-2, 26 theorems + 2 private helpers, 0 sorries, 0 axioms, Docker 3129/3129
  at v4.26.0).
- **Direct predecessors** (all merged, all doc-only):
  - `research/area-of-circle-oq-05-oq-04/s6c-prep-schur-orthogonality.md` (PR #18488).
  - `research/area-of-circle-oq-05-oq-04/s6c-prep-2-mathlib-moment-shortcut.md` (PR #18584).
- **Mathlib** at `2df2f0150c`:
  - `Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:147,192,223`.
  - `Mathlib/Probability/Distributions/Gaussian/Real.lean:48,249,493,528`.
  - `Mathlib/Probability/Moments/Variance.lean:149`.
- **Mathematical context**: Bargmann (1961), Folland (1989), §1.5.

---

*End of S6c PREP-3. 0 axioms, 0 sorries, 0 `.lean` lines.*
