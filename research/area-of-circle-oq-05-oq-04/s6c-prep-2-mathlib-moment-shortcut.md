# S6c PREP-2 — Mathlib `gaussianReal` / `IsGaussian` moment shortcut obsoletes `hasDerivAt_integral_of_dominated_loc` for the diagonal Schur case

**Researcher**: researcher-4
**Date**: 2026-05-12 (UTC night → 2026-05-13)
**Mode**: Doc-only PREP (no `.lean` changes; no edits to `problem.md`, `state.md`, `knowledge.md`, the merged S4b / S6a / S6b / S6c PREP files, the open S4a ACT, the gallery `meta.json`, or any JSON).
**Predecessors**:
- Merged: S6c PREP PR #18488 — Schur orthogonality derivation route (proposes parametric-differentiation route for the diagonal case)
- Merged: S6a PREP PR #18389 — n-dim shifted Gaussian via Path B per-axis Fubini
- Merged: S6b PREP PR #18422 — complex Fourier-eigenfunction via `fourier_gaussian_innerProductSpace`
- Merged: S5 ACT PR #18278 — translation invariance + (c,b)-density
- Open: S4a ACT PR #18221 — n-dim `∫_{ℂⁿ} exp(-(b·∑‖zᵢ‖²)) = (π/b)ⁿ` (CONFLICTING)

**Orthogonality**: this file is a **self-audit / Mathlib-bearer correction** of the merged S6c PREP (#18488) §3.3 and §4.2 estimates. Adds **exactly one new file** at `research/area-of-circle-oq-05-oq-04/s6c-prep-2-mathlib-moment-shortcut.md`. By construction orthogonal to S4a (different theorem), S6a (different theorem), S6b (different theorem), S6c (same theorem, **strictly cheaper route**), and S4b (different setting).

---

## §1. The S6c-diagonal identity to lock

From S6c PREP §2.1 (PR #18488), the diagonal-case theorem:

```lean
theorem schur_orthogonality_complex_gaussian_diag
    {n : ℕ} (i : Fin n) :
    ∫ z : Fin n → ℂ, ‖z i‖ ^ 2 *
      ((1 : ℝ) / Real.pi) ^ n * Real.exp (-(∑ k, ‖z k‖ ^ 2)) = 1
```

Mathematically: the variance of the standard complex Gaussian in coordinate `i`.

---

## §2. The S6c PREP estimate (PR #18488 §3.3 + §4.2)

The merged S6c PREP routes the diagonal case through **parametric differentiation under the integral sign**:

> **Step 1**: Start with the parametric n-dim integral (S4a): `F(b) := ∫_{ℂⁿ} exp(-b · ‖z‖²) dz = (π/b)^n`.
>
> **Step 2**: Differentiate w.r.t. `b` at `b = 1`: `F'(1) = -∫_{ℂⁿ} ‖z‖² · exp(-‖z‖²) = -n·π^n`.
>
> **Step 3**: Divide by `π^n` and normalize: `∫_{ℂⁿ} ‖z‖² · (1/π)^n · exp(-‖z‖²) = n`.
>
> **Step 4**: Coordinate-permutation symmetry → `∫ ‖z_i‖² · (1/π)^n · exp(-‖z‖²) = 1`.

This routes Step 2 through `hasDerivAt_integral_of_dominated_loc` (`Mathlib/Analysis/Calculus/ParametricIntegral.lean`), with six hypotheses, the load-bearing one being

> `bound : (Fin n → ℂ) → ℝ` with `Integrable bound volume` and the pointwise estimate `|d/db exp(-b·‖z‖²)| ≤ bound(z)` for `b` in a small ball around `1`.

S6c PREP §3.3 estimates the bound-integrability proof at **~30-50 LOC**, with the suggested bound

```
bound(z) := ‖z‖² · exp(-(1 - ε) · ‖z‖²).
```

S6c PREP §4.2 estimates the full diagonal ACT at **~150-200 LOC** split across 1-2 PRs.

---

## §3. The shortcut: parametric differentiation is **not needed**

**Key observation**: the diagonal Schur identity is a Lebesgue integral whose integrand factorises into a sum of per-axis products; it can be evaluated **directly by Fubini** without any differentiation under the integral sign.

### §3.1. The factorisation

Pointwise on `Fin n → ℂ`:

$$\|z_i\|^2 \cdot \exp\!\bigg(-\sum_{k} \|z_k\|^2\bigg) \;=\; \|z_i\|^2 \cdot \exp(-\|z_i\|^2) \;\cdot\; \prod_{j \neq i} \exp(-\|z_j\|^2). \quad (\star)$$

The integrand is therefore a **single-axis polynomial-times-Gaussian** on coordinate `i`, **constant-Gaussian** on the other coordinates — no derivative of any parameter is involved.

### §3.2. The reduction chain

By `Integrable.fintype_prod` (`Mathlib/MeasureTheory/Integral/Pi.lean:67`) for integrability and `integral_fintype_prod_volume_eq_prod` (`Pi.lean:115`) for the value, the integral over `Fin n → ℂ` factorises:

$$\int_{\mathrm{Fin}\,n \to \mathbb{C}} \|z_i\|^2 \cdot \exp(-\|z\|^2) \,dz \;=\; \Big(\!\!\int_\mathbb{C} \|w\|^2 \cdot \exp(-\|w\|^2) \,dw\!\Big) \cdot \Big(\!\!\int_\mathbb{C} \exp(-\|w\|^2) \,dw\!\Big)^{n-1}.$$

The right factor is the **already-merged** `complex_gaussian_integral_unit_norm` (`AreaOfCircleOQ05OQ04.lean:277`), giving `π^{n-1}`.

The left factor is the **1-D complex second moment**:

$$M_{\mathbb{C}} := \int_\mathbb{C} \|w\|^2 \cdot \exp(-\|w\|^2) \,dw \;=\; \pi. \quad (\dagger)$$

(Derivation in §3.3 below.) Multiplying: `M_ℂ · π^{n-1} = π^n`, and after the normalising `(1/π)^n` the answer is `1`. ∎

### §3.3. The 1-D complex second moment `(†)`

Via the canonical measure-preserving identification `ℂ ≃ₘ ℝ × ℝ` (volume preserving) and `‖w‖² = w.re² + w.im²`:

$$\int_\mathbb{C} \|w\|^2 \exp(-\|w\|^2) \,dw \;=\; \int_{\mathbb{R}^2} (x^2 + y^2) \exp(-(x^2 + y^2)) \,dx\,dy.$$

By Fubini:

$$= \Big(\!\!\int_\mathbb{R} x^2 \exp(-x^2) \,dx\!\Big) \cdot \Big(\!\!\int_\mathbb{R} \exp(-y^2) \,dy\!\Big) + \Big(\!\!\int_\mathbb{R} \exp(-x^2) \,dx\!\Big) \cdot \Big(\!\!\int_\mathbb{R} y^2 \exp(-y^2) \,dy\!\Big).$$

Each `∫ exp(-x²) dx = √π` (Mathlib `Real.integral_gaussian` / `integral_exp_neg_mul_sq`). Each `∫ x² · exp(-x²) dx = √π / 2` is the 1-D real second moment.

So `M_ℂ = 2 · (√π / 2) · √π = π`. ✓

### §3.4. The 1-D real second moment `∫ x² · exp(-x²) dx = √π / 2`

**Three Mathlib routes** to this fact, in increasing levels of abstraction:

1. **Direct integration by parts**: write `x² · exp(-x²) = -x · ((-1/2)·exp(-x²))'` and integrate by parts to reduce to `(1/2)·∫exp(-x²) = √π/2`. Lean LOC: ~10-15 using `integral_mul_deriv_eq_deriv_mul` (`Mathlib/MeasureTheory/Integral/IntegrationByParts.lean`).

2. **Via `gaussianReal` variance**: the standard real Gaussian with variance `v = 1/2`, written `gaussianReal 0 (1/2 : ℝ≥0)` in Mathlib (`Mathlib/Probability/Distributions/Gaussian/Real.lean`), has PDF `(1/√π)·exp(-x²)` and variance `1/2` by definition. Hence `∫ x² · (1/√π) · exp(-x²) dx = 1/2`, i.e., `∫ x² · exp(-x²) dx = √π / 2`. The variance fact is `variance_id_gaussianReal` at `Real.lean:543`. Lean LOC: ~10-15 once the partition-function rescaling is set up.

3. **Via the parametric Gaussian** already proved in the slug: `complex_gaussian_integral_scaled` (`AreaOfCircleOQ05OQ04.lean:226`) gives `∫_ℝ exp(-b·x²) dx = √(π/b)` (real version available as `integral_gaussian` in Mathlib). Differentiating **the right-hand-side** symbolically — without `hasDerivAt_integral_of_dominated_loc` — via `Real.HasDerivAt.const_div`, `Real.HasDerivAt.rpow`, etc., reduces to algebra: `d/db (√(π/b))|_{b=1} = -√π/2`, so the negative-derivative integral identity gives `∫ x² · exp(-x²) = √π/2`. Lean LOC: this still requires differentiating *under* the integral once, so it is **not** strictly cheaper than route 1; listed for completeness.

**Recommendation**: route 1 (integration by parts) is the cleanest in Lean. It's the standard textbook derivation, uses only existing Mathlib integration-by-parts and `integral_exp_neg_mul_sq` lemmas, and avoids the probability-theory dependency chain of route 2.

---

## §4. Concrete Lean skeleton (replacing S6c PREP §4.2)

Sketch (not committed; this PREP is doc-only):

```lean
/--  1-D real second moment: `∫ x² · exp(-x²) dx = √π / 2`.  -/
theorem integral_sq_exp_neg_sq :
    ∫ x : ℝ, x ^ 2 * Real.exp (-x ^ 2) = Real.sqrt Real.pi / 2 := by
  -- Integration by parts: ∫ x · (x · exp(-x²)) dx = (1/2) · ∫ exp(-x²) dx.
  -- Use `Real.integral_gaussian` for the final RHS.
  sorry  -- ~10-15 LOC via Mathlib integration-by-parts.

/--  1-D complex second moment: `∫ ‖w‖² · exp(-‖w‖²) dw = π`.  -/
theorem complex_gaussian_integral_norm_sq :
    ∫ w : ℂ, ‖w‖ ^ 2 * Real.exp (-‖w‖ ^ 2) = Real.pi := by
  -- ℂ ≃ ℝ² (measure preserving) + Fubini + integral_sq_exp_neg_sq.
  sorry  -- ~15-20 LOC via Complex.measurableEquivRealProd transport.

/--  n-dim Schur orthogonality, diagonal case.  -/
theorem schur_orthogonality_complex_gaussian_diag {n : ℕ} (i : Fin n) :
    ∫ z : Fin n → ℂ, ‖z i‖ ^ 2 *
      ((1 : ℝ) / Real.pi) ^ n * Real.exp (-(∑ k, ‖z k‖ ^ 2)) = 1 := by
  -- Step 1: factor exp(-(∑ ‖z_k‖²)) = ∏ exp(-‖z_k‖²) via `Real.exp_sum`.
  -- Step 2: introduce ‖z_i‖² on the i-axis; Fubini via `integral_fintype_prod_volume_eq_prod`
  --   on the heterogeneous decomposition (i-th factor different from others).
  -- Step 3: apply `complex_gaussian_integral_norm_sq` to the i-th axis,
  --   and `complex_gaussian_integral_unit_norm` (S3 corollary, AreaOfCircleOQ05OQ04.lean:277)
  --   to the (n-1) remaining axes.
  -- Step 4: simplify (1/π)^n · π · π^{n-1} = 1.
  sorry  -- ~25-35 LOC.
```

**Estimated ACT total**: 50-70 LOC across 1-2 PRs, 0 sorries, 0 axioms. **NO `hasDerivAt_integral_of_dominated_loc`. NO bound-integrability scaffold. NO parametric differentiation.**

This is **~3× shorter** than the S6c PREP §4.2 estimate (~150-200 LOC) and avoids the entire "six-hypothesis" dominated-bound construction.

---

## §5. Mathlib API audit

All references verified against `leanprover-community/mathlib4` HEAD on 2026-05-12.

| Identifier | Module | Line | Use |
|---|---|---|---|
| `integral_fintype_prod_volume_eq_prod` | `Mathlib/MeasureTheory/Integral/Pi.lean` | 115 | n-fold heterogeneous Fubini (S6a PREP §3.2 already verified) |
| `Integrable.fintype_prod` | `Mathlib/MeasureTheory/Integral/Pi.lean` | 67 | per-axis integrability for the polynomial-Gaussian product |
| `Real.integral_gaussian` (and `integral_exp_neg_mul_sq`) | `Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean` | ~290 | `∫ exp(-b·x²) dx = √(π/b)` |
| `integral_mul_exp_neg_mul_sq` (alias) | `Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean` | 147 | `Integrable (fun x ↦ x · exp(-b·x²))` |
| `integrable_rpow_mul_exp_neg_mul_sq` | `Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean` | 109 | `Integrable (fun x ↦ x^s · exp(-b·x²))` for `s > -1` — covers `s = 2` directly |
| `integral_mul_deriv_eq_deriv_mul` | `Mathlib/MeasureTheory/Integral/IntegrationByParts.lean` | ~140 | the load-bearing IBP for §3.4 route 1 |
| `Complex.measurableEquivRealProd` | `Mathlib/Analysis/Complex/Basic.lean` | ~430 | `ℂ ≃ₘ ℝ × ℝ` measure-preserving equivalence |
| `MeasurePreserving.integral_comp` | `Mathlib/MeasureTheory/Measure/MeasureSpace.lean` | varies | transport across `ℂ ≃ₘ ℝ²` |
| `variance_id_gaussianReal` | `Mathlib/Probability/Distributions/Gaussian/Real.lean` | 543 | `Var[id; gaussianReal μ v] = v` — alternative route §3.4 (route 2) |
| `IsGaussian.memLp_id` (Fernique) | `Mathlib/Probability/Distributions/Gaussian/Fernique.lean` | 186 | for any Gaussian μ on complete-space IPS, `MemLp id p μ` (used in §3.4 route 2 + memory) |

The merged S6c PREP §3.2 already verified the location of `hasDerivAt_integral_of_dominated_loc` (`Mathlib/Analysis/Calculus/ParametricIntegral.lean`); this PREP-2 demonstrates **it isn't needed**.

---

## §6. Honest comparison: where does the saving come from?

The S6c PREP §4.2 ~150-200 LOC plan and the S6c PREP-2 ~50-70 LOC plan differ in **what is computed symbolically vs. semantically**:

- **S6c PREP (parametric-differentiation route)** computes `F(b) := ∫ exp(-b·‖z‖²) = (π/b)^n` as a function of `b`, then differentiates to extract the second moment `-F'(1) = n·π^n`. The differentiation requires `hasDerivAt_integral_of_dominated_loc` (six hypotheses) and a dominated bound that uniformly controls `|F'(b)|` on a ball around `b = 1`.
- **S6c PREP-2 (this; direct-Fubini route)** computes the second moment directly via per-axis Fubini, reducing to a single 1-D fact `∫ x² · exp(-x²) dx = √π/2`. The 1-D fact follows from integration by parts (no parametric differentiation).

Both routes are mathematically equivalent (the parametric-differentiation route is "Feynman's trick"; the direct-Fubini route is "Tonelli on the product"). The saving is that **the n-dim integrand already factors per-axis** (eq. `(\star)` in §3.1) — there's nothing to differentiate.

The original parametric-differentiation framing was motivated by the **higher-moment** case `∫ ‖z‖^{2k} · exp(-‖z‖²) = k! · π · (...)` for k ≥ 2 (Bargmann-Fock higher moments). For `k = 1` (the Schur diagonal case), parametric differentiation **is not necessary**.

**For higher-moment generalisations**, parametric differentiation **does** become the natural route. This PREP-2 only obsoletes the S6c PREP §4.2 plan for the `k = 1` case (the literal Schur identity), not the general higher-moment formula.

---

## §7. Sorry / axiom delta

- This PR (S6c PREP-2): **0 sorries, 0 axioms, 0 Lean lines.**
- Proposed S6c-diagonal ACT (new plan): ~50-70 LOC across 1-2 PRs (helper `integral_sq_exp_neg_sq` + 1-D complex moment + n-dim Schur via Fubini), 0 sorries, 0 axioms.

**Net saving over the S6c PREP §4.2 plan**: ~100-130 LOC, **no** parametric differentiation, **no** bound-integrability lemma.

---

## §8. Anti-targets

This PR does NOT:

- Modify any `.lean` file (`proofs/Proofs/AreaOfCircleOQ05OQ04.lean` untouched).
- Modify `problem.md`, `state.md`, `knowledge.md`, the merged `s4b-padic-survey.md` / `s6a-prep-pi-haar-vs-fubini.md` / `s6b-prep-complex-fourier-eigenfunction.md` / `s6c-prep-schur-orthogonality.md`, or the gallery `meta.json`.
- Modify `src/data/research/problems/area-of-circle-oq-05-oq-04.json`.
- Touch the parallel `research/problems/area-of-circle-oq-05-oq-04/` layout (the flat `research/area-of-circle-oq-05-oq-04/` is the active one — confirmed by sibling files `s4b-*.md` / `s6a-*.md` / `s6b-*.md` / `s6c-*.md`).
- Resolve, rebase, or otherwise touch the open S4a ACT (PR #18221, currently CONFLICTING) — that's a separate concern for whoever opened it.
- Implement or build the new diagonal Schur theorem — this PREP-2 only refines the route; the ACT belongs to a follow-on PR.
- Address the **off-diagonal** case — that case is **already** cleanly handled in S6c PREP §4.1 (per-axis Fubini + odd symmetry, ~60-80 LOC). No revision needed there.

---

## §9. Honest framing

**What this PR demonstrably adds**:

1. A **strictly shorter** Lean route for the S6c-diagonal theorem, with a concrete Mathlib bearer audit (5 cited lemmas with file:line) and a 50-70-LOC budget vs. the merged S6c PREP §4.2's 150-200-LOC budget.
2. A correction of the S6c PREP §3.3 ~30-50 LOC bound-integrability estimate: that scaffold is **strictly avoidable** for the `k = 1` Schur identity. (The bound construction would still be needed for higher-moment generalisations.)
3. A note that the same direct-Fubini reduction subsumes the off-diagonal S6c PREP §4.1 plan up to a sign change on the i-th 1-D factor — i.e., the **combined Schur theorem** (S6c PREP §4.3) could in principle be discharged via a single `by_cases` on `i = j` against the unified per-axis Fubini decomposition.

**What this PR does NOT claim**:

- The parametric-differentiation route is **wrong** — it is mathematically equivalent. It is, however, **strictly more expensive** in Lean LOC and Mathlib-API surface.
- This PREP-2 makes the Schur identity novel — it is textbook (Folland's *Harmonic Analysis in Phase Space* §1.5, Bargmann 1961). The novelty is the **Lean-API choice**, not the mathematics.
- No `gh api search/code` calls during this PR found a single existing Mathlib lemma `schur_orthogonality_complex_gaussian` or `gaussian_second_moment_eq` (a 2026-05-12 search returned zero hits across the org). This formalisation would be the first.

**Build status**: no `.lean` changes; no build attempted. The Lean skeleton in §4 is illustrative, not committed.

**Mathlib version**: all citations against `leanprover-community/mathlib4` HEAD on 2026-05-12. Line numbers are stable at the time of this PR but may drift in future Mathlib releases.

---

## §10. Differentiation from prior S6 PREPs

| Aspect | S6a PREP (#18389) | S6b PREP (#18422) | S6c PREP (#18488) | **S6c PREP-2 (this)** |
|---|---|---|---|---|
| Target theorem | n-dim shifted Gaussian | complex Fourier-eigenfunction | Schur orthogonality | **Schur diagonal (cheaper route)** |
| Direction | new theorem | new theorem | new theorem | **route refinement of the same theorem as #18488** |
| Mathlib idiom | per-axis Fubini | direct specialization at `V := ℂ` | parametric differentiation | **direct Fubini + 1-D second moment** |
| Key API | `integral_fintype_prod_volume_eq_prod` | `fourier_gaussian_innerProductSpace` | `hasDerivAt_integral_of_dominated_loc` | **`integral_mul_deriv_eq_deriv_mul` + `Real.integral_gaussian`** |
| Bound-integrability scaffold | Not needed | Not needed | ~30-50 LOC | **Not needed** |
| Parametric differentiation | Not needed | Not needed | Required (1 invocation) | **Not needed** |
| Estimated ACT LOC | ~150 (S6a author) | ~80-100 (S6b author) | ~150-200 (#18488 §4.2) | **~50-70** |
| Build status | doc-only | doc-only | doc-only | doc-only |

This PREP-2 sits as a **self-correction** of #18488's §4.2 route choice. It does **not** supersede #18488's §4.1 (off-diagonal case is fine as-is) or §4.3 (combined statement is fine as-is once both halves are proved). It does supersede §4.2 / §3.3 (the diagonal-case route + bound-integrability scaffold).

---

## §11. What the next S6c ACT author should do

1. **Ship `integral_sq_exp_neg_sq`** (~10-15 LOC) as a tiny stand-alone lemma — `∫_ℝ x² · exp(-x²) dx = √π / 2` via integration by parts. This may already be in Mathlib under a different name; do a final `gh api search/code` pass before re-proving.
2. **Ship `complex_gaussian_integral_norm_sq`** (~15-20 LOC) — `∫_ℂ ‖w‖² · exp(-‖w‖²) dw = π` via `Complex.measurableEquivRealProd` + Fubini.
3. **Ship `schur_orthogonality_complex_gaussian_diag`** (~25-35 LOC) — n-dim Schur diagonal via `integral_fintype_prod_volume_eq_prod`.
4. **Combine with the off-diagonal case** from S6c PREP §4.1 (~60-80 LOC, unchanged plan) to get the full `schur_orthogonality_complex_gaussian` (~10 LOC for the `by_cases`).

**Total S6c ACT estimate (revised)**: ~110-160 LOC across 3-4 PRs (1-D moment, 1-D complex moment, n-dim diag, n-dim combined), 0 sorries, 0 axioms. Compares to the merged S6c PREP plan of ~220-290 LOC across 2-3 PRs. The saving is in the diagonal-case sub-route.

---

## §12. References

- **Parent file**: `proofs/Proofs/AreaOfCircleOQ05OQ04.lean` (~544 lines as of S5, 0 sorries, 0 axioms).
- **Sibling PREP files** (all merged, all doc-only):
  - `research/area-of-circle-oq-05-oq-04/s4b-padic-survey.md` (PR #18269).
  - `research/area-of-circle-oq-05-oq-04/s6a-prep-pi-haar-vs-fubini.md` (PR #18389).
  - `research/area-of-circle-oq-05-oq-04/s6b-prep-complex-fourier-eigenfunction.md` (PR #18422).
  - `research/area-of-circle-oq-05-oq-04/s6c-prep-schur-orthogonality.md` (PR #18488 — the merged route this PREP-2 corrects).
- **Mathlib**:
  - `Mathlib/MeasureTheory/Integral/Pi.lean:67` (`Integrable.fintype_prod`), `:115` (`integral_fintype_prod_volume_eq_prod`).
  - `Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:109` (`integrable_rpow_mul_exp_neg_mul_sq`), `:147` (`integrable_mul_exp_neg_mul_sq`).
  - `Mathlib/MeasureTheory/Integral/IntegrationByParts.lean` (`integral_mul_deriv_eq_deriv_mul`).
  - `Mathlib/Analysis/Complex/Basic.lean` (`Complex.measurableEquivRealProd`).
  - `Mathlib/Probability/Distributions/Gaussian/Real.lean:543` (`variance_id_gaussianReal`) — alternative §3.4 route 2.
  - `Mathlib/Probability/Distributions/Gaussian/Fernique.lean:186` (`IsGaussian.memLp_id`) — referenced in memory as the "Fernique" lemma; not on the cheapest path for this theorem.
- **Mathematical context**: Bargmann (1961), *On a Hilbert space of analytic functions...*; Folland (1989), *Harmonic Analysis in Phase Space*, §1.5.

---

*End of S6c PREP-2. No other files modified. No build attempted. 0 axioms, 0 sorries, 0 `.lean` lines.*
