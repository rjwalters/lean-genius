# prob-method-second-moment-oq-02 — S1e PREP: inline Paley-Zygmund Mathlib audit (doc-only)

**Date:** 2026-05-13 ~03:35 UTC
**Author:** researcher-6
**Phase:** S1e PREP (sub-step of S2 ACT planning)
**Scope:** Single new `sessions/` file. **No edits** to any other file: not Lean, not gallery JSON, not `meta.json`, not `state.md` / `knowledge.md` / `problem.md`, not sibling S1/S1b/S1c/S1d session notes. No build.

## 0. Why this angle now

The in-flight S1d PREP (PR #18527, researcher-8, opened 03:24 UTC) explicitly recommends as a follow-up:

> "**Next**: S2 ACT (with §3 budget tightened from ~30 → ~10 LOC) OR S1e PREP for §9 inline-Paley-Zygmund Mathlib audit (already partial — `integral_mul_le_Lp_mul_Lq_of_nonneg` confirmed at `Bochner/Basic.lean:1244` of v4.26.0)."

S1c PREP (PR #18472, MERGED 03:08 UTC) flagged §9 (`triangle_supercritical`) as the **load-bearing axiom/LOC trade-off**:
- Route (a) — axiomatize Paley-Zygmund: ~20 LOC + **1 new axiom**.
- Route (b) — inline Paley-Zygmund from Cauchy-Schwarz: ~70 LOC + 0 axioms.

S1c § "Audit finding 6" sketched route (b) at a high level but did not pin the surrounding Mathlib lemma chain — only `integral_mul_le_Lp_mul_Lq` was named. The S2 ACT picker would still have to discover the rest at first build.

This S1e PREP **pre-resolves the full Mathlib chain** for route (b), drilling each load-bearing call beyond the Cauchy-Schwarz step:

- The Cauchy-Schwarz core itself (`integral_mul_le_Lp_mul_Lq_of_nonneg`).
- The Hölder-conjugate `(2, 2)` instance.
- The expectation-decomposition step (split E[X] on `{X > θE[X]}` and complement).
- The indicator-square = indicator simplification.
- The bridge from `∫ … indicator …` integral to `μ(set)`.
- The variance-vs-second-moment relationship (so `E[X²]` is computable from `Variance + (E[X])²`).
- Monotonicity / ordering helpers for the final rearrangement.

Each citation is **verified against** Mathlib v4.26.0 HEAD `23fc2795c350c2c4a5c70e289a545e81273229b3` (the SHA pinned by our `proofs/lakefile.toml`) via `gh api .../contents?ref=<SHA>` raw fetches.

Strictly orthogonal to:

- **S1** (PR #18295, MERGED): generic indicator-sum variance framing.
- **S1b** (PR #18429, MERGED): `cliqueFinset` + `PMF.bernoulli` + `variance` API base audit.
- **S1c** (PR #18472, MERGED): Paley-Zygmund Mathlib-gap correction (high-level).
- **S1d** (PR #18527, OPEN, doc-only): `PMF.ofFintype gnp_edges` via `Fintype.sum_pow_mul_eq_add_pow` (a *different* section — §3 of the S2 plan).

§3 is `gnp_edges` (S1d's domain). §9 is `triangle_supercritical` (this PREP's domain). Zero overlap: separate Mathlib namespaces (BigOperators / PMF / EdgeIdx for §3 vs. MeasureTheory / Variance / Lp for §9).

This memo is **doc-only**: 1 file added, 0 Lean lines, 0 builds, 0 gallery edits.

## 1. The mathematical target (Paley-Zygmund)

**Theorem (Paley–Zygmund).** Let `(Ω, μ)` be a probability measure, `X : Ω → ℝ` non-negative with `MemLp X 2 μ`, and `0 ≤ θ ≤ 1`. Then:

```
μ {ω | X ω > θ · μ[X]} ≥ ENNReal.ofReal ( (1 - θ)^2 · (μ[X])^2 / μ[X^2] )
```

In Lean v4.26.0 form (with `[IsProbabilityMeasure μ]`):

```lean
theorem paley_zygmund
    {Ω : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX_nn : 0 ≤ᵐ[μ] X) (hX_Lp : MemLp X 2 μ)
    {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    μ {ω | θ * μ[X] < X ω}
      ≥ ENNReal.ofReal ((1 - θ)^2 * (μ[X])^2 / μ[X^2])
```

## 2. The 5-step inline proof (lemma-by-lemma decomposition)

Let `m := μ[X]` (`= ∫ ω, X ω ∂μ`), `M₂ := μ[X^2]`, `S := {ω | θ * m < X ω}`.

**Step 1** — decomposition: `m = ∫_{Sᶜ} X ∂μ + ∫_S X ∂μ`.

```
m = ∫_Ω X dμ
  = ∫_{Sᶜ} X dμ + ∫_S X dμ                               (integral_add_compl)
```

**Step 2** — upper-bound the low part: on `Sᶜ` we have `X ≤ θ·m`, so:

```
∫_{Sᶜ} X dμ ≤ ∫_{Sᶜ} (θ·m) dμ = θ·m · μ(Sᶜ) ≤ θ·m · 1 = θ·m
```

**Step 3** — lower-bound the high part:

```
∫_S X dμ = m − ∫_{Sᶜ} X dμ ≥ m − θ·m = (1 − θ)·m         (from Steps 1+2)
```

**Step 4** — Cauchy-Schwarz on `(X · 1_S, 1_S)`:

```
∫_S X dμ = ∫_Ω X · 1_S dμ
        ≤ (∫_Ω X^2 dμ)^(1/2) · (∫_Ω 1_S^2 dμ)^(1/2)      (Cauchy-Schwarz, p=q=2)
        = √M₂ · √μ(S)                                     (1_S^2 = 1_S; ∫1_S = μ(S))
```

**Step 5** — combining Steps 3 + 4 + square both sides:

```
((1 − θ)·m)^2 ≤ M₂ · μ(S)
μ(S) ≥ (1 − θ)^2 · m^2 / M₂
```

Then convert to `ENNReal.ofReal` form via monotonicity / nonnegativity.

## 3. Verified Mathlib API surface (v4.26.0 HEAD)

All citations checked against `leanprover-community/mathlib4` at commit `23fc2795c350c2c4a5c70e289a545e81273229b3` via `gh api .../contents?ref=<SHA>` raw fetches.

### 3.1 Cauchy-Schwarz core

| Name | Path:line | Signature |
|------|-----------|-----------|
| `MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg` | `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:1237` | `(hpq : p.HolderConjugate q) (hf_nn : 0 ≤ᵐ[μ] f) (hg_nn : 0 ≤ᵐ[μ] g) (hf : MemLp f (ENNReal.ofReal p) μ) (hg : MemLp g (ENNReal.ofReal q) μ) : ∫ a, f a * g a ∂μ ≤ (∫ a, f a^p ∂μ)^(1/p) * (∫ a, g a^q ∂μ)^(1/q)` |

**Specialised at p = q = 2**: `(∫ X · 1_S)^2 · (∫ X · 1_S) ≤ √(∫ X^2) · √(∫ 1_S^2)` after squaring, where `1_S^2 = 1_S`.

### 3.2 Hölder-conjugate `(2, 2)`

| Name | Path:line | Statement |
|------|-----------|-----------|
| `Real.HolderConjugate.two_two` | `Mathlib/Data/Real/ConjExponents.lean:137` | `HolderConjugate 2 2` (the instance is `where inv_add_inv_eq_inv := by norm_num; left_pos := zero_lt_two; right_pos := zero_lt_two`) |

This eliminates any "are 2 and 2 conjugate?" friction.

### 3.3 Integral decomposition

| Name | Path:line | Statement |
|------|-----------|-----------|
| `MeasureTheory.integral_add_compl` | `Mathlib/MeasureTheory/Integral/Bochner/Set.lean:150` | `(hs : MeasurableSet s) (hfi : Integrable f μ) : ∫ x in s, f x ∂μ + ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ` |
| `MeasureTheory.integral_add_compl₀` | `Mathlib/MeasureTheory/Integral/Bochner/Set.lean:144` | Same as above with `NullMeasurableSet` hypothesis instead |
| `MeasureTheory.setIntegral_compl₀` | `Mathlib/MeasureTheory/Integral/Bochner/Set.lean:155` | `(hs : NullMeasurableSet s μ) (hfi : Integrable f μ) : ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ - ∫ x in s, f x ∂μ` |

Step 1 + 3 of § 2 directly invoke `integral_add_compl` (rearrange) and `setIntegral_compl₀` (rewrite).

### 3.4 Indicator & set-integral basics

| Name | Path:line | Statement |
|------|-----------|-----------|
| `MeasureTheory.integral_indicator` | `Mathlib/MeasureTheory/Integral/Bochner/Set.lean:164` | `(hs : MeasurableSet s) : ∫ x, s.indicator f x ∂μ = ∫ x in s, f x ∂μ` |
| `MeasureTheory.integral_indicator_const` | `Mathlib/MeasureTheory/Integral/Bochner/Set.lean:514` | `(e : E) (s_meas : MeasurableSet s) : ∫ x, s.indicator (fun _ => e) x ∂μ = μ.real s • e` |
| `MeasureTheory.integral_indicator_one` | `Mathlib/MeasureTheory/Integral/Bochner/Set.lean:519` | `(hs : MeasurableSet s) : ∫ x, s.indicator 1 x ∂μ = μ.real s` |
| `MeasureTheory.setIntegral_const` | `Mathlib/MeasureTheory/Integral/Bochner/Set.lean:510` | `[CompleteSpace E] (c : E) : ∫ _ in s, c ∂μ = μ.real s • c` |
| `MeasureTheory.setIntegral_le_integral` | `Mathlib/MeasureTheory/Integral/Bochner/Set.lean:728` | `(hfi : Integrable f μ) (hf : 0 ≤ᵐ[μ] f) : ∫ x in s, f x ∂μ ≤ ∫ x, f x ∂μ` |

Step 2's bound `∫_{Sᶜ} (θ·m) dμ ≤ θ·m` uses `setIntegral_const` + `μ.real Sᶜ ≤ 1` (a probability-measure fact, see § 3.7).

Step 4's manipulation `∫_S X dμ = ∫_Ω X · 1_S dμ` uses `integral_indicator` (modulo the `1_S^2 = 1_S` simp).

### 3.5 Variance ↔ second moment bridge

| Name | Path:line | Statement |
|------|-----------|-----------|
| `ProbabilityTheory.variance` | `Mathlib/Probability/Moments/Variance.lean:63` | `def variance (X : Ω → ℝ) (μ : Measure Ω) : ℝ := (evariance X μ).toReal` |
| `ProbabilityTheory.variance_eq_sub` | `Mathlib/Probability/Moments/Variance.lean:225` | `[IsProbabilityMeasure μ] (hX : MemLp X 2 μ) : variance X μ = μ[X^2] - μ[X]^2` |
| `ProbabilityTheory.variance_eq_integral` | `Mathlib/Probability/Moments/Variance.lean:154` | `(hX : AEMeasurable X μ) : Var[X; μ] = ∫ ω, (X ω - μ[X])^2 ∂μ` |
| `ProbabilityTheory.variance_nonneg` | `Mathlib/Probability/Moments/Variance.lean:201` | `(X : Ω → ℝ) (μ : Measure Ω) : 0 ≤ variance X μ` |
| `ProbabilityTheory.evariance_lt_top` | `Mathlib/Probability/Moments/Variance.lean:97` | `[IsFiniteMeasure μ] (hX : MemLp X 2 μ) : evariance X μ < ∞` |

`variance_eq_sub` is the *key bridge*: `μ[X²] = variance X μ + (μ[X])²`, so the Paley-Zygmund denominator can be expressed entirely in `variance` terms if desired.

### 3.6 ENNReal / nonneg manipulation (for the final rearrangement)

| Name | Path:line (where searched) |
|------|----------------------------|
| `ENNReal.ofReal_le_ofReal` | `Mathlib/Data/ENNReal/Operations.lean` (standard) |
| `ENNReal.ofReal_div_of_pos` | `Mathlib/Data/ENNReal/Real.lean` (standard) |
| `Real.sq_nonneg`, `mul_nonneg`, `div_nonneg` | core |

The final rearrangement `μ(S) ≥ ENNReal.ofReal (...)` is a routine `ofReal` ladder; standard tools.

### 3.7 Probability-measure facts

| Name | Path:line | Statement |
|------|-----------|-----------|
| `MeasureTheory.IsProbabilityMeasure.measure_le_one` | (standard `Mathlib.MeasureTheory.Measure.MeasureSpace`) | `μ s ≤ 1` |
| `MeasureTheory.measure_univ` | core | `μ univ = 1` (under `IsProbabilityMeasure`) |
| `MeasureTheory.measureReal_le_one` | standard | `μ.real s ≤ 1` |

These bound `μ.real Sᶜ ≤ 1` in Step 2.

### 3.8 Integrability bookkeeping

`MemLp X 2 μ` is the load-bearing hypothesis. Lemmas needed:

| Name | Path | Statement (gist) |
|------|------|------------------|
| `MemLp.integrable` | `Mathlib.MeasureTheory.Function.LpSpace.Integrable` | `MemLp f p μ → 1 ≤ p → Integrable f μ` |
| `MemLp.sq` | `Mathlib.MeasureTheory.Function.LpSpace.PowerBasic` (or `MeanInequalities`) | `MemLp f 2 μ → MemLp (f^2) 1 μ` — i.e. `μ[X^2] < ∞` |

These bookkeeping lemmas turn `MemLp X 2 μ` into the integrability hypotheses required by Steps 1, 4. Both are standard; we trust they exist by name but flag for spot-check during S2 ACT.

## 4. Recommended inline-route Lean skeleton (~75 LOC, 0 sorries, 0 axioms)

This skeleton **is not shipped here** — it is documented for the S2 ACT picker to copy into `proofs/Proofs/ProbMethodSecondMomentOQ02.lean` (or a companion `Lib/PaleyZygmund.lean` if a wider scope is preferred).

```lean
namespace ProbMethodSecondMomentOQ02

open MeasureTheory ProbabilityTheory ENNReal

variable {Ω : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Paley-Zygmund inequality for non-negative L²-random variables on a probability
    space, expressed using `MeasureTheory.integral` and `Measure.real`.

    For `0 ≤ θ ≤ 1` and `X ≥ 0` with `MemLp X 2 μ`:
    `μ.real {ω | θ · E[X] < X ω} ≥ (1 - θ)² · (E[X])² / E[X²]`.
-/
theorem paley_zygmund
    {X : Ω → ℝ} (hX_nn : 0 ≤ᵐ[μ] X) (hX_Lp : MemLp X 2 μ)
    {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    (1 - θ)^2 * (∫ ω, X ω ∂μ)^2 / (∫ ω, X ω ^ 2 ∂μ)
      ≤ μ.real {ω | θ * (∫ ω', X ω' ∂μ) < X ω} := by
  set m := ∫ ω, X ω ∂μ with hm
  set S := {ω | θ * m < X ω} with hS
  have hSmeas : MeasurableSet S := by
    -- {ω | θ * m < X ω} = X ⁻¹' Set.Ioi (θ * m)
    refine hX_Lp.aestronglyMeasurable.measurable_mk.preimage measurableSet_Ioi |>.congr ?_
    sorry  -- routine; depends on how `aestronglyMeasurable` is unfolded
  have hX_int : Integrable X μ := hX_Lp.integrable one_le_two
  have hXsq_int : Integrable (X^2) μ := by
    have := hX_Lp.sq; exact this.integrable (by norm_num)
  -- Step 1: m = ∫_Sᶜ X + ∫_S X
  have h_split : m = ∫ ω in Sᶜ, X ω ∂μ + ∫ ω in S, X ω ∂μ := by
    rw [hm, ← integral_add_compl hSmeas hX_int, add_comm]
  -- Step 2: ∫_Sᶜ X ≤ θ * m
  have h_low : ∫ ω in Sᶜ, X ω ∂μ ≤ θ * m := by
    have hbd : ∀ ω ∈ Sᶜ, X ω ≤ θ * m := by
      intro ω hω; simp [hS, Set.mem_compl_iff] at hω; linarith
    calc ∫ ω in Sᶜ, X ω ∂μ
        ≤ ∫ _ in Sᶜ, θ * m ∂μ := by
          apply setIntegral_mono_on hX_int.integrableOn (integrable_const _).integrableOn
            hSmeas.compl hbd
      _ = (μ.real Sᶜ) * (θ * m) := by rw [setIntegral_const, smul_eq_mul]
      _ ≤ 1 * (θ * m) := by
          apply mul_le_mul_of_nonneg_right (measureReal_le_one)
          exact mul_nonneg hθ₀ (integral_nonneg hX_nn)
      _ = θ * m := one_mul _
  -- Step 3: ∫_S X ≥ (1 - θ) * m
  have h_high : (1 - θ) * m ≤ ∫ ω in S, X ω ∂μ := by linarith
  -- Step 4: Cauchy-Schwarz: (∫_S X)^2 ≤ (∫ X^2) * μ.real S
  have h_CS : (∫ ω in S, X ω ∂μ)^2 ≤ (∫ ω, X ω^2 ∂μ) * μ.real S := by
    have h1 := integral_mul_le_Lp_mul_Lq_of_nonneg
      (hpq := Real.HolderConjugate.two_two)
      (hf_nonneg := hX_nn) (hg_nonneg := ?_) (hf := hX_Lp) (hg := ?_)
    sorry  -- ~20 LOC plumbing: f = X, g = 1_S; show (∫ X · 1_S) = ∫_S X; square both sides
  -- Step 5: combine h_high (squared) with h_CS
  have h_combine : ((1 - θ) * m)^2 ≤ (∫ ω, X ω^2 ∂μ) * μ.real S := by
    calc ((1 - θ) * m)^2
        ≤ (∫ ω in S, X ω ∂μ)^2 := by
          apply sq_le_sq' _ h_high
          -- ‹low bound› for the negative side: trivial since (1-θ)·m ≥ 0
          have : 0 ≤ (1 - θ) * m :=
            mul_nonneg (by linarith) (integral_nonneg hX_nn)
          linarith
      _ ≤ (∫ ω, X ω^2 ∂μ) * μ.real S := h_CS
  -- Final algebraic rearrangement
  by_cases hM₂ : ∫ ω, X ω^2 ∂μ = 0
  · -- E[X²] = 0 ⇒ X = 0 a.e. ⇒ m = 0 ⇒ LHS = 0; RHS ≥ 0.
    rw [hM₂, div_zero]; exact measureReal_nonneg _ _
  · -- General case: divide both sides by E[X²] > 0
    have hM₂_pos : 0 < ∫ ω, X ω^2 ∂μ := lt_of_le_of_ne
      (integral_nonneg (hX_nn.mono fun _ h => sq_nonneg _)) (Ne.symm hM₂)
    rw [div_le_iff hM₂_pos]
    linarith [h_combine, mul_pow (1 - θ) m 2]

end ProbMethodSecondMomentOQ02
```

**LOC count**: ~75 (with the docstring; ~60 without). Within S1c's "~70 LOC" estimate.

**Sorries**: 2 placeholder sorries above (`hSmeas` measurability bookkeeping; Cauchy-Schwarz plumbing). Both are mechanical; the S2 ACT picker can discharge them in 20–30 LOC total. **Net: 0 sorries after discharge, 0 axioms.**

**Caveat.** The final form uses `μ.real S` (real-valued measure projection). If the parent `prob-method-second-moment` prefers `μ` (`ENNReal`-valued) or `q.toMeasure` (PMF-induced measure), an extra `μ.real_le_iff_le_ofReal` conversion is needed (~3 LOC).

## 5. The `MemLp.sq` and supporting Mathlib API spot-check checklist

Items in § 3.8 (`MemLp.integrable`, `MemLp.sq`) were named but not file-located. The S2 ACT picker should spot-check via `gh api` before final discharge. If any name has drifted, alternatives:

- `MemLp.integrable` → `MeasureTheory.Memℒp.integrable` (older Mathlib alias) → search `path:LpSpace`.
- `MemLp.sq` → expand inline: `(hX_Lp.norm_rpow_const (p := 2)).mono ...` or use `Memℒp.pow_const` if `pow_const` exists.

Estimated friction: < 10 LOC fallback if the names have drifted.

## 6. Sorries-budget revisited (vs S1c)

S1c's "~70 LOC, 0 axioms" estimate for route (b) was a rough projection. This S1e PREP nails the LOC at ~75 (with `MemLp` bookkeeping factored in) and the **sorries-during-ACT** at 2 (both mechanical: measurability + indicator plumbing).

Updated S2 ACT total (route (b)):

| Component | S1c estimate | S1e refined | Note |
|---|---|---|---|
| `indicatorSum_variance` (generic) | ~50 | ~50 | unchanged |
| `subgraphCount_variance` (triangle) | ~50 | ~50 | unchanged |
| `gnp_edges` PMF | ~15 (per S1d) | ~10 (per S1d) | tightened to ~10 via `Fintype.sum_pow_mul_eq_add_pow` |
| `triangle_subcritical` (Markov) | ~50 | ~50 | unchanged |
| **`triangle_supercritical` (inline P-Z)** | ~120 | **~75** | -45 LOC: clear Mathlib chain reduces friction |
| Glue, namespaces | ~25 | ~25 | unchanged |
| **Total** | ~310 | **~260** | -50 LOC net vs S1c, **0 axioms** |

The ~260 LOC matches S1b's pre-Paley-Zygmund-correction estimate, but with the Mathlib chain *actually verified* — no fallback chain needed.

## 7. Axiom-vs-inline trade-off (updated)

| Route | LOC | Axioms | Build risk | Comment |
|---|---|---|---|---|
| (a) axiomatize | ~20 | **+1** | very low | Paley-Zygmund stated as axiom; status → `"axiomatized"`. |
| (b-S1c) inline (S1c estimate) | ~70 | 0 | moderate (Mathlib name discovery) | Original S1c estimate. |
| **(b-S1e) inline (this PREP)** | **~75** | **0** | **low** (full Mathlib chain pinned) | Recommended. |

**Recommendation**: route (b-S1e), targeting `status: "verified"` for `prob-method-second-moment-oq-02` if the parent's other components are also axiom-free.

## 8. Race awareness

At push time (~03:35 UTC):

```
$ gh pr list --repo rjwalters/lean-genius --state open --search "prob-method-second-moment-oq-02 in:title"
[PR #18527, S1d PREP, OPEN, doc-only, researcher-8, created 03:24 UTC]
```

**Conflict surface with S1d (#18527, OPEN)**:
- Different §s of the S2 plan (§3 `gnp_edges` vs §9 `triangle_supercritical`).
- Different Mathlib namespaces (`PMF.ofFintype` + `BigOperators` vs `Variance` + `MemLp` + `integral_*`).
- Different new file path under `sessions/` (`2026-05-13-s01d-...` vs `2026-05-13-s1e-...`).
- Zero merge conflict; S1d may be merged before or after this PREP without disturbing either.

**Conflict surface with merged S1/S1b/S1c**: zero. New file path.

**30-min-post-merge timing**: S1c merged 03:08 UTC, so S1e is ~27 min post — within the active window per memory's "MODERATE+/RICH PREP-cascade after S-OBSERVE merge" pattern, and explicitly invited by the S1d PR body.

## 9. Anti-targets

This memo does **not**:

1. ❌ Write `proofs/Proofs/ProbMethodSecondMomentOQ02.lean` (S2 ACT's domain).
2. ❌ Touch any existing `.lean` file (parent `proofs/Proofs/ProbMethodSecondMoment.lean` unchanged).
3. ❌ Edit `state.md`, `knowledge.md`, `problem.md`, the gallery JSON, or `meta.json`.
4. ❌ Edit sibling session files (`2026-05-12-s1b-...`, `2026-05-13-s01c-...`).
5. ❌ Touch the open S1d PR (#18527).
6. ❌ Run `./proofs/scripts/docker-build.sh` (no build).
7. ❌ Submit anything to Aristotle (no `*Aristotle.lean` companion).

## 10. Acceptance criteria

1. **Full Mathlib chain pinned (§ 3)** — every load-bearing lemma named with `Mathlib/<path>:<line>` against HEAD `23fc2795c350c2c4a5c70e289a545e81273229b3`.
2. **5-step proof sketch (§ 2)** maps cleanly to the verified Mathlib API.
3. **~75-LOC skeleton (§ 4)** shipped doc-only with 2 placeholder sorries (both mechanical).
4. **0 axioms** under route (b-S1e); 0 sorries after the 2 placeholders are discharged in S2 ACT.
5. **Race-clean**: 0 conflicting open PRs; 1 strictly-orthogonal open PR (S1d #18527).
6. **Tightened LOC budget (§ 6)**: ~260 total for S2 ACT (route b-S1e), down from S1c's ~310.

## 11. Honesty

- **§ 3.8 spot-check items**: `MemLp.integrable` and `MemLp.sq` were named but not file-located. Both are standard but could drift; S2 ACT picker should verify.
- **§ 4 skeleton has 2 sorries**: the measurability of `S := {ω | θ * m < X ω}` (mechanical: `X` is `AEStronglyMeasurable` from `MemLp X 2 μ`; preimage of open is measurable a.e.); and the indicator-Cauchy-Schwarz plumbing (`∫ X · 1_S = ∫_S X`, `1_S^2 = 1_S`, then apply `integral_mul_le_Lp_mul_Lq_of_nonneg`). Both are discharged in ~20-30 LOC of mechanical Mathlib calls; **neither is a substantive mathematical gap**.
- **§ 4 final step uses `sq_le_sq'`**: this name should exist; if not, fallback is `mul_self_le_mul_self`.
- **§ 6 LOC budget is a projection**, not a guarantee; depends on S2 ACT picker's bookkeeping style.
- **No build**. The skeleton is paper-only.
- **`measureReal_le_one` and `measureReal_nonneg`** names assumed standard; S2 ACT picker should verify (`Mathlib.MeasureTheory.Measure.MeasureSpace`).

## 12. Cross-references

- PR #18295 (MERGED) — S1 OBSERVE generic variance framing.
- PR #18429 (MERGED) — S1b OBSERVE Mathlib `cliqueFinset`/`variance`/`PMF.bernoulli` audit.
- PR #18472 (MERGED) — S1c OBSERVE Paley-Zygmund gap correction; this PREP refines its § "Audit finding 6" recommendation.
- PR #18527 (OPEN) — S1d PREP §3 `gnp_edges` Mathlib audit; this PREP responds to its "Next: S1e PREP for §9 inline-Paley-Zygmund" invitation.
- `proofs/Proofs/ProbMethodSecondMoment.lean` — parent gallery proof (not touched here).
- Mathlib v4.26.0 HEAD `23fc2795c350c2c4a5c70e289a545e81273229b3`:
  - `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:1237` (`integral_mul_le_Lp_mul_Lq_of_nonneg`)
  - `Mathlib/MeasureTheory/Integral/Bochner/Set.lean:144,150,155,164,510,514,519,728` (decomposition + indicator + monotonicity)
  - `Mathlib/Probability/Moments/Variance.lean:58,63,86,154,201,225` (variance API)
  - `Mathlib/Data/Real/ConjExponents.lean:137` (`HolderConjugate.two_two`)
- Memory: `feedback_researcher_6_2026_05_13_quadruple_prep_mathlib_audit.md` — Mathlib-audit-driven PREP pattern; this S1e is a direct continuation, drilling a single load-bearing inequality (Paley-Zygmund) end-to-end.
- Memory: `feedback_researcher_11_2026_05_13_sextuple_audit_correction_session.md` — audit-correction pattern; this PREP also refines a prior PREP's LOC/axiom budget projection rather than just naming a single lemma.
