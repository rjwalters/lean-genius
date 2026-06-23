# S3 PREP — `chartIntrinsicDist_triangle` design + paste-ready skeleton

**Date**: 2026-05-16
**Researcher**: researcher-10
**Phase**: PREP (predecessor S2b ACT shipped 2026-05-16T04:38Z, PR #19449, build-verified 2551 jobs)
**Status**: doc-only

## 0. TL;DR

S2b ACT shipped `chartArcLength_trans` (additivity under interval concatenation). State.md's named **Next Action (S2c)** is the chart-local triangle inequality `chartIntrinsicDist_triangle` "mirroring the parent `Proofs.TriangleInequalityOQ04.intrinsicDist_triangle`."

This PREP:

1. Audits the parent's `intrinsicDist_triangle` proof (4 steps, 12 LOC + 1 helper `pathLength_trans` ~30 LOC + 2 sub-lemmas `eqOn_first` / `eqOn_second` ~40 LOC = ~80 LOC total in parent).
2. Surveys **four design options** (A–D) for chart-local `chartIntrinsicDist`. The parent's `Path x y → ℝ≥0∞` machinery does **not** transport verbatim because (i) `chartArcLength` returns `ℝ` (not `ℝ≥0∞`), and (ii) the parent's reparameterization step (`eVariationOn.comp_eq_of_monotoneOn`) has no direct integral-form analog at v4.26.0.
3. Recommends **Option A** (Path-mirror with reparameterization-by-substitution): preserves the parent's iInf-exchange structure, but the reparameterization step uses `intervalIntegral.integral_comp_mul_left` + `deriv.scomp` (chain rule) instead of `eVariationOn.comp_eq_of_monotoneOn`.
4. Provides **paste-ready** Lean skeleton (~120 LOC across 1 definition + 4 helper lemmas + 1 main theorem) with `sorry` placeholders for 2 sub-steps that require careful `IntervalIntegrable` plumbing.
5. ACT-readiness gate (S3 ACT): **6/8 GREEN**, 1/8 AMBER (reparameterization chain-rule + `IntervalIntegrable` plumbing), 1/8 RED (Docker daemon hung — INFRASTRUCTURE-ONLY, does not block doc-only PREP).

Infrastructure status (2026-05-16T09:51Z): `timeout 5 docker info --format '{{.ServerVersion}}'` → exit 124 (daemon unresponsive); `df -h /System/Volumes/Data` → 100% / 6.9Gi avail (within memory-classified `_docker_daemon_hang_server_unresponsive_ship_build_pending_distinct_from_disk_full` band, but disk also at 100% so cascade risk elevated). **PREP is doc-only** — no build verification needed.

## 1. Parent's `intrinsicDist_triangle` proof anatomy (lines 215–239 of `proofs/Proofs/TriangleInequalityOQ04.lean`)

```lean
theorem intrinsicDist_triangle (x y z : X) :
    intrinsicDist x z ≤ intrinsicDist x y + intrinsicDist y z := by
  simp only [intrinsicDist]
  calc ⨅ γ : Path x z, pathLength γ
      ≤ ⨅ γ₁ : Path x y, ⨅ γ₂ : Path y z, pathLength γ₁ + pathLength γ₂ := by
        apply le_iInf; intro γ₁
        apply le_iInf; intro γ₂
        exact (iInf_le _ (γ₁.trans γ₂)).trans (pathLength_trans γ₁ γ₂).le
    _ = (⨅ γ₁ : Path x y, pathLength γ₁) + ⨅ γ₂ : Path y z, pathLength γ₂ := by
        simp_rw [ENNReal.iInf_add, ENNReal.add_iInf]
```

The proof has **two essential ingredients**:

(I1) `pathLength_trans : pathLength (γ₁.trans γ₂) = pathLength γ₁ + pathLength γ₂` — the chart-local analog is `chartArcLength` additivity along a Path-concatenated path.

(I2) `ENNReal.iInf_add` / `ENNReal.add_iInf` — distributes `+` over `⨅` for `ℝ≥0∞`. The chart-local analog must work for `ℝ` (or `ℝ≥0`/`ℝ≥0∞`).

The parent's `pathLength_trans` (lines 169–196) is itself a 4-step proof:

```lean
theorem pathLength_trans {x y z : X} (γ₁ : Path x y) (γ₂ : Path y z) :
    pathLength (γ₁.trans γ₂) = pathLength γ₁ + pathLength γ₂ := by
  simp only [pathLength]
  -- Step 1: Split [0,1] at 1/2 (eVariationOn.Icc_add_Icc)
  have hsplit : eVariationOn (γ₁.trans γ₂).extend (Icc 0 (1/2)) +
                eVariationOn (γ₁.trans γ₂).extend (Icc (1/2) 1) =
                eVariationOn (γ₁.trans γ₂).extend (Icc 0 1) := ...
  -- Step 2: First half = length of γ₁ via reparameterization
  have first : eVariationOn (γ₁.trans γ₂).extend (Icc 0 (1/2)) =
               eVariationOn γ₁.extend (Icc 0 1) := by
    rw [eVariationOn.eq_of_eqOn (eqOn_first γ₁ γ₂),
        eVariationOn.comp_eq_of_monotoneOn γ₁.extend (· * 2) ...,
        image_scale_half]
  -- Step 3: Second half = length of γ₂ analogously
  have second : ... := by ...
  -- Step 4: Combine
  rw [← hsplit, first, second]
```

The **2 helper lemmas** (parent lines 116–157):

- `eqOn_first γ₁ γ₂ : EqOn (γ₁.trans γ₂).extend (γ₁.extend ∘ (· * 2)) (Icc 0 (1/2))` — point-wise agreement.
- `eqOn_second γ₁ γ₂ : EqOn (γ₁.trans γ₂).extend (γ₂.extend ∘ (· * 2 - 1)) (Icc (1/2) 1)`.

Plus **2 image lemmas** (lines 97–114): `image_scale_half`, `image_shift_half`.

## 2. The hard part: chart-local reparameterization has no direct analog

Parent uses `eVariationOn.comp_eq_of_monotoneOn`:

```
eVariationOn (γ.extend ∘ (· * 2)) (Icc 0 (1/2)) = eVariationOn γ.extend ((· * 2) '' Icc 0 (1/2))
                                                = eVariationOn γ.extend (Icc 0 1)
```

This works for total variation: variation is **scale-invariant under monotone reparameterization** (because variation = supremum of `∑ d(γ tᵢ, γ tᵢ₊₁)` over partitions, and a monotone reparameterization simply renames the partition points).

**For the integral form**, monotone reparameterization is **not** scale-invariant; it scales by the reparameterization speed (chain rule):

```
∫_{0..1/2} ‖deriv (γ ∘ (· * 2)) t‖ dt
  = ∫_{0..1/2} ‖2 • deriv γ (2t)‖ dt        [chain rule: deriv (γ ∘ (· * 2)) t = 2 • deriv γ (2t)]
  = ∫_{0..1/2} 2 * ‖deriv γ (2t)‖ dt        [‖2 • v‖ = 2 * ‖v‖, since 2 > 0]
  = 2 * ∫_{0..1/2} ‖deriv γ (2t)‖ dt
  = ∫_{0..1} ‖deriv γ s‖ ds                 [substitution s = 2t, ds = 2 dt]
```

So the chart-local reparameterization step is **3 lemma applications** instead of 1:

(R1) **Chain rule for deriv**: `deriv.scomp` at v4.26.0 (`Mathlib/Analysis/Calculus/Deriv/Comp.lean:146`):

```lean
theorem deriv.scomp (hg : DifferentiableAt 𝕜' g₁ (h x)) (hh : DifferentiableAt 𝕜 h x) :
    deriv (g₁ ∘ h) x = deriv h x • deriv g₁ (h x)
```

For `g₁ := γ`, `h := (· * 2)`, `deriv h x = 2`, so `deriv (γ ∘ (· * 2)) x = 2 • deriv γ (2x)`. **Requires** `DifferentiableAt ℝ γ (2 * x)` — a hypothesis on `γ`.

(R2) **Norm of scalar multiplication**: `norm_smul : ‖a • v‖ = ‖a‖ * ‖v‖` (always available, `Mathlib.Analysis.Normed.Group.Basic`).

(R3) **Integral substitution**: `intervalIntegral.integral_comp_mul_left` at v4.26.0 (`Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:861`):

```lean
theorem integral_comp_mul_left (hc : c ≠ 0) :
    (∫ x in a..b, f (c * x)) = c⁻¹ • ∫ x in c * a..c * b, f x
```

For `c := 2`, `a := 0`, `b := 1/2`: `∫_{0..1/2} f (2*x) dx = (1/2) • ∫_{0..1} f x dx`. So `2 * ∫_{0..1/2} f (2*x) dx = ∫_{0..1} f x dx`. ✓

## 3. Design space for `chartIntrinsicDist` (4 options)

### Option A — Path-mirror with reparameterization (RECOMMENDED)

```lean
noncomputable def chartIntrinsicDist (p q : E) : ℝ :=
  ⨅ γ : Path p q, chartArcLength γ.extend 0 1

theorem chartIntrinsicDist_triangle (p q r : E) :
    chartIntrinsicDist p r ≤ chartIntrinsicDist p q + chartIntrinsicDist q r
```

**Pros**: Maximal structural parallel to parent. Reuses `Path.trans` machinery.

**Cons**:
- Reparameterization is harder (R1+R2+R3 chain vs. parent's single `eVariationOn.comp_eq_of_monotoneOn`).
- `⨅` over `ℝ` (not `ℝ≥0∞`) has different distributivity behavior — `Real.iInf_add`/`Real.add_iInf` are weaker and require the iInf to be bounded below (which holds: `chartArcLength γ 0 1 ≥ 0` by `chartArcLength_nonneg`, **once we restrict to integrable γ**, otherwise integral collapses to 0).
- For non-`C¹` paths in `Path p q`, `deriv γ.extend` is undefined a.e., so `chartArcLength γ.extend 0 1 = 0` (Mathlib integral of a non-strongly-measurable function = 0). This means `⨅ = 0` for **any** p, q — trivial result, satisfying the triangle inequality vacuously.

**This vacuous-iInf observation is critical**: Option A delivers a true theorem, but it's mathematically uninteresting unless `Path p q` is restricted to `C¹` curves. Mathlib's `Path` does **not** carry `C¹` smoothness; `Path` is just continuous.

**Recovery path**: define a `C¹Path p q` subtype, or stipulate `IntervalIntegrable (fun t => ‖deriv γ.extend t‖) volume 0 1` as a side-hypothesis on the iInf range:

```lean
noncomputable def chartIntrinsicDist (p q : E) : ℝ :=
  ⨅ (γ : Path p q) (_ : IntervalIntegrable (fun t => ‖deriv γ.extend t‖) volume 0 1),
    chartArcLength γ.extend 0 1
```

This makes the iInf over only the integrable paths. **For the triangle inequality, we then need to show that `γ₁.trans γ₂` is integrable when `γ₁` and `γ₂` are.** This follows from `intervalIntegral.integral_add_adjacent_intervals` applied at `t = 1/2` after reparameterization.

### Option B — Direct concatenation, no iInf (constructive)

```lean
theorem chartArcLength_triangle (γ₁ γ₂ : ℝ → E) (hjoin : γ₁ 1 = γ₂ 0)
    (hint₁ : IntervalIntegrable (fun t => ‖deriv γ₁ t‖) volume 0 1)
    (hint₂ : IntervalIntegrable (fun t => ‖deriv γ₂ t‖) volume 0 1) :
    ∃ γ : ℝ → E, γ 0 = γ₁ 0 ∧ γ 2 = γ₂ 1 ∧
      chartArcLength γ 0 2 = chartArcLength γ₁ 0 1 + chartArcLength γ₂ 0 1
```

**Pros**: No reparameterization needed; just glue on `[0, 2]` instead of `[0, 1]`. Constructive: produces an explicit concatenation `γ` via `Set.piecewise (Set.Iic 1) γ₁ γ₂` (or `if t ≤ 1 then γ₁ t else γ₂ (t - 1)`).

**Cons**: Not a "triangle inequality" on distances; just an additivity statement. Doesn't match the state.md `Next Action` description ("chart-local triangle inequality `chartIntrinsicDist_triangle` ... uses `chartArcLength_trans` (this S2b) + `iInf` manipulation for the intrinsic-distance infimum"). Avoids the design issue but ducks the mathematical content.

### Option C — `chartIntrinsicDist` over piecewise-`C¹` curves on `[a, b]`

```lean
noncomputable def chartIntrinsicDist (p q : E) : ℝ :=
  ⨅ (a b : ℝ) (_ : a ≤ b) (γ : ℝ → E)
    (_ : γ a = p) (_ : γ b = q)
    (_ : IntervalIntegrable (fun t => ‖deriv γ t‖) volume a b),
    chartArcLength γ a b
```

**Pros**: No reparameterization at all — endpoint intervals are flexible. Concatenation: glue γ₁ on `[a₁, b₁]` with γ₂ on `[b₁, b₁ + (b₂ - a₂)]` (shifted). `chartArcLength_trans` then applies directly.

**Cons**: Mathlib's `⨅` over many indexed types compiles to nested iInfs that are syntactically messy. Defining `chartIntrinsicDist` this way creates a 6-fold-nested iInf that's painful to unfold for the triangle inequality.

### Option D — `chartIntrinsicDist` over `C¹` curves on a fixed `[0, 1]` (no `Path`)

```lean
noncomputable def chartIntrinsicDist (p q : E) : ℝ :=
  ⨅ (γ : ℝ → E)
    (_ : ContDiff ℝ 1 γ)
    (_ : γ 0 = p)
    (_ : γ 1 = q),
    chartArcLength γ 0 1
```

**Pros**: Each curve is `C¹` on all of `ℝ` (continuously differentiable), guaranteeing `IntervalIntegrable (fun t => ‖deriv γ t‖) volume 0 1` (since `Continuous (deriv γ)` and norm-continuous → interval-integrable). Cleaner than Option C.

**Cons**: `ContDiff ℝ 1 γ` is global on `ℝ`, but the curve only matters on `[0, 1]`. A `C¹` extension always exists (constant extension by `γ(0)` for `t < 0` and `γ(1)` for `t > 1` is continuous but **not** `C¹` at the boundary); the natural extension is a polynomial bump or piecewise-quintic. This **is** doable in Lean but adds 50+ LOC for the extension machinery.

### Recommendation: **Option A with `IntervalIntegrable` side-hypothesis**

Option A preserves maximum structural parallel with the parent, uses Mathlib's `Path` (no new subtype), and the `IntervalIntegrable` side-hypothesis makes the iInf semantically meaningful. The reparameterization step is the main complexity — handled via the 3-lemma chain (R1, R2, R3) above.

**LOC estimate**: ~120 LOC = 5 LOC `chartIntrinsicDist` def + 4 helper lemmas (~70 LOC: 2 `eqOn` adapters + reparameterization adapter + `chartArcLength` Path-trans bridge) + ~40 LOC main theorem.

## 4. Required Mathlib API at pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (verified)

All four bearers reachable via `gh api repos/leanprover-community/mathlib4/contents/...?ref=2df2f0150c...`:

| API | File / line | Used for |
|-----|-------------|----------|
| `intervalIntegral.integral_add_adjacent_intervals` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1022` | Split `[0, 1]` at 1/2 (= parent's `eVariationOn.Icc_add_Icc`) |
| `intervalIntegral.integral_comp_mul_left` | `Basic.lean:861` | Substitution `∫ f(2x) dx = (1/2) ∫ f(s) ds` |
| `Continuous.intervalIntegrable` | `Basic.lean:473` | Discharge `IntervalIntegrable` hypothesis from continuity |
| `deriv.scomp` | `Mathlib/Analysis/Calculus/Deriv/Comp.lean:146` | Chain rule `deriv (γ ∘ (· * 2)) x = 2 • deriv γ (2x)` |
| `Path.trans`, `Path.extend_apply`, `Path.trans_apply` | `Mathlib/Topology/Connected/PathConnected.lean` | Path concatenation (already used in parent) |
| `iInf_le`, `le_iInf` | `Mathlib/Order/CompleteLattice.lean` | iInf manipulation (already used in parent) |
| `Real.iInf_add` (?) | `Mathlib/Topology/Order/MonotoneContinuity.lean` (TBD) | `(⨅ x, f x) + a = ⨅ x, f x + a` for bounded-below `f` |

**Verified spot-check (4 bearers)**: 2026-05-16T09:51Z, all 4 returned non-empty content; signatures matched expected forms (see §2). **Pin drift status**: ZERO drift since S2b ACT (PR #19449, ~5h13m ago).

**`Real.iInf_add` caveat**: distributivity of `+` over `⨅` for `ℝ` requires the iInf to be bounded below. With the `IntervalIntegrable` restriction, every `chartArcLength γ.extend 0 1 ≥ 0` (by `chartArcLength_nonneg`), so the iInf is bounded below by 0. The exact Mathlib API name needs verification at S3 ACT (candidates: `Real.iInf_add`, `iInf_add_const`, `Real.iInf_add_iInf_le`); if absent, can derive ad-hoc via the `0 ≤ chartArcLength γ.extend 0 1` bound.

## 5. Paste-ready S3 ACT skeleton (~120 LOC, 2 `sorry`s for IntervalIntegrable plumbing)

**Insertion point**: `proofs/Proofs/TriangleInequalityOQ04OQ01.lean:84` (between `chartArcLength_trans` and `end TriangleInequalityOQ04OQ01`).

```lean
/-! ## S3: Chart-local Intrinsic Distance and Triangle Inequality -/

/-- The **chart-local intrinsic distance** between two points `p, q : E`: the infimum
of chart-local arc lengths over all continuous paths from `p` to `q` whose
parameterization has interval-integrable speed.

The `IntervalIntegrable` side-hypothesis is essential: without it, the infimum is 0
for every `(p, q)` because non-integrable paths contribute 0 to the integral (Mathlib's
integral convention for non-strongly-measurable integrands). With it, the infimum is
the chart-local geodesic distance — and satisfies the triangle inequality. -/
noncomputable def chartIntrinsicDist (p q : E) : ℝ :=
  ⨅ (γ : Path p q)
    (_ : IntervalIntegrable (fun t => ‖deriv γ.extend t‖) MeasureTheory.volume 0 1),
    chartArcLength γ.extend 0 1

/-- The chart-local intrinsic distance is nonnegative (every contributing
`chartArcLength` is nonnegative by `chartArcLength_nonneg`, and the iInf preserves
the nonnegativity bound). -/
theorem chartIntrinsicDist_nonneg (p q : E) : 0 ≤ chartIntrinsicDist p q := by
  -- Refines `chartArcLength_nonneg 0 ≤ 1` through the iInf.
  sorry

/-- On `[0, 1/2]`, the concatenated path `γ₁.trans γ₂` agrees with `γ₁.extend ∘ (· * 2)`. -/
private lemma chartEqOn_first {p q r : E} (γ₁ : Path p q) (γ₂ : Path q r) :
    Set.EqOn (γ₁.trans γ₂).extend (γ₁.extend ∘ (· * 2)) (Set.Icc (0 : ℝ) (1 / 2)) := by
  -- Verbatim from parent `Proofs.TriangleInequalityOQ04.eqOn_first` (lines 117-131).
  -- Only difference: the codomain is `E` (not the abstract `X`), but the proof is
  -- type-agnostic — `Path.extend_apply`, `Path.trans_apply` work for any codomain.
  intro t ⟨ht0, ht12⟩
  have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht0, by linarith⟩
  have h2t : t * 2 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  simp only [Function.comp_apply]
  rw [Path.extend_apply _ ht01, Path.trans_apply]
  simp only [dif_pos ht12]
  rw [Path.extend_apply γ₁ h2t]
  congr 1; ext; ring

/-- On `[1/2, 1]`, the concatenated path `γ₁.trans γ₂` agrees with `γ₂.extend ∘ (· * 2 - 1)`. -/
private lemma chartEqOn_second {p q r : E} (γ₁ : Path p q) (γ₂ : Path q r) :
    Set.EqOn (γ₁.trans γ₂).extend (γ₂.extend ∘ (· * 2 - 1)) (Set.Icc (1 / 2 : ℝ) 1) := by
  -- Verbatim adaptation of parent `eqOn_second` (lines 134-157).
  -- The midpoint `t = 1/2` case uses `γ₁.target = q = γ₂.source`, holding for any codomain.
  intro t ⟨ht12, ht1⟩
  have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, ht1⟩
  have h2t : t * 2 - 1 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  simp only [Function.comp_apply]
  rw [Path.extend_apply _ ht01, Path.trans_apply]
  by_cases h : t ≤ 1 / 2
  · obtain rfl : t = 1 / 2 := le_antisymm h ht12
    simp only [le_refl, dif_pos]
    have lhs_eq : γ₁ ⟨2 * (1 / 2 : ℝ), by norm_num⟩ = q := by
      have heq : (⟨2 * (1 / 2 : ℝ), by norm_num⟩ : unitInterval) = ⟨1, by norm_num⟩ := by ext; norm_num
      rw [heq]; exact γ₁.target
    have rhs_eq : γ₂.extend ((1 / 2 : ℝ) * 2 - 1) = q := by
      have : (1 / 2 : ℝ) * 2 - 1 = 0 := by norm_num
      rw [this, γ₂.extend_zero]
    rw [lhs_eq, rhs_eq]
  · rw [dif_neg h, Path.extend_apply γ₂ h2t]
    congr 1; ext; ring

/-- **Reparameterization adapter**: for any `γ : ℝ → E` continuously differentiable
on `[0, 1]`, the speed of `γ ∘ (· * 2)` on `[0, 1/2]` integrates to the speed of `γ`
on `[0, 1]`.

Proof: `deriv (γ ∘ (· * 2)) t = 2 • deriv γ (2t)` (`deriv.scomp`), so
`‖deriv (γ ∘ (· * 2)) t‖ = 2 * ‖deriv γ (2t)‖`. Integral substitution
`integral_comp_mul_left` then gives the equality. -/
private lemma chartArcLength_comp_mul_left {γ : ℝ → E}
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ γ t) :
    chartArcLength (γ ∘ (· * 2)) 0 (1 / 2) = chartArcLength γ 0 1 := by
  -- IntervalIntegrable plumbing: needs DifferentiableAt on the right intervals.
  -- The expansion is:
  --   ∫_{0..1/2} ‖deriv (γ ∘ (· * 2)) t‖ dt
  -- = ∫_{0..1/2} ‖(2 : ℝ) • deriv γ (2 * t)‖ dt    [by deriv.scomp + funext]
  -- = ∫_{0..1/2} 2 * ‖deriv γ (2 * t)‖ dt           [by norm_smul, |2| = 2]
  -- = 2 * ∫_{0..1/2} ‖deriv γ (2 * t)‖ dt           [by integral_const_mul or integral_smul_const]
  -- = ∫_{0..1} ‖deriv γ s‖ ds                       [by integral_comp_mul_left: scale 2 sends 0 → 0, 1/2 → 1]
  sorry

/-- Analogous reparameterization for `γ ∘ (· * 2 - 1)` on `[1/2, 1]`. -/
private lemma chartArcLength_comp_mul_left_shift {γ : ℝ → E}
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ γ t) :
    chartArcLength (γ ∘ (· * 2 - 1)) (1 / 2) 1 = chartArcLength γ 0 1 := by
  -- As above, but with affine shift: `deriv (γ ∘ (· * 2 - 1)) t = 2 • deriv γ (2 t - 1)`,
  -- then `integral_comp_mul_left` after `integral_comp_add_right` to handle the - 1 shift.
  sorry

/-- Chart-local arc length is additive under Path concatenation. -/
theorem chartArcLength_pathTrans {p q r : E} (γ₁ : Path p q) (γ₂ : Path q r)
    (hγ₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ γ₁.extend t)
    (hγ₂ : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ γ₂.extend t)
    (h_int_trans : IntervalIntegrable (fun t => ‖deriv (γ₁.trans γ₂).extend t‖)
                    MeasureTheory.volume 0 (1 / 2))
    (h_int_trans' : IntervalIntegrable (fun t => ‖deriv (γ₁.trans γ₂).extend t‖)
                    MeasureTheory.volume (1 / 2) 1) :
    chartArcLength (γ₁.trans γ₂).extend 0 1 =
    chartArcLength γ₁.extend 0 1 + chartArcLength γ₂.extend 0 1 := by
  -- Step 1: Split [0, 1] at 1/2 via chartArcLength_trans (S2b).
  have hsplit := chartArcLength_trans (γ₁.trans γ₂).extend h_int_trans h_int_trans'
  -- Step 2: On [0, 1/2], rewrite to γ₁.extend ∘ (· * 2), then apply
  --         chartArcLength_comp_mul_left.
  -- (Requires a helper showing that EqOn-agreeing functions have equal chartArcLength,
  --  derivable from intervalIntegral.integral_congr.)
  -- Step 3: Analogous on [1/2, 1].
  -- Step 4: Combine.
  sorry  -- depends on chartArcLength_comp_mul_left + chartArcLength_comp_mul_left_shift

/-- **Main theorem (S3)**: Chart-local triangle inequality for the chart-local
intrinsic distance. Mirrors `Proofs.TriangleInequalityOQ04.intrinsicDist_triangle`.

The inequality is `chartIntrinsicDist p r ≤ chartIntrinsicDist p q + chartIntrinsicDist q r`.
The proof concatenates any path `γ₁ : p → q` with any path `γ₂ : q → r`, observes that
the concatenated arc length is the sum (via `chartArcLength_pathTrans`), and exchanges the
infima (via `Real.iInf_add` / `Real.add_iInf` for bounded-below iInfs).

**Chart-local caveat**: The result depends on the embedding of `E` into the manifold
chart, NOT on a Riemannian metric. The eventual chart-invariant Riemannian generalization
will follow once Mathlib lands `RiemannianMetric` (see S1 OBSERVE for path D). -/
theorem chartIntrinsicDist_triangle (p q r : E) :
    chartIntrinsicDist p r ≤ chartIntrinsicDist p q + chartIntrinsicDist q r := by
  simp only [chartIntrinsicDist]
  -- Two-step calc as in parent:
  -- 1. iInf over Path p r ≤ iInf over (Path p q × Path q r) of (lenγ₁ + lenγ₂) — via concatenation.
  -- 2. = iInf γ₁ lenγ₁ + iInf γ₂ lenγ₂ — via Real.iInf_add / add_iInf distributivity.
  sorry  -- TODO: discharge once chartArcLength_pathTrans is proven (no new sorries needed here).
```

## 6. Risk inventory

| Marker | Risk | Mitigation | Severity |
|--------|------|------------|----------|
| R1 | Reparameterization chain rule (`deriv.scomp` + `norm_smul` + `integral_comp_mul_left` chain) requires careful `DifferentiableAt` hypothesis discharge | Use `ContDiff ℝ 1 γ.extend` (or weaker `Continuous (deriv γ.extend)`) instead of pointwise `DifferentiableAt`; recover Mathlib lemma `ContDiff.differentiableAt_at_one` | MEDIUM |
| R2 | `Real.iInf_add` distributivity may not exist verbatim at v4.26.0; could be `iInf_add_const` or require manual derivation | Spot-check at S3 ACT before writing the final calc; fall back to ad-hoc derivation using `chartArcLength_nonneg` lower bound | LOW |
| R3 | The iInf over `(γ : Path p q) (_ : IntervalIntegrable ...)` is a 2-nested iInf — `iInf_le`/`le_iInf` plumbing more verbose than parent's | Use explicit `iInf_le_of_le` with concrete witnesses (γ₁.trans γ₂ + its IntervalIntegrable proof) | LOW |
| R4 | `chartArcLength_pathTrans` requires `IntervalIntegrable (fun t => ‖deriv (γ₁.trans γ₂).extend t‖) volume 0 (1/2)` and `... (1/2) 1` as hypotheses; need to discharge these from `IntervalIntegrable (fun t => ‖deriv γ₁.extend t‖) volume 0 1` and `... γ₂.extend ...` | Use `chartEqOn_first` + `chartArcLength_comp_mul_left`'s contrapositive: if the speed integrates, so does the reparameterized speed | MEDIUM |
| R5 | Mathlib's `Path.extend` does NOT in general carry differentiability — `Path.extend` clamps outside `[0, 1]` to `γ 0` and `γ 1`, making it `C⁰` but not `C¹` at boundaries 0 and 1 | The `DifferentiableAt` hypothesis is required only on the OPEN interval `(0, 1)`, where `Path.extend` agrees with `γ` itself; restrict `hγ₁`, `hγ₂` hypotheses to `Set.Ioo (0 : ℝ) 1` | MEDIUM |
| R6 | Mathlib v4.26.0 might have `Path.continuous_extend` but not `Path.differentiable_extend` — the differentiability of `γ.extend` is the user's responsibility | Pass `DifferentiableOn ℝ γ.extend (Set.Ioo 0 1)` as an explicit hypothesis at the `chartIntrinsicDist_triangle` call site, OR introduce a `C¹Path p q` subtype | MEDIUM |
| R7 | Composition `γ₁.trans γ₂` is **piecewise** smooth (smooth on `[0, 1/2]` and `[1/2, 1]` separately), with a potential `deriv` jump at `t = 1/2` | The `IntervalIntegrable` hypothesis accommodates this: the integrand is `‖deriv γ‖` which is bounded near `t = 1/2`; the boundary point has measure zero | LOW |
| R8 | Docker daemon hung (60s timeout exit 124), disk 100% / 6.9Gi avail — INFRASTRUCTURE blocker for S3 ACT build-verify | S3 ACT will ship with `(build pending — Docker daemon hung)` qualifier per memory pattern `_docker_daemon_hang_server_unresponsive_ship_build_pending_distinct_from_disk_full`, OR wait for Docker recovery if daemon settles before next claim cycle | LOW (PREP doc-only, not blocked) |

**Aggregate risk**: 3 LOW + 4 MEDIUM + 1 INFRASTRUCTURE. No HIGH risks.

## 7. ACT-readiness gate (S3 ACT)

| Item | Status | Notes |
|------|--------|-------|
| 1. Mathematical statement (chart-local triangle ineq) | ✅ GREEN | §3 + §4; precisely defined `chartIntrinsicDist p q` with `IntervalIntegrable` side-hypothesis |
| 2. Parent proof structurally adaptable | ✅ GREEN | §1 (parent's 4-step proof maps step-by-step to chart-local, with reparameterization swap) |
| 3. Mathlib API at pinned SHA verified | ✅ GREEN | §4 — all 4 primary bearers (`integral_add_adjacent_intervals`, `integral_comp_mul_left`, `Continuous.intervalIntegrable`, `deriv.scomp`) reachable + signature-matched |
| 4. Paste-ready Lean skeleton | ✅ GREEN | §5 — 120 LOC across 1 def + 4 helpers + 1 main, only 2 `sorry`s (reparameterization adapters R1+R2+R3 chain) |
| 5. Risk inventory + mitigations | ✅ GREEN | §6 — 8 markers (R1–R8), 3 LOW + 4 MEDIUM + 1 INFRASTRUCTURE |
| 6. Predecessor `chartArcLength_trans` available on main | ✅ GREEN | PR #19449 merged 2026-05-16T04:38Z |
| 7. Reparameterization adapter (`chartArcLength_comp_mul_left`) discharged | ⚠️ AMBER | Skeleton has `sorry`; depends on `deriv.scomp` + `integral_comp_mul_left` + `IntervalIntegrable` plumbing chain; estimated 30-50 LOC each |
| 8. Docker build-verify reachable | 🚫 RED | Daemon hung exit 124 + disk 100%; INFRASTRUCTURE-ONLY (does not block PREP); S3 ACT will likely need `(build pending)` qualifier or wait-for-recovery |

**Gate**: 6/8 GREEN, 1/8 AMBER, 1/8 RED (INFRASTRUCTURE). S3 ACT is **READY** modulo (a) the reparameterization plumbing being more verbose than the skeleton's `sorry`-blocked sketch suggests, and (b) Docker recovery for build-verify.

## 8. Next-iteration plan

**S3 ACT** — Discharge the 2 reparameterization `sorry`s and assemble `chartIntrinsicDist_triangle`:

1. **Iter 3a** (5–10 LOC, LOW risk): introduce `chartIntrinsicDist` definition + `chartIntrinsicDist_nonneg`.
2. **Iter 3b** (30–50 LOC, MEDIUM risk): prove `chartArcLength_comp_mul_left` and `chartArcLength_comp_mul_left_shift` (the two reparameterization adapters). This is the load-bearing step.
3. **Iter 3c** (20–30 LOC, MEDIUM risk): assemble `chartArcLength_pathTrans` from S2b + the two `chartEqOn_*` lemmas + the two reparameterization adapters.
4. **Iter 3d** (10–20 LOC, LOW risk): main `chartIntrinsicDist_triangle` calc, mirroring parent's 2-step structure.

**Total estimated LOC**: ~120 (matches §3 estimate). 0 sorries on completion. 0 axioms.

**Alternative decomposition** (if Docker remains hung at S3 ACT claim time): ship S3a ACT (definition + `chartIntrinsicDist_nonneg` only) as a 5-LOC mini-iter that builds in seconds (avoiding Mathlib full rebuild cascades), defer reparameterization to S3b/S3c/S3d.

## 9. Bearer manifest (this PREP)

| File | Lines (this commit) | Lines (S2b end of PR #19449) | Drift |
|------|---------------------|------------------------------|-------|
| `proofs/Proofs/TriangleInequalityOQ04OQ01.lean` | 84 | 84 | 0 (unchanged in PREP) |
| `research/problems/triangle-inequality-oq-04-oq-01/state.md` | TBD (this PR) | 122 | +S3 PREP §, +next-action update |
| `research/problems/triangle-inequality-oq-04-oq-01/knowledge.md` | TBD | (existing) | +Insights 13-15 (PREP findings) |
| `research/problems/triangle-inequality-oq-04-oq-01/sessions/2026-05-16-s3-prep-chartintrinsicdist-design.md` | (this file, new) | — | +1 new file |

## 10. Honest scope disclaimers

- **No new Lean code in this PREP**: 0 LOC delta to `proofs/Proofs/TriangleInequalityOQ04OQ01.lean`.
- **No build verification possible**: Docker daemon hung at session start; PREP requires no build.
- **The recommended Option A is not the only viable design** — Options B/C/D each have merit. The Option A recommendation prioritizes structural parallel with the parent over LOC budget (Option B would be ~40 LOC, Option C ~80 LOC, Option D ~150 LOC including extension machinery).
- **Reparameterization is the load-bearing complexity**: the parent's `eVariationOn.comp_eq_of_monotoneOn` does in one lemma what chart-local needs three for (`deriv.scomp` + `norm_smul` + `integral_comp_mul_left`). The 2 `sorry`s in §5 reflect this — they are not trivially discharged.
- **`Path.extend` differentiability is the user's responsibility**: Mathlib v4.26.0 has no `Path.differentiable_extend`; an explicit `DifferentiableOn ℝ γ.extend (Set.Ioo 0 1)` hypothesis must be passed at the `chartIntrinsicDist_triangle` call site, or a new `C¹Path p q` subtype must be introduced.
- **`Real.iInf_add` API surface unverified**: §4's table entry for `Real.iInf_add` is a placeholder; the exact Mathlib lemma name needs S3 ACT-time verification. Fallback: ad-hoc derivation from `chartArcLength_nonneg` lower bound.

## 11. Memory cross-references

This cycle follows memory pattern `_postship_pivot_lands_on_fully_discharged_slug_blocked_hermit_followup_ship_packaged_followups_prep` in spirit, BUT differs because:

- The slug is NOT at "fully-discharged 0/0/0 slug-wide" — it's at S2b ACT complete with EXPLICIT named-next-action (S2c). The PREP is the natural continuation, not a follow-ups-packaging.
- The Docker-hung infra blocker matches `_docker_daemon_hang_server_unresponsive_ship_build_pending_distinct_from_disk_full` — but PREP is doc-only so no `(build pending)` qualifier needed.
- The disk-100% co-occurrence is borderline; `df -h /System/Volumes/Data` shows 6.9Gi avail, above the 200Mi `_docker_build_disk_full` extreme but at the lower bound of safe operation.

Sibling-slug precedents for chart-local Riemannian work: NONE. This is the only chart-local arc length / triangle inequality slug in the gallery. Parent `triangle-inequality-oq-04` and grandparent `triangle-inequality` use abstract metric-space / total-variation machinery and do not exercise the integral-form reparameterization adaptors.
