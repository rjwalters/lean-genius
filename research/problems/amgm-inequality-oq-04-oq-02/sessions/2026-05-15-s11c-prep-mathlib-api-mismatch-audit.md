# S11c PREP — Mathlib API mismatch audit of `dK_dk` (merged) and `dE_dk` (PR #19222 §3)

**Researcher.** researcher-8
**Date.** 2026-05-15 ~08:30Z
**Phase.** ACT (S11c PREP — follow-up audit of PR #19222 + the merged `dK_dk` template)
**Mode.** doc-only
**Lean changes.** 0
**Parent.** PR #19222 (S11b PREP, MERGEABLE) — which mirrors merged `dK_dk` at `AmgmInequalityOQ04OQ02.lean:1482-1557`
**Estimated reading.** 8-10 min

## TL;DR

PR #19222 §3 ships a literal 76-LOC drop-in body for `dE_dk` that mirrors
the merged `dK_dk` theorem (`AmgmInequalityOQ04OQ02.lean:1482-1557`,
landed via #17606 as "build pending"). This sibling-PREP audits the
proposed text against **the lake-pinned Mathlib SHA**
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (`leanprover/lean4:v4.26.0`)
and finds:

| # | Finding | Severity | Affects |
|---|---------|----------|---------|
| F1 | **Mathlib lemma first arg is `ε_pos : 0 < ε`, not `s ∈ 𝓝 k`** | BLOCKER | both `dK_dk` (merged) + `dE_dk` (PR #19222 §3) |
| F2 | **Lemma's `h_bound`/`h_diff` quantify over `Metric.ball x₀ ε`, not `Set.Ioo (-M) M`** | BLOCKER | both |
| F3 | E-side helper inventory (PR #19222 §2 table E1-E14) verified line-accurate on origin/main | OK | confirms #19222 §2 |
| F4 | E3/E4 simplifications (drop `hk : k² < 1`) verified by file read | OK | confirms #19222 §2 |
| F5 | E-side `integral_dIntegrandE_eq` exists at line 488 with stated signature | OK | confirms #19222 §3 final rw |

**Net effect.** F1 + F2 together mean **both the merged `dK_dk` AND the
proposed `dE_dk` will fail to compile** under the pinned Mathlib SHA.
The "(build pending)" tag on #17606 was load-bearing — no auditor or
mechanic has yet validated `dK_dk` against the actual API, and #19222
mirroring it inherits the same break.

This sibling-PREP is **strictly doc-only**: a single new `sessions/`
file. Zero edits to `state.md`, `problem.md`, gallery JSON, or any
`proofs/Proofs/` file. Orthogonal to all currently-open PRs (#17371,
#17445, #17477, #19024, #19187, #19222).

## §1 — Mathlib bearer pin-verification

### §1.1 Lemma signature at lake SHA

**File.** `Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean`
**Ref.** `?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
**Lines.** 96-111 (verified via `gh api repos/leanprover-community/mathlib4/contents/...`)

```lean
namespace intervalIntegral

nonrec theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le
    {F : 𝕜 → ℝ → E} {F' : 𝕜 → ℝ → E} {x₀ : 𝕜}
    (ε_pos : 0 < ε)                                                       -- ← FIRST EXPLICIT ARG
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) (μ.restrict (Ι a b)))
    (hF_int : IntervalIntegrable (F x₀) μ a b)
    (hF'_meas : AEStronglyMeasurable (F' x₀) (μ.restrict (Ι a b)))
    (h_bound : ∀ᵐ t ∂μ, t ∈ Ι a b → ∀ x ∈ ball x₀ ε, ‖F' x t‖ ≤ bound t)   -- ← `Metric.ball x₀ ε`
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_diff : ∀ᵐ t ∂μ, t ∈ Ι a b → ∀ x ∈ ball x₀ ε, HasDerivAt (fun x => F x t) (F' x t) x) :
    IntervalIntegrable (F' x₀) μ a b ∧
      HasDerivAt (fun x => ∫ t in a..b, F x t ∂μ) (∫ t in a..b, F' x₀ t ∂μ) x₀ := by
  ...
```

Header at top of file binds `ε : ℝ` as an auto-bound implicit:
```lean
variable {𝕜 : Type*} [RCLike 𝕜] {μ : Measure ℝ} {E : Type*} ...
  ... {a b ε : ℝ} {bound : ℝ → ℝ}
```

So `ε` is auto-inferred from the type of `ε_pos`. The first **explicit**
positional arg is `ε_pos : 0 < ε`.

### §1.2 Underlying non-namespaced lemma in `ParametricIntegral.lean`

**File.** `Mathlib/Analysis/Calculus/ParametricIntegral.lean`
**Lines.** 286-292 (same SHA pin)

```lean
theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le (ε_pos : 0 < ε)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ) (hF_int : Integrable (F x₀) μ)
    {F' : 𝕜 → α → E} (hF'_meas : AEStronglyMeasurable (F' x₀) μ)
    (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, ‖F' x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, HasDerivAt (F · a) (F' x a) x) :
    Integrable (F' x₀) μ ∧ HasDerivAt (fun n ↦ ∫ a, F n a ∂μ) (∫ a, F' x₀ a ∂μ) x₀ := by
  ...
```

Same shape: first explicit arg is `ε_pos`, `h_bound`/`h_diff` use
`∀ x ∈ ball x₀ ε`.

### §1.3 Reference usage in Mathlib

**File.** `Mathlib/Analysis/MellinTransform.lean`
**Lines.** 397 (same SHA pin)

```lean
  obtain ⟨v, hv0, hv1, hv2⟩ : ∃ v : ℝ, 0 < v ∧ ... := ...
  ...
  have h4 : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0),
      ∀ z : ℂ, z ∈ Metric.ball s v → ‖F' z t‖ ≤ bound t := ...
  have h6 : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0),
      ∀ y : ℂ, y ∈ Metric.ball s v → HasDerivAt (fun z : ℂ => F z t) (F' y t) y := ...
  have main := hasDerivAt_integral_of_dominated_loc_of_deriv_le hv0 h1 h2 h3 h4 h5 h6
```

Note `hv0 : 0 < v` is the first arg, and both `h4` (h_bound) and `h6`
(h_diff) quantify over `z ∈ Metric.ball s v`. This is the **canonical
calling convention** for the lemma.

### §1.4 Negative result — no `nhds`-based variant exists

A search across Mathlib for any wrapper or alternate form of
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` taking `s ∈ 𝓝 x₀`
in place of `ε_pos : 0 < ε` returns **zero hits**:

```
$ gh api 'search/code?q="hasDerivAt_integral_of_dominated"+"nhds"+repo:leanprover-community/mathlib4'
→ Mathlib/Analysis/Calculus/ParametricIntegral.lean      (lemma def + signature)
→ Mathlib/Analysis/MellinTransform.lean                  (usage with ball + 0<v)
→ Mathlib/Probability/Moments/ComplexMGF.lean            (usage with ball + 0<ε)
→ Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean (nonrec wrapper)
```

All four usages take `0 < ε` first. **No `s ∈ 𝓝 x₀` shape exists.**

## §2 — Bug F1: merged `dK_dk` first-arg type mismatch

### §2.1 The merged code (origin/main, file post-#17606)

`proofs/Proofs/AmgmInequalityOQ04OQ02.lean:1485-1548`:

```lean
  -- Pick the band M = (k+1)/2 ∈ (k, 1); note M² < 1.
  set M : ℝ := (k + 1) / 2 with hM_def
  ...
  set s : Set ℝ := Set.Ioo (-M) M with hs_def
  have hk_mem_s : k ∈ s := ⟨by linarith, hk_lt_M⟩
  have hs_nhds : s ∈ 𝓝 k := isOpen_Ioo.mem_nhds hk_mem_s
  ...
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs_nhds hF_meas hF_int hF'_meas h_bound h_bound_int h_diff
```

### §2.2 The type error

- Position-1 of the lemma: `(ε_pos : 0 < ε)` — type is `0 < ε`.
- Position-1 of the call:  `hs_nhds : s ∈ 𝓝 k` — type is `s ∈ 𝓝 k`.

These are **different propositions** at the level of definitional
equality. Lean's elaborator cannot unify `s ∈ 𝓝 k` with `0 < ?ε` because:

1. `s ∈ 𝓝 k` reduces to `s ∈ nhds k`, which is an application of
   the `Membership` instance for `Filter`. Concretely, `s ∈ nhds k`
   unfolds to `∃ U ∈ nhdsBasis k, U ⊆ s` (or similar — depending on the
   Filter API used). No `<` or `0` appears in the unfolded form.

2. `0 < ε` reduces to `LT.lt 0 ε` where `ε : ℝ`. Type-level: `Prop`
   built from `0 : ℝ`, `ε : ℝ`, and the `LT ℝ` instance.

No unification path produces `0 = ε := ?` and `0 < ε := s ∈ 𝓝 k`.

**Consequence.** The merged `dK_dk` proof fails to elaborate at the
lake-pinned Mathlib SHA. The PR description ("build pending") combined
with no auditor verification means this was never caught.

### §2.3 Same bug propagated to PR #19222 §3

PR #19222 mirrors `dK_dk` line-by-line (§3 of the PR text). The
problematic call at the bottom of §3 reads:

```lean
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs_nhds hF_meas hF_int hF'_meas h_bound h_bound_int h_diff
```

Identical first-arg shape — `hs_nhds : s ∈ 𝓝 k`. Same elaboration
failure expected.

## §3 — Bug F2: `h_bound`/`h_diff` quantify over `Set.Ioo (-M) M`, not `Metric.ball k ε`

### §3.1 The merged code

`dK_dk` constructs (file line 1526-1545):

```lean
  have h_bound : ∀ᵐ θ ∂MeasureTheory.volume,
      θ ∈ Set.uIoc (0 : ℝ) (π / 2) →
      ∀ κ ∈ s, ‖dIntegrandK κ θ‖ ≤ boundDIntegrandK M θ := ...
  ...
  have h_diff : ∀ᵐ θ ∂MeasureTheory.volume,
      θ ∈ Set.uIoc (0 : ℝ) (π / 2) →
      ∀ κ ∈ s, HasDerivAt
        (fun x => AmgmInequalityOQ04OQ01.ellipticIntegrand x θ)
        (dIntegrandK κ θ) κ := ...
```

Where `s := Set.Ioo (-M) M` (file line 1494).

### §3.2 The lemma's requirement

Per §1.1, the lemma's `h_bound` is typed:

```lean
(h_bound : ∀ᵐ t ∂μ, t ∈ Ι a b → ∀ x ∈ ball x₀ ε, ‖F' x t‖ ≤ bound t)
```

Where `ball x₀ ε := Metric.ball x₀ ε := {x : dist x x₀ < ε}`. For
`x₀ = k : ℝ` and `ε : ℝ`:

```
Metric.ball k ε = Set.Ioo (k - ε) (k + ε)
```

### §3.3 The geometric mismatch

The merged code's `s := Set.Ioo (-M) M`. This equals
`Metric.ball k ε` **only if** `k - ε = -M` and `k + ε = M`, i.e.
`ε = M` and `k = 0`. For any `k > 0` (which is the entire stated
domain of `dK_dk`), the equality fails.

Concretely at `k = 1/2`, `M = 3/4`:
- `s = Set.Ioo (-3/4) (3/4) = (−0.75, 0.75)`
- `Metric.ball (1/2) ε` for any `ε > 0` is `(0.5 − ε, 0.5 + ε)`.

To get `(−0.75, 0.75)` from `Metric.ball (1/2) ε`, we'd need
`ε = 1.25` simultaneously to the left and right of `1/2` — impossible.

**Consequence.** Even if Lean could unify the `ε_pos` slot (F1), the
`h_bound` and `h_diff` slots fail elaboration because their quantifier
domain is `∀ κ ∈ s`, but the lemma reads `∀ x ∈ ball k ε`.

### §3.4 Same bug propagated to PR #19222 §3

PR #19222 §3 reproduces the `∀ κ ∈ s` quantifier verbatim in both
`h_bound` and `h_diff` (with E-side substitutions but K-side ball
shape). Same elaboration failure expected.

## §4 — Corrected template (for next mechanic / fresh-ACT claimer)

### §4.1 Replace `(M, s)` with `(ε, ball)`

For `dK_dk` (and by mirror, `dE_dk`), the cleanest fix is:

```lean
  -- Pick the ball radius ε = min(k, 1-k) / 2 so Metric.ball k ε ⊆ (0,1).
  set ε : ℝ := min k (1 - k) / 2 with hε_def
  have hε_pos : 0 < ε := by
    simp only [hε_def]; positivity
  have hε_lt_k : ε < k := by
    simp only [hε_def]
    have h1 : min k (1 - k) ≤ k := min_le_left _ _
    have h2 : 0 < min k (1 - k) := lt_min hk_pos (by linarith)
    linarith
  have hε_lt_1mk : ε < 1 - k := by
    simp only [hε_def]
    have h1 : min k (1 - k) ≤ 1 - k := min_le_right _ _
    have h2 : 0 < min k (1 - k) := lt_min hk_pos (by linarith)
    linarith
  -- For κ ∈ Metric.ball k ε we have 0 < κ < 1, so κ² < 1.
  have h_kappa_sq_lt_one : ∀ κ ∈ Metric.ball k ε, κ ^ 2 < 1 := by
    intro κ hκ
    rw [Metric.mem_ball, Real.dist_eq] at hκ
    have hκ_pos : 0 < κ := by
      have : -ε < κ - k := by
        have := abs_lt.mp hκ
        linarith
      linarith
    have hκ_lt_one : κ < 1 := by
      have : κ - k < ε := by
        have := abs_lt.mp hκ
        linarith
      linarith
    nlinarith [hκ_pos, hκ_lt_one]
  ...
```

Then the `h_bound` and `h_diff` quantifiers become:

```lean
  have h_bound : ∀ᵐ θ ∂MeasureTheory.volume,
      θ ∈ Set.uIoc (0 : ℝ) (π / 2) →
      ∀ κ ∈ Metric.ball k ε, ‖dIntegrandK κ θ‖ ≤ boundDIntegrandK M θ := ...
  have h_diff : ∀ᵐ θ ∂MeasureTheory.volume,
      θ ∈ Set.uIoc (0 : ℝ) (π / 2) →
      ∀ κ ∈ Metric.ball k ε, HasDerivAt
        (fun x => AmgmInequalityOQ04OQ01.ellipticIntegrand x θ)
        (dIntegrandK κ θ) κ := ...
```

(Note: `M := some larger constant` is still useful — it's the bound
inflation cap. The choice of `ε := min(k, 1-k)/2` ensures
`Metric.ball k ε ⊆ (0,1)`, which gives `κ² < 1` for the bound
hypothesis without needing `M`. Alternatively, use
`M := max |k − ε| |k + ε|` and keep the existing bound infrastructure.)

### §4.2 Reorder the lemma call

```lean
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hε_pos hF_meas hF_int hF'_meas h_bound h_bound_int h_diff
```

First arg `hε_pos : 0 < ε` matches the lemma's `(ε_pos : 0 < ε)` slot.

### §4.3 Estimated LOC delta for the fix

- Replace ~12 lines of `M`/`s`/`hs_nhds` machinery with ~25 lines of
  `ε`/`ball` machinery (positivity + bounds + `κ² < 1` derivation).
- Net delta per theorem: **+13 LOC** (modest).
- Two theorems (`dK_dk`, `dE_dk`) ⇒ total +26 LOC vs. the broken
  template.

### §4.4 Alternative — minimal fix preserving most of the broken text

If the mechanic wants the smallest possible patch:

1. Insert immediately after `hk_lt_M`:
   ```lean
   set ε : ℝ := min (M - k) (k - (-M)) with hε_def    -- = min(M − k, k + M)
   have hε_pos : 0 < ε := by simp only [hε_def]; constructor <;> linarith
   have h_ball_eq_s : Metric.ball k ε ⊆ s := by
     intro x hx
     rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
     obtain ⟨hx_low, hx_hi⟩ := hx
     refine ⟨?_, ?_⟩
     · linarith [min_le_left (M - k) (k - (-M)), hx_low]
     · linarith [min_le_right (M - k) (k - (-M)), hx_hi]
   ```
2. Rewrite `h_bound` and `h_diff` to `∀ κ ∈ Metric.ball k ε`, using
   `h_ball_eq_s` to lift the existing `s`-based derivations:
   ```lean
   have h_bound : ∀ᵐ θ ∂MeasureTheory.volume,
       θ ∈ Set.uIoc (0 : ℝ) (π / 2) →
       ∀ κ ∈ Metric.ball k ε, ‖dIntegrandK κ θ‖ ≤ boundDIntegrandK M θ := by
     refine MeasureTheory.ae_of_all _ ?_
     intro θ _ κ hκ
     rw [Real.norm_eq_abs]
     have hκs : κ ∈ s := h_ball_eq_s hκ
     exact dIntegrandK_abs_le_bound hM_sq_lt_one hM_nn κ θ (h_kappa_sq_le κ hκs)
   -- and similarly for h_diff
   ```
3. Replace the call's first arg `hs_nhds` with `hε_pos`.

LOC delta: ~+8 per theorem.

### §4.5 Recommendation

Path §4.1 (full rewrite to `ε`/`ball`) is cleaner. Path §4.4 (lift
`s`-domain via `h_ball_eq_s`) preserves more existing text and may be
faster to apply. The choice depends on whether the mechanic prefers
readability or minimal-diff.

## §5 — Reaffirmed accurate claims in PR #19222

The Mathlib API mismatch (F1 + F2) is the only structural finding.
Everything else in PR #19222 is correct:

### §5.1 E-side helper inventory (PR #19222 §2 table)

Verified line-accurate against `proofs/Proofs/AmgmInequalityOQ04OQ02.lean`
on origin/main (1559 lines, file SHA = `7c726654c9d57daa8690db436d9b623da184c91c`):

| # | Symbol | Claimed line | Verified |
|---|--------|-------------|----------|
| E1 | `ellipticIntegrandE` | 76 | ✓ exact match |
| E2 | `ellipticE` | 82 | ✓ exact match |
| E3 | `integrandE_continuous (k : ℝ)` | 116 | ✓ no `hk` arg |
| E4 | `ellipticE_integrable (k : ℝ)` | 123 | ✓ no `hk` arg |
| E5 | `dIntegrandE` | 393 | ✓ exact match |
| E6 | `dIntegrandE_continuous (hk : k^2 < 1)` | 397 | ✓ exact match |
| E7 | `dIntegrandE_integrable (hk : k^2 < 1)` | 412 | ✓ exact match |
| E8 | `integrandE_hasDerivAt_in_k (hk : k^2 < 1) (θ : ℝ)` | 421 | ✓ exact match |
| E9 | `dIntegrandE_mul_k (hk : k^2 < 1) (θ : ℝ)` | 464 | ✓ exact match |
| E10 | `integral_dIntegrandE_eq (hk_pos : 0 < k) (hk_lt : k < 1)` | 488 | ✓ exact match |
| E11 | `boundDIntegrandE` | 541 | ✓ exact match |
| E12 | `boundDIntegrandE_continuous (hM : M^2 < 1)` | 545 | ✓ exact match |
| E13 | `boundDIntegrandE_integrable (hM : M^2 < 1)` | 559 | ✓ exact match |
| E14 | `dIntegrandE_abs_le_bound (hM hM_nn κ θ hκ)` | 575 | ✓ exact match |

**All 14 helpers exist at the claimed line numbers with the claimed
signatures.** The two E-vs-K simplifications (E3 and E4 take no
`hk : k² < 1`) are also verified.

### §5.2 Closing `exact h_deriv` step

PR #19222 §3's final two lines:

```lean
  rw [integral_dIntegrandE_eq hk_pos hk_lt] at h_deriv
  exact h_deriv
```

This is the same shape as `dK_dk`'s final two lines (file 1555-1557).
Both rely on `ellipticE` (resp. `ellipticK`) being definitionally equal
to its `∫ θ in 0..π/2, integrand` unfolding. **This is correct** —
`ellipticE` is a `noncomputable def` at line 82-83 with that exact body.
The `exact h_deriv` will work via definitional unfolding.

(This step is independent of bugs F1/F2 — the structural mismatch is
in the call to the parametric integral lemma, not in the final rewrite.)

### §5.3 Risk §4.1 (inlining `h_kappa_sq_lt_one` into `h_diff`)

PR #19222 §4.1 notes that the E-side `h_diff` inlines the per-κ
`κ² < 1` derivation (rather than naming a separate
`h_kappa_sq_lt_one : ∀ κ ∈ s, κ² < 1` hypothesis as the K-side does).
This is a stylistic choice and is **correct**: in either case the
discharge invokes `lt_of_le_of_lt (h_kappa_sq_le κ hκ) hM_sq_lt_one`.

(Note: this independence from F1/F2 is preserved — the inlined form is
still a syntactic refactor of the same broken s-domain quantifier.)

## §6 — Race / orthogonality

### §6.1 File-touch race-check (verified 2026-05-15 08:25Z)

This PREP creates a **single new file**:
`research/problems/amgm-inequality-oq-04-oq-02/sessions/2026-05-15-s11c-prep-mathlib-api-mismatch-audit.md`.

Zero edits to:
- `state.md` (orthogonal to #19024 STATE-SYNC).
- `problem.md`, `knowledge.md`.
- Gallery `meta.json`, `src/data/research/problems/.../json`.
- Any `proofs/Proofs/` file.
- Any other `sessions/` file (different filename).

| Open PR | Touches | Conflict |
|---------|---------|----------|
| #17371 (dE_dk S6 original, ~7d stale) | .lean, .json, state.md, sessions/2026-05-08-s06-… | NONE |
| #17445 (dE_dk S8 replay, ~7d stale) | .lean, .json, state.md, sessions/2026-05-08-s08-… | NONE |
| #17477 (complModulus boundary, ~7d stale) | .lean, .json, state.md, sessions/2026-05-08-s09-… | NONE |
| #19024 (STATE-SYNC, ~23h) | state.md, .json (no sessions/ touch) | NONE |
| #19187 (S11 PREP) | sessions/2026-05-14-s11-prep-wronskian-closure.md | NONE |
| #19222 (S11b PREP) | sessions/2026-05-15-s11b-prep-de-dk-fallback-skeleton.md | NONE |

Strictly orthogonal across the board.

### §6.2 Provenance

- **Lemma signature pin.** `gh api repos/leanprover-community/mathlib4/contents/Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` — fetched 2026-05-15 08:10Z.
- **Underlying lemma pin.** `Mathlib/Analysis/Calculus/ParametricIntegral.lean` at the same SHA — fetched 2026-05-15 08:12Z.
- **Reference usage pin.** `Mathlib/Analysis/MellinTransform.lean` at the same SHA — fetched 2026-05-15 08:15Z.
- **K-side template source.** `proofs/Proofs/AmgmInequalityOQ04OQ02.lean` on origin/main, lines 1482-1557. Merged via #17606 (`deedde5f669`) "(build pending)".
- **E-side helper inventory source.** Same file, lines 76-577. Read 2026-05-15 08:20Z.
- **Toolchain pin.** `leanprover/lean4:v4.26.0` (per `proofs/lean-toolchain`).

### §6.3 Open follow-ups for future researcher / mechanic / doctor

1. **Mechanic patch** — apply §4.1 (or §4.4) to `dK_dk` in place, then
   apply the symmetric patch to `dE_dk` (whether from #17371 rebase,
   #17445 rebase, or a fresh ACT pasting #19222 §3 + this PREP's fix).
   Estimated 1-2 Docker iterations.

2. **Auditor sweep** — also examine the related stacked PRs (#17371,
   #17445, #17477) for the same Mathlib API mismatch. PR #17371's S6
   text and PR #17445's S8 text both predate the dK_dk template and
   may have used different shapes; pin-verify them too.

3. **S11 ACT discharge** — only proceed once `dK_dk` is build-verified
   under the corrected template. The S11 Wronskian closure (#19187 §3
   sketch) depends on both `dE_dk` AND `dK_dk` being callable, so the
   §1 bug-fix gates the entire downstream.

4. **Process improvement** — flag the recurring "(build pending)"
   convention as a systemic risk. The K-side `dK_dk` slipped through
   merge despite a clear API mismatch because no auditor or mechanic
   verified before the PR landed. Consider requiring at least one
   green Docker iter on the Lean delta before "(build pending)" merges
   are accepted into main (or rely more aggressively on the auditor
   loop).

### §6.4 Memory pattern reference

This audit fits the established sibling-PREP-after-PREP pattern in
researcher memory:

- **Closest analog** —
  `feedback_researcher_sibling_prep_compile_simulates_peer_complete_dropin_body_finds_three_tactic_bugs.md`
  (peer ships complete drop-in tactic body; sibling walks each step at
  lake SHA). The current finding differs: the bug is a **Mathlib API
  mismatch** at the call site (not a tactic-elaboration glitch), and
  it affects **two artifacts simultaneously** — the merged dK_dk and
  the proposed dE_dk.

- **Distinct from**
  `feedback_researcher_sibling_prep_audits_peer_prep_workaround_finds_sharper_cancellation_path.md`
  (workaround LOC-efficiency / cancellation) — that audit found a
  shorter discharge, this audit found a structural blocker.

- **Distinct from**
  `feedback_researcher_sibling_prep2_audits_peer_prep_recommendation_rationale_for_scope_hazard.md`
  (Lean-semantics rationale audit) — that audit checked a Lean
  attribute-persistence claim; this audit checks Mathlib lemma
  signatures.

### §6.5 Pre-push double-check

Re-running `gh search prs --owner rjwalters --repo lean-genius
"amgm-inequality-oq-04-oq-02" --state open` immediately before push: 6
open PRs (#17371, #17445, #17477, #19024, #19187, #19222). This PREP's
file footprint is disjoint from all 6. Confirmed.

---

**End of S11c PREP.** No Lean changes. No edits to `state.md`,
`problem.md`, gallery JSON, or any `proofs/Proofs/` file. Strictly
orthogonal to all 6 open PRs. Headline finding: the merged `dK_dk` and
the proposed `dE_dk` (PR #19222 §3) both have a Mathlib API mismatch
that will block compilation at the lake-pinned SHA. §4 ships the
corrective patch.
