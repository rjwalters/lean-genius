import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Exponential
import Proofs.LHopitalOQ02

/-
# Logarithmic and Exponential Growth Limits via the ∞/∞ L'Hôpital Rule (OQ-02 leaf)

## What This Proves

The parent entry (`LHopitalOQ02`) establishes the ∞/∞ form of L'Hôpital's rule —
content that Mathlib does **not** provide (Mathlib's 26 L'Hôpital variants only
cover the 0/0 form). That entry, however, only states the abstract rule. This leaf
puts the rule to work, deriving three classic growth-comparison limits as direct
corollaries of `LHopitalInfty.lhopital_infty_atTop`:

1. `log_div_id_atTop`:        (log x) / x      → 0   as x → +∞   (logarithm grows slower than the identity)
2. `id_div_exp_atTop`:        x / eˣ           → 0   as x → +∞   (the identity grows slower than the exponential)
3. `id_add_log_div_id_atTop`: (x + log x) / x  → 1   as x → +∞   (the nonzero-limit case c = 1)

The first two are the c = 0 instances of the rule; the third exercises the
general c ≠ 0 statement, confirming that the parent theorem handles a genuinely
nonzero target limit and is not silently specialised to vanishing ratios.

## Proof Strategy

Each limit is an `∞/∞` indeterminate form `f / g` with `g → +∞`. We supply the
derivatives `f'`, `g'`, check `g' ≠ 0`, verify `g → atTop`, and compute the easy
limit of `f'/g'`; the parent rule then delivers the conclusion. Concretely:

| limit            | f         | g    | f'        | g'   | f'/g'      → |
|------------------|-----------|------|-----------|------|--------------|
| (log x)/x        | log       | id   | x⁻¹       | 1    | x⁻¹      → 0 |
| x/eˣ             | id        | exp  | 1         | eˣ   | (eˣ)⁻¹   → 0 |
| (x + log x)/x    | x + log x | id   | 1 + x⁻¹   | 1    | 1 + x⁻¹  → 1 |

The auxiliary `f'/g'` limits are themselves elementary (`tendsto_inv_atTop_zero`,
`Real.tendsto_exp_atTop`), so the whole derivation reduces the hard ∞/∞ behaviour
to a single application of the parent's rule.

## Status
- [x] (log x)/x → 0
- [x] x/eˣ → 0
- [x] (x + log x)/x → 1 (nonzero limit, general c form)

## Difficulty: Medium
The mathematical depth lives in the parent rule; here the work is assembling the
hypotheses (derivative lemmas, non-vanishing denominators, the auxiliary limits)
and discharging the routine `f'/g'` computations.
-/

namespace LHopitalOQ02Incomplete01

open Set Filter Topology Real

/-! ═══════════════════════════════════════════════════════════════════════════════
COROLLARY 1: (log x) / x → 0  —  the logarithm grows slower than the identity
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **(log x) / x → 0 as x → +∞.**

The classic statement that the natural logarithm is dominated by the identity,
obtained as the `c = 0` case of the ∞/∞ L'Hôpital rule with `f = log`, `g = id`,
`f' = x⁻¹`, `g' = 1`. The ratio `f'/g' = x⁻¹ → 0`, and `g = id → +∞`. -/
theorem log_div_id_atTop :
    Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
  have hff' : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt Real.log x⁻¹ x :=
    fun x hx => Real.hasDerivAt_log (ne_of_gt hx)
  have hgg' : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x : ℝ => x) (1 : ℝ) x :=
    fun x _ => hasDerivAt_id' x
  have hg' : ∀ x ∈ Ioi (0 : ℝ), (1 : ℝ) ≠ 0 := fun _ _ => one_ne_zero
  have hgTop : Tendsto (fun x : ℝ => x) atTop atTop := tendsto_id
  have hdiv : Tendsto (fun x : ℝ => x⁻¹ / 1) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero
  exact LHopitalInfty.lhopital_infty_atTop hff' hgg' hg' hgTop hdiv

/-! ═══════════════════════════════════════════════════════════════════════════════
COROLLARY 2: x / eˣ → 0  —  the identity grows slower than the exponential
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **x / eˣ → 0 as x → +∞.**

The exponential dominates every polynomial; here the degree-one case, as the
`c = 0` instance of the ∞/∞ rule with `f = id`, `g = exp`, `f' = 1`, `g' = eˣ`.
The ratio `f'/g' = (eˣ)⁻¹ → 0`, and `g = exp → +∞`. -/
theorem id_div_exp_atTop :
    Tendsto (fun x : ℝ => x / Real.exp x) atTop (𝓝 0) := by
  have hff' : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x : ℝ => x) (1 : ℝ) x :=
    fun x _ => hasDerivAt_id' x
  have hgg' : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt Real.exp (Real.exp x) x :=
    fun x _ => Real.hasDerivAt_exp x
  have hg' : ∀ x ∈ Ioi (0 : ℝ), Real.exp x ≠ 0 := fun x _ => (Real.exp_pos x).ne'
  have hgTop : Tendsto Real.exp atTop atTop := Real.tendsto_exp_atTop
  have hdiv : Tendsto (fun x : ℝ => (1 : ℝ) / Real.exp x) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp Real.tendsto_exp_atTop
  exact LHopitalInfty.lhopital_infty_atTop hff' hgg' hg' hgTop hdiv

/-! ═══════════════════════════════════════════════════════════════════════════════
COROLLARY 3: (x + log x) / x → 1  —  the nonzero-limit (c = 1) case
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **(x + log x) / x → 1 as x → +∞.**

A worked instance of the *general* `c ≠ 0` form of the rule, confirming the parent
theorem is not silently restricted to vanishing ratios. Here `f = x + log x`,
`g = id`, `f' = 1 + x⁻¹`, `g' = 1`, so `f'/g' = 1 + x⁻¹ → 1`, and `g → +∞`. -/
theorem id_add_log_div_id_atTop :
    Tendsto (fun x : ℝ => (x + Real.log x) / x) atTop (𝓝 1) := by
  have hff' : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (fun x : ℝ => x + Real.log x) (1 + x⁻¹) x :=
    fun x hx => (hasDerivAt_id' x).add (Real.hasDerivAt_log (ne_of_gt hx))
  have hgg' : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x : ℝ => x) (1 : ℝ) x :=
    fun x _ => hasDerivAt_id' x
  have hg' : ∀ x ∈ Ioi (0 : ℝ), (1 : ℝ) ≠ 0 := fun _ _ => one_ne_zero
  have hgTop : Tendsto (fun x : ℝ => x) atTop atTop := tendsto_id
  have hdiv : Tendsto (fun x : ℝ => (1 + x⁻¹) / 1) atTop (𝓝 1) := by
    have : Tendsto (fun x : ℝ => 1 + x⁻¹) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_inv_atTop_zero
    simpa using this
  exact LHopitalInfty.lhopital_infty_atTop hff' hgg' hg' hgTop hdiv

end LHopitalOQ02Incomplete01
