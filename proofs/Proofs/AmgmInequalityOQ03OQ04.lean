/-
# Rényi Entropy and Power Mean Monotonicity

## Open Question: amgm-inequality-oq-03-oq-04

The weighted power mean M_r(z, w) = (Σ wᵢ · zᵢ^r)^(1/r) is increasing in r.
The Rényi entropy H_α(p) = (1/(1-α)) · log(Σ pᵢ^α) is decreasing in α.

These are not separate facts: **they are the same statement in different notation.**

When the probability distribution p serves as BOTH weights and values in the
power mean, we have the identity:

  H_α(p) = -log(M_{α-1}(p, p))

This shows H_α is decreasing iff M_r is increasing.

## What This File Proves

1. `renyiEntropy`: Definition of Rényi entropy H_α(p) for α ≠ 1
2. `selfPowerMean`: Power mean M_r(p,p) with distribution as both weights and values
3. `renyi_sum_eq_powerMean_sum`: Key algebraic identity Σ pᵢ·pᵢ^(α-1) = Σ pᵢ^α
4. `renyi_eq_neg_log_powerMean`: Main identity H_α(p) = -log(M_{α-1}(p,p))
5. `renyi_decreasing_of_powerMean_increasing`: H decreasing ← M increasing
6. `powerMean_increasing_of_renyi_decreasing`: M increasing ← H decreasing
7. `renyi_monotone_iff_powerMean_monotone`: Full biconditional equivalence

## Mathematical Proof of the Identity

For probability distribution p with pᵢ > 0:

  M_{α-1}(p,p) = (Σ pᵢ · pᵢ^(α-1))^(1/(α-1))
               = (Σ pᵢ^α)^(1/(α-1))           [since pᵢ · pᵢ^(α-1) = pᵢ^α]

  log(M_{α-1}(p,p)) = (1/(α-1)) · log(Σ pᵢ^α)

  -log(M_{α-1}(p,p)) = -(1/(α-1)) · log(Σ pᵢ^α)
                      = (1/(1-α)) · log(Σ pᵢ^α)  [since 1-α = -(α-1)]
                      = H_α(p)                    ✓

## References

- Rényi, A. (1961). On measures of entropy and information. 4th Berkeley Symp.
- Hardy, G.H., Littlewood, J.E., Pólya, G. (1934). Inequalities. Cambridge.
-/

import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

variable {ι : Type*} (s : Finset ι) (p : ι → ℝ)

namespace RenyiPowerMean

-- ============================================================
-- PART I: Definitions
-- ============================================================

/-- The **Rényi entropy** of order α for a distribution p on finset s:
    H_α(p) = (1/(1-α)) · log(Σ_{i∈s} pᵢ^α)

    Special limits (not covered here): α→1 gives Shannon entropy. -/
noncomputable def renyiEntropy (α : ℝ) (hα : α ≠ 1) : ℝ :=
  (1 / (1 - α)) * Real.log (∑ i ∈ s, p i ^ α)

/-- The **self-power mean** M_r(p,p): power mean with p as both weights and values:
    M_r(p,p) = (Σ_{i∈s} pᵢ · pᵢ^r)^(1/r) = (Σ pᵢ^(r+1))^(1/r) -/
noncomputable def selfPowerMean (r : ℝ) (hr : r ≠ 0) : ℝ :=
  (∑ i ∈ s, p i * p i ^ r) ^ (1 / r)

-- ============================================================
-- PART II: Key Algebraic Identity
-- ============================================================

/-- **pᵢ · pᵢ^(α-1) = pᵢ^α** for pᵢ > 0 (uses rpow_add). -/
private lemma mul_rpow_pred (α : ℝ) {x : ℝ} (hx : 0 < x) :
    x * x ^ (α - 1) = x ^ α := by
  have : x * x ^ (α - 1) = x ^ (1 : ℝ) * x ^ (α - 1) := by
    rw [Real.rpow_one]
  rw [this, ← Real.rpow_add hx.ne']
  norm_num

/-- **Core identity**: Σ pᵢ · pᵢ^(α-1) = Σ pᵢ^α when all pᵢ > 0.
    This is the algebraic bridge between the selfPowerMean and renyiEntropy sums. -/
theorem renyi_sum_eq_powerMean_sum
    (hp : ∀ i ∈ s, 0 < p i) (α : ℝ) :
    ∑ i ∈ s, p i * p i ^ (α - 1) = ∑ i ∈ s, p i ^ α :=
  Finset.sum_congr rfl (fun i hi => mul_rpow_pred α (hp i hi))

-- ============================================================
-- PART III: Positivity
-- ============================================================

/-- The Rényi sum Σ pᵢ^α is positive for positive distributions on nonempty s. -/
private lemma renyi_sum_pos
    (hp : ∀ i ∈ s, 0 < p i) (hs : s.Nonempty) (α : ℝ) :
    0 < ∑ i ∈ s, p i ^ α :=
  Finset.sum_pos (fun i hi => Real.rpow_pos_of_pos (hp i hi) α) hs

/-- The self-power mean is positive for positive distributions. -/
private lemma selfPowerMean_pos
    (hp : ∀ i ∈ s, 0 < p i) (hs : s.Nonempty) {r : ℝ} (hr : r ≠ 0) :
    0 < selfPowerMean s p r hr := by
  unfold selfPowerMean
  apply Real.rpow_pos_of_pos
  rw [renyi_sum_eq_powerMean_sum s p hp]
  exact renyi_sum_pos s p hp hs (r + 1)

-- ============================================================
-- PART IV: Main Identity H_α = -log(M_{α-1})
-- ============================================================

/-- **Main Identity**: H_α(p) = -log(M_{α-1}(p,p)).

This is the key connection between Rényi entropy and power means:
both measure the same "spread" of the distribution, just with different
sign conventions and base changes. -/
theorem renyi_eq_neg_log_powerMean
    (hp : ∀ i ∈ s, 0 < p i) (hs : s.Nonempty)
    (α : ℝ) (hα : α ≠ 1) :
    renyiEntropy s p α hα =
    -Real.log (selfPowerMean s p (α - 1) (sub_ne_zero.mpr hα)) := by
  unfold renyiEntropy selfPowerMean
  -- Step 1: Replace Σ pᵢ·pᵢ^(α-1) with Σ pᵢ^α using the algebraic identity
  rw [renyi_sum_eq_powerMean_sum s p hp]
  -- Step 2: Apply log(x^r) = r * log(x)
  have hpos : 0 < ∑ i ∈ s, p i ^ α := renyi_sum_pos s p hp hs α
  rw [Real.log_rpow hpos]
  -- Step 3: Simplify arithmetic: (1/(1-α)) * L = -((1/(α-1)) * L)
  have hα1 : α - 1 ≠ 0 := sub_ne_zero.mpr hα
  field_simp
  ring

-- ============================================================
-- PART V: Equivalence of Monotonicity
-- ============================================================

/-- **H decreasing ← M increasing**: If selfPowerMean is increasing in r,
    then renyiEntropy is decreasing in α.

    Proof: H_α = -log(M_{α-1}). For α ≤ β (so α-1 ≤ β-1):
    M_{α-1} ≤ M_{β-1} ⟹ log(M_{α-1}) ≤ log(M_{β-1}) ⟹ H_α ≥ H_β. -/
theorem renyi_decreasing_of_powerMean_increasing
    (hp : ∀ i ∈ s, 0 < p i) (hs : s.Nonempty)
    (hM : ∀ r t : ℝ, r ≤ t → (hr : r ≠ 0) → (ht : t ≠ 0) →
      selfPowerMean s p r hr ≤ selfPowerMean s p t ht)
    {α β : ℝ} (hαβ : α ≤ β) (hα : α ≠ 1) (hβ : β ≠ 1) :
    renyiEntropy s p β hβ ≤ renyiEntropy s p α hα := by
  rw [renyi_eq_neg_log_powerMean s p hp hs α hα,
      renyi_eq_neg_log_powerMean s p hp hs β hβ]
  apply neg_le_neg
  apply Real.log_le_log (selfPowerMean_pos s p hp hs (sub_ne_zero.mpr hα))
  exact hM _ _ (by linarith) _ _

/-- **M increasing ← H decreasing**: If renyiEntropy is decreasing in α,
    then selfPowerMean is increasing in r.

    Proof: M_r = exp(log(M_r)). Since H_{r+1} = -log(M_r), H decreasing
    means H_{t+1} ≤ H_{r+1}, i.e., -log(M_t) ≤ -log(M_r), so M_r ≤ M_t. -/
theorem powerMean_increasing_of_renyi_decreasing
    (hp : ∀ i ∈ s, 0 < p i) (hs : s.Nonempty)
    (hH : ∀ α β : ℝ, α ≤ β → (hα : α ≠ 1) → (hβ : β ≠ 1) →
      renyiEntropy s p β hβ ≤ renyiEntropy s p α hα)
    {r t : ℝ} (hrt : r ≤ t) (hr : r ≠ 0) (ht : t ≠ 0) :
    selfPowerMean s p r hr ≤ selfPowerMean s p t ht := by
  -- H_{t+1} ≤ H_{r+1} (Rényi decreasing, with r+1 ≤ t+1)
  have hr1 : r + 1 ≠ 1 := fun h => hr (by linarith)
  have ht1 : t + 1 ≠ 1 := fun h => ht (by linarith)
  have hH_step := hH (r + 1) (t + 1) (by linarith) hr1 ht1
  -- H_{r+1} = -log(M_r) and H_{t+1} = -log(M_t)
  rw [renyi_eq_neg_log_powerMean s p hp hs (r+1) hr1,
      renyi_eq_neg_log_powerMean s p hp hs (t+1) ht1] at hH_step
  simp only [add_sub_cancel_right] at hH_step
  -- hH_step : -log(M_t) ≤ -log(M_r), i.e., log(M_r) ≤ log(M_t)
  have hlog : Real.log (selfPowerMean s p r hr) ≤
              Real.log (selfPowerMean s p t ht) :=
    neg_le_neg_iff.mp hH_step
  -- Convert log inequality to base inequality using exp
  calc selfPowerMean s p r hr
      = Real.exp (Real.log (selfPowerMean s p r hr)) :=
        (Real.exp_log (selfPowerMean_pos s p hp hs hr)).symm
    _ ≤ Real.exp (Real.log (selfPowerMean s p t ht)) :=
        Real.exp_le_exp.mpr hlog
    _ = selfPowerMean s p t ht :=
        Real.exp_log (selfPowerMean_pos s p hp hs ht)

/-- **Biconditional Equivalence** (Main Theorem):
    The self-power mean M_r(p,p) is increasing in r
    if and only if the Rényi entropy H_α(p) is decreasing in α.

    This unifies two central monotonicity results in information theory and
    analysis, showing they are dual descriptions of the same phenomenon. -/
theorem renyi_monotone_iff_powerMean_monotone
    (hp : ∀ i ∈ s, 0 < p i) (hs : s.Nonempty) :
    (∀ α β : ℝ, α ≤ β → ∀ (hα : α ≠ 1) (hβ : β ≠ 1),
        renyiEntropy s p β hβ ≤ renyiEntropy s p α hα)
    ↔
    (∀ r t : ℝ, r ≤ t → ∀ (hr : r ≠ 0) (ht : t ≠ 0),
        selfPowerMean s p r hr ≤ selfPowerMean s p t ht) := by
  constructor
  · intro hH r t hrt hr ht
    exact powerMean_increasing_of_renyi_decreasing s p hp hs hH hrt hr ht
  · intro hM α β hαβ hα hβ
    exact renyi_decreasing_of_powerMean_increasing s p hp hs hM hαβ hα hβ

-- ============================================================
-- PART VI: Shannon Entropy as Limit (α → 1)
-- ============================================================

/-- The Rényi entropy at α = 2 has a simple form:
    H_2(p) = -log(Σ pᵢ²) = -log(collision probability). -/
theorem renyi_two_eq_neg_log_collision
    (hp : ∀ i ∈ s, 0 < p i) (hs : s.Nonempty) :
    renyiEntropy s p 2 (by norm_num) =
    -Real.log (∑ i ∈ s, p i ^ (2 : ℝ)) := by
  simp [renyiEntropy]
  have hpos : 0 < ∑ i ∈ s, p i ^ (2 : ℝ) :=
    renyi_sum_pos s p hp hs 2
  rw [Real.log_inv]
  ring

/-- Connection: H_2(p) = -log(M_1(p,p)) is the negative log of the arithmetic
    self-mean (since M_1 = Σ pᵢ · pᵢ = Σ pᵢ²). -/
theorem renyi_two_eq_neg_log_self_mean
    (hp : ∀ i ∈ s, 0 < p i) (hs : s.Nonempty) :
    renyiEntropy s p 2 (by norm_num) =
    -Real.log (selfPowerMean s p 1 (by norm_num)) := by
  exact renyi_eq_neg_log_powerMean s p hp hs 2 (by norm_num)

end RenyiPowerMean
