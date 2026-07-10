/-
# Shannon AWGN water-filling, oq-03-oq-01 — capacity monotonicity

Source: parallel-Gaussian-channel water-filling (see
`ShannonChannelCodingAWGNOQ03OQ01.lean`, namespace `ShannonWaterFilling`, which
proves optimality of `Pᵢ⋆ = (μ − Nᵢ)₊`, the closed-form optimum
`∑ᵢ ½ log(max μ Nᵢ / Nᵢ)`, and existence/uniqueness of the water level `μ`).

The companion `…EqualNoise.lean` records the equal-noise closed form and its
monotonicities.  This file supplies the *general* (arbitrary noise profile)
structural monotonicities of the water-filling capacity, all axiom-free /
sorry-free:

* `perUseCapacity_nonneg`   — a single AWGN sub-channel with `P ≥ 0`, `N > 0` has
  nonnegative rate `½ log(1 + P/N) ≥ 0`.
* `perUseCapacity_mono`     — the per-channel rate is monotone in the allotted
  power `P`.
* `waterAlloc_mono_level`   — the water-filling depth `(μ − Nᵢ)₊` is monotone in
  the water level `μ`.
* `rate_waterAlloc_nonneg`  — the water-filling rate is nonnegative.
* `rate_waterAlloc_mono_level` — the water-filling rate is monotone in the water
  level `μ` (raising the surface never lowers the achievable rate).
* `waterBudget_nonneg`      — the poured-in power is nonnegative.
* `waterLevel_pos`          — a positive budget forces a positive water level.
* `rate_waterAlloc_eq_zero_of_budget_zero` — a zero budget yields zero rate.
* `capacity_mono_budget`    — **the headline**: the constrained capacity
  `C(P) = R(waterAlloc μ N)` is monotone in the total power budget `P`; more
  power never decreases the optimal achievable rate.  Proved directly from
  optimality (`waterfilling_optimal`): the water-filling allocation for a smaller
  budget is a *feasible* allocation for the larger budget, so the larger budget's
  optimum dominates it.

Tags: information-theory, shannon, awgn, water-filling, capacity, monotonicity
-/

import Mathlib
import Proofs.ShannonChannelCodingAWGNOQ03OQ01

set_option linter.unusedSectionVars false

namespace ShannonWaterFilling

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-! ## Per-channel rate: nonnegativity and power-monotonicity -/

/-- **A single sub-channel has nonnegative rate.**  With nonnegative allotted
power `P` and positive noise `N`, the per-use AWGN capacity `½ log(1 + P/N)` is
nonnegative, since `1 + P/N ≥ 1`. -/
theorem perUseCapacity_nonneg {P N : ℝ} (hP : 0 ≤ P) (hN : 0 < N) :
    0 ≤ perUseCapacity P N := by
  unfold perUseCapacity
  apply mul_nonneg (by norm_num)
  apply Real.log_nonneg
  have : 0 ≤ P / N := div_nonneg hP hN.le
  linarith

/-- **Per-channel rate is monotone in power.**  For fixed positive noise `N`,
allocating more (nonnegative) power to a sub-channel never decreases its rate:
`P₁ ≤ P₂ ⟹ ½ log(1 + P₁/N) ≤ ½ log(1 + P₂/N)`. -/
theorem perUseCapacity_mono {N : ℝ} (hN : 0 < N) {P₁ P₂ : ℝ}
    (hP1 : 0 ≤ P₁) (hP : P₁ ≤ P₂) :
    perUseCapacity P₁ N ≤ perUseCapacity P₂ N := by
  unfold perUseCapacity
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.log_le_log
  · have : 0 ≤ P₁ / N := div_nonneg hP1 hN.le
    linarith
  · have hdiv : P₁ / N ≤ P₂ / N := by gcongr
    linarith

/-! ## Per-channel rate: strict positivity and its zero set -/

/-- **A single sub-channel with positive power has strictly positive rate.**  For
positive noise `N` and strictly positive allotted power `P`, the per-use AWGN
capacity `½ log(1 + P/N)` is strictly positive, since `1 + P/N > 1`.  This
sharpens `perUseCapacity_nonneg` and is the atomic building block behind the
sum-level `rate_waterAlloc_pos`. -/
theorem perUseCapacity_pos {P N : ℝ} (hP : 0 < P) (hN : 0 < N) :
    0 < perUseCapacity P N := by
  unfold perUseCapacity
  apply mul_pos (by norm_num)
  apply Real.log_pos
  have hpos : 0 < P / N := div_pos hP hN
  linarith

/-- **A single sub-channel's rate vanishes exactly at zero power.**  For positive
noise `N` and nonnegative power `P`, the per-use AWGN capacity is zero iff no power
is allotted: `½ log(1 + P/N) = 0 ↔ P = 0`.  This pins the zero set of the
per-channel rate, the atomic counterpart of the sum-level
`rate_waterAlloc_eq_zero_iff`. -/
theorem perUseCapacity_eq_zero_iff {P N : ℝ} (hP : 0 ≤ P) (hN : 0 < N) :
    perUseCapacity P N = 0 ↔ P = 0 := by
  constructor
  · intro h
    unfold perUseCapacity at h
    have hlog : Real.log (1 + P / N) = 0 := by
      rcases mul_eq_zero.1 h with h' | h'
      · exact absurd h' (by norm_num)
      · exact h'
    have hxpos : 0 < 1 + P / N := by
      have : 0 ≤ P / N := div_nonneg hP hN.le
      linarith
    have hx1 : 1 + P / N = 1 := by
      have hexp := Real.exp_log hxpos
      rw [hlog, Real.exp_zero] at hexp
      linarith
    have hpn : P / N = 0 := by linarith
    rcases div_eq_zero_iff.1 hpn with hP0 | hN0
    · exact hP0
    · exact absurd hN0 (ne_of_gt hN)
  · intro h
    subst h
    simp [perUseCapacity]

/-- **A single sub-channel has positive rate exactly when it is allotted positive
power.**  For positive noise `N` and nonnegative power `P`, `0 < perUseCapacity P N
↔ 0 < P`.  Combined with `perUseCapacity_nonneg` this fixes the per-channel
trichotomy: no power ⇒ no rate, any positive power ⇒ positive rate. -/
theorem perUseCapacity_pos_iff {P N : ℝ} (hP : 0 ≤ P) (hN : 0 < N) :
    0 < perUseCapacity P N ↔ 0 < P := by
  constructor
  · intro h
    rcases eq_or_lt_of_le hP with h0 | h0
    · rw [(perUseCapacity_eq_zero_iff hP hN).2 h0.symm] at h
      exact absurd h (lt_irrefl 0)
    · exact h0
  · intro h
    exact perUseCapacity_pos h hN

/-! ## Water-filling depth: monotonicity in the water level -/

/-- **The water-filling depth is monotone in the water level.**  Raising the
surface `μ₁ ≤ μ₂` never decreases any channel's depth `(μ − Nᵢ)₊`. -/
theorem waterAlloc_mono_level {μ₁ μ₂ : ℝ} (h : μ₁ ≤ μ₂) (N : ι → ℝ) (i : ι) :
    waterAlloc μ₁ N i ≤ waterAlloc μ₂ N i := by
  unfold waterAlloc
  exact max_le_max (by linarith) le_rfl

/-! ## Water-filling rate: nonnegativity and monotonicity in the water level -/

/-- **The water-filling rate is nonnegative.**  Summing nonnegative per-channel
rates, the total rate `R(waterAlloc μ N)` is `≥ 0`. -/
theorem rate_waterAlloc_nonneg (N : ι → ℝ) (hN : ∀ i, 0 < N i) (μ : ℝ) :
    0 ≤ parallelRate N (waterAlloc μ N) := by
  unfold parallelRate
  apply Finset.sum_nonneg
  intro i _
  exact perUseCapacity_nonneg (waterAlloc_nonneg μ N i) (hN i)

/-- **The water-filling rate is monotone in the water level.**  Raising the water
surface `μ₁ ≤ μ₂` never decreases the total achievable rate; each per-channel term
grows with its (monotone) depth. -/
theorem rate_waterAlloc_mono_level (N : ι → ℝ) (hN : ∀ i, 0 < N i)
    {μ₁ μ₂ : ℝ} (h : μ₁ ≤ μ₂) :
    parallelRate N (waterAlloc μ₁ N) ≤ parallelRate N (waterAlloc μ₂ N) := by
  unfold parallelRate
  apply Finset.sum_le_sum
  intro i _
  exact perUseCapacity_mono (hN i) (waterAlloc_nonneg μ₁ N i)
    (waterAlloc_mono_level h N i)

/-! ## Budget positivity ⇒ water-level positivity, and the zero-budget degeneracy -/

/-- The poured-in power `g(μ) = ∑ᵢ (μ − Nᵢ)₊` is nonnegative. -/
theorem waterBudget_nonneg (N : ι → ℝ) (μ : ℝ) : 0 ≤ waterBudget N μ := by
  unfold waterBudget
  exact Finset.sum_nonneg fun i _ => waterAlloc_nonneg μ N i

/-- **A positive budget forces a positive water level.**  If the water level `μ`
realises a strictly positive budget `P > 0` (with positive noise floors) then
`μ > 0`: at `μ ≤ 0` every channel is dry (`μ − Nᵢ < 0`) and the budget vanishes. -/
theorem waterLevel_pos (N : ι → ℝ) (hN : ∀ i, 0 < N i) {μ P : ℝ}
    (hbudget : waterBudget N μ = P) (hP : 0 < P) : 0 < μ := by
  by_contra hcon
  push_neg at hcon
  have hzero : waterBudget N μ = 0 := by
    unfold waterBudget waterAlloc
    apply Finset.sum_eq_zero
    intro i _
    exact max_eq_right (by linarith [hN i])
  rw [hbudget] at hzero
  linarith

/-- **A zero budget yields zero rate.**  When no power is poured in
(`g(μ) = 0`) every channel is switched off and the water-filling rate is `0`. -/
theorem rate_waterAlloc_eq_zero_of_budget_zero (N : ι → ℝ)
    {μ : ℝ} (h : waterBudget N μ = 0) :
    parallelRate N (waterAlloc μ N) = 0 := by
  have hsum : ∑ i, waterAlloc μ N i = 0 := h
  have hzero : ∀ i, waterAlloc μ N i = 0 := by
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => waterAlloc_nonneg μ N i)).1 hsum
    intro i; exact this i (Finset.mem_univ i)
  unfold parallelRate
  apply Finset.sum_eq_zero
  intro i _
  rw [hzero i]
  simp [perUseCapacity]

/-- **Strict positivity of the water-filling rate.**  As soon as a strictly
positive total power `P > 0` is poured in (with positive noise floors), the
water-filling rate is strictly positive: `0 < R(waterAlloc μ N)`.  Some channel is
necessarily active (`Pᵢ⋆ > 0`) — otherwise the whole budget `∑ᵢ Pᵢ⋆ = P` would
vanish — and that active channel contributes a strictly positive
`½ log(1 + Pᵢ⋆/Nᵢ)`, while every other term is nonnegative.  This sharpens
`rate_waterAlloc_nonneg` and is the general-noise counterpart of the equal-noise
`rate_equalNoise_pos`. -/
theorem rate_waterAlloc_pos (N : ι → ℝ) (hN : ∀ i, 0 < N i) {μ P : ℝ}
    (hbudget : waterBudget N μ = P) (hP : 0 < P) :
    0 < parallelRate N (waterAlloc μ N) := by
  -- some channel is active, else the whole budget `∑ᵢ Pᵢ⋆ = P` would vanish
  have hact : ∃ i, 0 < waterAlloc μ N i := by
    by_contra hcon
    push_neg at hcon
    have hle : waterBudget N μ ≤ 0 := by
      unfold waterBudget
      exact Finset.sum_nonpos fun i _ => hcon i
    rw [hbudget] at hle
    linarith
  obtain ⟨i₀, hi₀⟩ := hact
  unfold parallelRate
  refine Finset.sum_pos'
    (fun i _ => perUseCapacity_nonneg (waterAlloc_nonneg μ N i) (hN i))
    ⟨i₀, Finset.mem_univ i₀, ?_⟩
  -- the active channel `i₀` has strictly positive per-use capacity
  unfold perUseCapacity
  apply mul_pos (by norm_num)
  apply Real.log_pos
  have hpos : 0 < waterAlloc μ N i₀ / N i₀ := div_pos hi₀ (hN i₀)
  linarith

/-- **The water-filling rate vanishes exactly at zero budget.**  For positive noise
floors and a water level `μ` realising a budget `P ≥ 0`, the water-filling rate is
zero iff `P = 0`.  This pins down the capacity's zero set for an *arbitrary* noise
profile — the general-noise counterpart of `rate_equalNoise_eq_zero_iff` — by
combining `rate_waterAlloc_eq_zero_of_budget_zero` (⇐) with the contrapositive of
`rate_waterAlloc_pos` (⇒).  Together with `rate_waterAlloc_nonneg` it fixes the
dichotomy: no power ⇒ no rate, and any positive power ⇒ positive rate. -/
theorem rate_waterAlloc_eq_zero_iff (N : ι → ℝ) (hN : ∀ i, 0 < N i) {μ P : ℝ}
    (hbudget : waterBudget N μ = P) (hP : 0 ≤ P) :
    parallelRate N (waterAlloc μ N) = 0 ↔ P = 0 := by
  constructor
  · intro h
    by_contra hP0
    exact (rate_waterAlloc_pos N hN hbudget (lt_of_le_of_ne hP (Ne.symm hP0))).ne' h
  · intro h
    exact rate_waterAlloc_eq_zero_of_budget_zero N (hbudget.trans h)

/-! ## The headline: capacity is monotone in the power budget -/

/-- **Capacity is monotone in the total power budget.**  Let `μ₁` and `μ₂` be the
water levels realising budgets `P₁` and `P₂` respectively (`g(μⱼ) = Pⱼ`), with
positive noise floors and `P₁ ≤ P₂`.  Then the constrained parallel-channel
capacities satisfy

    R(waterAlloc μ₁ N) ≤ R(waterAlloc μ₂ N).

More total power never decreases the optimal achievable rate.  The proof is a
direct consequence of optimality: the water-filling allocation for the smaller
budget `P₁` is a *feasible* allocation for the larger budget `P₂` (its total power
is `P₁ ≤ P₂`), so the optimum at `P₂` dominates it (`waterfilling_optimal`). -/
theorem capacity_mono_budget (N : ι → ℝ) (hN : ∀ i, 0 < N i)
    {μ₁ μ₂ P₁ P₂ : ℝ}
    (h1 : waterBudget N μ₁ = P₁) (h2 : waterBudget N μ₂ = P₂) (hP : P₁ ≤ P₂) :
    parallelRate N (waterAlloc μ₁ N) ≤ parallelRate N (waterAlloc μ₂ N) := by
  have hP2nonneg : 0 ≤ P₂ := by rw [← h2]; exact waterBudget_nonneg N μ₂
  rcases eq_or_lt_of_le hP2nonneg with hP2z | hP2pos
  · -- degenerate: P₂ = 0 forces P₁ = 0, so both capacities are 0
    have hP2 : P₂ = 0 := hP2z.symm
    have hP1nonneg : 0 ≤ P₁ := by rw [← h1]; exact waterBudget_nonneg N μ₁
    have hP1 : P₁ = 0 := le_antisymm (hP2 ▸ hP) hP1nonneg
    rw [rate_waterAlloc_eq_zero_of_budget_zero N (h1.trans hP1),
        rate_waterAlloc_eq_zero_of_budget_zero N (h2.trans hP2)]
    -- both capacities are 0
    exact le_refl 0
  · -- generic: P₂ > 0, so μ₂ > 0 and optimality at P₂ dominates the P₁ allocation
    have hμ₂ : 0 < μ₂ := waterLevel_pos N hN h2 hP2pos
    have hxsum : ∑ i, waterAlloc μ₁ N i ≤ P₂ := by
      have hb : (∑ i, waterAlloc μ₁ N i) = P₁ := h1
      rw [hb]; exact hP
    exact waterfilling_optimal N hN hμ₂ h2 (waterAlloc μ₁ N)
      (fun i => waterAlloc_nonneg μ₁ N i) hxsum

/-! ## The water level itself is monotone in the power budget -/

/-- **The water level is monotone in the power budget.**  Let `μ₁` and `μ₂` be the
water levels realising budgets `P₁` and `P₂` (`g(μⱼ) = Pⱼ`), with `P₁ > 0` and
`P₁ ≤ P₂`.  Then `μ₁ ≤ μ₂`: pouring in more total power can only raise the water
surface.

This is the level-side dual of `capacity_mono_budget` (which shows the *capacity*
is monotone in the budget).  It follows immediately from strict monotonicity of
the budget function once a channel is active: if the surface dropped
(`μ₂ < μ₁`) while the (positive) budget at the lower level is `g(μ₂) = P₂ ≥ P₁ > 0`,
then `waterBudget_strictMono_of_pos` gives `P₂ = g(μ₂) < g(μ₁) = P₁`, contradicting
`P₁ ≤ P₂`.  The hypothesis `P₁ > 0` is essential: at budget `0` every channel is dry
and any `μ ≤ min Nᵢ` realises it, so the water level is not determined. -/
theorem waterLevel_mono_budget (N : ι → ℝ) {μ₁ μ₂ P₁ P₂ : ℝ}
    (h1 : waterBudget N μ₁ = P₁) (h2 : waterBudget N μ₂ = P₂)
    (hP1 : 0 < P₁) (hP : P₁ ≤ P₂) :
    μ₁ ≤ μ₂ := by
  by_contra hcon
  push_neg at hcon
  -- `μ₂ < μ₁`, and the budget at the lower level `μ₂` is `P₂ ≥ P₁ > 0`
  have hp2 : 0 < waterBudget N μ₂ := by rw [h2]; linarith
  have hlt := waterBudget_strictMono_of_pos N hcon hp2
  rw [h2, h1] at hlt
  -- `P₂ < P₁` contradicts `P₁ ≤ P₂`
  linarith

end ShannonWaterFilling
