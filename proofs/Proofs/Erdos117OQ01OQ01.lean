/-
  Exponential Base Implies Exponential Behavior (OQ-01-OQ-01)

  Open Question OQ-01-OQ-01:
  Can `base_implies_behavior` from Erdos117OQ01.lean be proved rigorously?
  That is: if lim_{n→∞} log(h(n))/n = log c, does h(n) behave like cⁿ?

  **Answer**: YES (with a correction).

  The original `ExponentialBehavior c` definition in Erdos117OQ01 states:
    ∀ ε > 0, ∃ N, ∀ n ≥ N, (c - ε)ⁿ ≤ h(n) ≤ (c + ε)ⁿ.
  The lower bound (c - ε)ⁿ ≤ h(n) has a subtle issue for ε > c:
  when c - ε < 0 and n is even, (c - ε)ⁿ = (ε - c)ⁿ can grow faster than h(n),
  making the lower bound false for large ε. The comment in the parent file notes:
  "requires implicit ε small enough for the lower bound to make sense."

  **Corrected version**: Use ε ∈ (0, c) so that c - ε > 0 always.
  Then the proof goes through cleanly using exp/log monotonicity.

  **Proof strategy** (for ε ∈ (0, c)):
  1. δ := min(log(c+ε) - log c, log c - log(c-ε)) > 0
  2. By convergence: ∃ N₀, ∀ n ≥ N₀, |log(h n)/n - log c| < δ
  3. For n ≥ max(N₀, 1):
     Upper: log(h n)/n < log c + δ ≤ log(c+ε) → h n ≤ (c+ε)ⁿ
     Lower: log(h n)/n > log c - δ ≥ log(c-ε) → h n ≥ (c-ε)ⁿ
  Both follow from exp being monotone and Real.log_pow.

  **Status**: 0 sorries, 0 axioms beyond those of Erdos117OQ01.
  Main theorem `base_implies_behavior_correct` is fully proved.

  See Erdos117OQ01.lean for the parent (growth rate convergence via Fekete's lemma).
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic
import Proofs.Erdos117OQ01

open Real Filter Topology

namespace Erdos117OQ01OQ01

open Erdos117OQ01 (h h_pos pyber_bounds growthRate ExponentialBehavior)

/-! ## Helper Lemmas -/

/-- h(n) is positive as a real number for n ≥ 1. -/
private lemma h_pos_real (n : ℕ) (hn : 1 ≤ n) : (0 : ℝ) < (h n : ℝ) :=
  Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one (h_pos n hn))

/-- growthRate n = log(h n) / n for n ≥ 1. -/
private lemma growthRate_eq' (n : ℕ) (hn : 1 ≤ n) :
    growthRate n = Real.log (h n : ℝ) / n := by
  unfold growthRate
  rw [if_neg (by omega)]

/-! ## Corrected Exponential Behavior -/

/-- The correct statement of exponential behavior:
    for ε ∈ (0, c), the base c - ε is positive, making the lower bound meaningful. -/
def ExponentialBehaviorCorrect (c : ℝ) : Prop :=
  ∀ ε ∈ Set.Ioo 0 c, ∃ N : ℕ, ∀ n ≥ N,
    (c - ε) ^ n ≤ (h n : ℝ) ∧ (h n : ℝ) ≤ (c + ε) ^ n

/-! ## Main Theorem -/

/-- **Convergence Implies Exponential Behavior**:
    If lim log(h(n))/n = log c (c > 1), then for all ε ∈ (0, c),
    eventually (c - ε)ⁿ ≤ h(n) ≤ (c + ε)ⁿ.

    This is the corrected version of `Erdos117OQ01.base_implies_behavior`,
    restricting to ε ∈ (0, c) to ensure c - ε > 0. -/
theorem base_implies_behavior_correct (c : ℝ) (hc : c > 1)
    (hconv : Tendsto growthRate atTop (𝓝 (Real.log c))) :
    ExponentialBehaviorCorrect c := by
  intro ε ⟨hε_pos, hε_lt_c⟩
  -- Both c - ε > 0 and c + ε > 0
  have hcmε : 0 < c - ε := by linarith
  have hcpε : 0 < c + ε := by linarith
  -- The logarithmic gaps are positive
  have hδ₁ : 0 < Real.log (c + ε) - Real.log c :=
    sub_pos.mpr (Real.log_lt_log (by linarith) (by linarith))
  have hδ₂ : 0 < Real.log c - Real.log (c - ε) :=
    sub_pos.mpr (Real.log_lt_log hcmε (by linarith))
  -- δ = min of the two gaps
  set δ := min (Real.log (c + ε) - Real.log c) (Real.log c - Real.log (c - ε))
  have hδ_pos : 0 < δ := lt_min hδ₁ hδ₂
  -- By convergence: find N₀ with |growthRate n - log c| < δ for n ≥ N₀
  rw [Metric.tendsto_atTop] at hconv
  obtain ⟨N₀, hN₀⟩ := hconv δ hδ_pos
  -- For n ≥ max(N₀, 1), both bounds hold
  refine ⟨max N₀ 1, fun n hn => ?_⟩
  have hn_N₀ : N₀ ≤ n := le_of_max_le_left hn
  have hn_1 : 1 ≤ n := le_of_max_le_right hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hhn_pos : (0 : ℝ) < (h n : ℝ) := h_pos_real n hn_1
  -- Unpack the distance condition into the growth rate at n
  have hdist := hN₀ n hn_N₀
  rw [Real.dist_eq, growthRate_eq' n hn_1] at hdist
  -- The bounds on growthRate n
  have hgr_l : Real.log c - δ < Real.log ↑(h n) / ↑n := by
    linarith [(abs_lt.mp hdist).1]
  have hgr_u : Real.log ↑(h n) / ↑n < Real.log c + δ := by
    linarith [(abs_lt.mp hdist).2]
  -- Key: convert log inequalities to power inequalities via exp ∘ log
  -- Upper bound: h n ≤ (c + ε)^n
  have hlog_u : Real.log ↑(h n) ≤ n * Real.log (c + ε) := by
    have hlt : Real.log ↑(h n) / ↑n < Real.log (c + ε) := by
      linarith [min_le_left (Real.log (c + ε) - Real.log c)
                            (Real.log c - Real.log (c - ε))]
    have := (div_lt_iff₀ hn_pos).mp hlt
    linarith [mul_comm (Real.log (c + ε)) (n : ℝ)]
  -- Lower bound: (c - ε)^n ≤ h n
  have hlog_l : n * Real.log (c - ε) ≤ Real.log ↑(h n) := by
    have hge : Real.log (c - ε) ≤ Real.log ↑(h n) / ↑n := by
      linarith [min_le_right (Real.log (c + ε) - Real.log c)
                             (Real.log c - Real.log (c - ε))]
    have := (le_div_iff₀ hn_pos).mp hge
    linarith [mul_comm (Real.log (c - ε)) (n : ℝ)]
  -- Now convert via exp ∘ log
  have hpow_u : 0 < (c + ε) ^ n := by positivity
  have hpow_l : 0 < (c - ε) ^ n := by positivity
  constructor
  · -- (c - ε)^n ≤ h n
    rw [← Real.exp_log hhn_pos, ← Real.exp_log hpow_l, Real.log_pow]
    exact Real.exp_le_exp.mpr hlog_l
  · -- h n ≤ (c + ε)^n
    rw [← Real.exp_log hhn_pos, ← Real.exp_log hpow_u, Real.log_pow]
    exact Real.exp_le_exp.mpr hlog_u

/-! ## Connection to Original ExponentialBehavior -/

/-- The corrected version implies the original for small ε ∈ (0, c).

    For ε ≥ c, the original `ExponentialBehavior c` may fail: (c - ε)^n for even n
    equals (ε - c)^n which grows faster than h(n) ≈ cⁿ if ε > 2c. -/
theorem correct_implies_original_for_small_ε (c : ℝ) (hc : c > 1) :
    ExponentialBehaviorCorrect c →
    ∀ ε ∈ Set.Ioo 0 c, ∃ N : ℕ, ∀ n ≥ N,
      (c - ε) ^ n ≤ (h n : ℝ) ∧ (h n : ℝ) ≤ (c + ε) ^ n :=
  fun hB ε hε => hB ε hε

/-! ## Corollary: Submultiplicativity Implies Exponential Behavior -/

/-- Under submultiplicativity, h(n) grows exponentially at a single base. -/
theorem abelian_covering_exponential_if_submultiplicative
    (hsub : ∀ m n : ℕ, h (m + n) ≤ h m * h n) :
    ∃ c : ℝ, c > 0 ∧ ExponentialBehaviorCorrect c := by
  -- Fekete's lemma gives the limiting growth rate L
  obtain ⟨L, hL⟩ := Erdos117OQ01.submultiplicative_implies_convergence hsub
  -- Pyber's lower bound: growth rate ≥ log c₁ > 0 eventually
  obtain ⟨c₁, _, hc₁_gt_1, _, hbounds⟩ := pyber_bounds
  -- L ≥ log c₁ > 0 since the sequence is eventually ≥ log c₁
  have hL_pos : 0 < L := by
    have hev : ∀ᶠ n : ℕ in atTop, Real.log c₁ ≤ growthRate n := by
      apply Filter.eventually_atTop.mpr
      refine ⟨1, fun n hn => ?_⟩
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
      rw [growthRate_eq' n hn, le_div_iff₀ hn_pos]
      have hcpow : (c₁ : ℝ) ^ n ≤ (h n : ℝ) := by
        exact_mod_cast (hbounds n hn).1
      calc Real.log c₁ * ↑n = ↑n * Real.log c₁ := mul_comm _ _
        _ = Real.log (c₁ ^ n) := (Real.log_pow c₁ n).symm
        _ ≤ Real.log ↑(h n) := Real.log_le_log (by positivity) hcpow
    exact lt_of_lt_of_le (Real.log_pos hc₁_gt_1) (ge_of_tendsto hL hev)
  -- Use c = exp(L) > 1
  refine ⟨Real.exp L, Real.exp_pos L, ?_⟩
  have hexpL_gt_1 : 1 < Real.exp L := Real.one_lt_exp_iff.mpr hL_pos
  -- base_implies_behavior_correct wants the limit as log (exp L) = L
  exact base_implies_behavior_correct (Real.exp L) hexpL_gt_1 (by rwa [Real.log_exp])

end Erdos117OQ01OQ01
