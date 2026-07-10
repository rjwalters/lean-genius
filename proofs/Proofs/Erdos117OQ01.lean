/-
  Open Question: Exponential Growth Rate of h(n)

  Related to Erdős Problem #117 (Covering Groups by Abelian Subgroups).

  Pyber (1987) proved c₁ⁿ < h(n) < c₂ⁿ for constants c₂ > c₁ > 1.
  This gives log h(n) / n ∈ (log c₁, log c₂) for all n > 0.

  The open question: does lim_{n→∞} log h(n) / n exist?
  Equivalently: is h(n) = Θ(cⁿ) for a single constant c?

  If the limit exists, it determines the "base of exponential growth"
  of the abelian covering number.

  References:
  - Pyber (1987): exponential bounds on h(n)
  - Isaacs: earlier lower bound
  - https://erdosproblems.com/117

  Tags: group-theory, abelian-subgroups, covering-number, growth-rate
-/

import Mathlib

open Real Filter

namespace Erdos117OQ01

/-
## Part I: Setup from Erdős #117

We assume the existence of the abelian covering number h(n)
satisfying exponential bounds.
-/

/-- The abelian covering number h(n): minimum number of abelian subgroups
    needed to cover any group with the n-commuting property.
    Axiomatized as a function ℕ → ℕ. -/
axiom h : ℕ → ℕ

/-- h(n) ≥ 1 for all n ≥ 1 (need at least one subgroup) -/
axiom h_pos : ∀ n : ℕ, n ≥ 1 → h n ≥ 1

/-- Pyber's exponential bounds: c₁ⁿ ≤ h(n) ≤ c₂ⁿ for constants c₂ > c₁ > 1 -/
axiom pyber_bounds :
    ∃ c₁ c₂ : ℝ, 1 < c₁ ∧ c₁ < c₂ ∧
      ∀ n : ℕ, n ≥ 1 → c₁ ^ n ≤ (h n : ℝ) ∧ (h n : ℝ) ≤ c₂ ^ n

/-
## Part II: The Logarithmic Growth Rate

Define the normalized logarithmic growth rate: log(h(n)) / n.
The question is whether this sequence converges.
-/

/-- The normalized logarithmic growth rate -/
noncomputable def growthRate (n : ℕ) : ℝ :=
  if n = 0 then 0 else Real.log (h n : ℝ) / (n : ℝ)

/-- The growth rate is bounded below by log(c₁) -/
theorem growthRate_lower_bound :
    ∃ L : ℝ, L > 0 ∧ ∀ n : ℕ, n ≥ 1 → growthRate n ≥ L := by
  obtain ⟨c₁, c₂, hc1, _, hbounds⟩ := pyber_bounds
  refine ⟨Real.log c₁, Real.log_pos hc1, fun n hn => ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from by omega)
  unfold growthRate
  rw [if_neg (show n ≠ 0 from by omega), ge_iff_le, le_div_iff₀ hn']
  have hlog : Real.log (c₁ ^ n) ≤ Real.log (h n : ℝ) :=
    Real.log_le_log (by positivity) (hbounds n hn).1
  rw [Real.log_pow, mul_comm] at hlog
  exact hlog

/-- The growth rate is bounded above by log(c₂) -/
theorem growthRate_upper_bound :
    ∃ U : ℝ, ∀ n : ℕ, n ≥ 1 → growthRate n ≤ U := by
  obtain ⟨c₁, c₂, _, hc12, hbounds⟩ := pyber_bounds
  have hc2 : c₂ > 1 := lt_trans (by linarith : 1 < c₁) hc12
  refine ⟨Real.log c₂, fun n hn => ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from by omega)
  unfold growthRate
  rw [if_neg (show n ≠ 0 from by omega), div_le_iff₀ hn']
  have hhn : (1 : ℝ) ≤ (h n : ℝ) := by exact_mod_cast h_pos n hn
  have hlog : Real.log (h n : ℝ) ≤ Real.log (c₂ ^ n) :=
    Real.log_le_log (by linarith) (hbounds n hn).2
  rw [Real.log_pow, mul_comm] at hlog
  exact hlog

/-
## Part III: liminf and limsup

Even though the limit may not exist, the liminf and limsup
are well-defined and bounded.
-/

/-- The liminf of the growth rate sequence -/
noncomputable def growthRateLimInf : ℝ :=
  Filter.liminf (fun n => growthRate n) atTop

/-- The limsup of the growth rate sequence -/
noncomputable def growthRateLimSup : ℝ :=
  Filter.limsup (fun n => growthRate n) atTop

/-- The liminf is at least log(c₁) -/
theorem limInf_ge_log_c1 :
    ∃ c₁ : ℝ, c₁ > 1 ∧ growthRateLimInf ≥ Real.log c₁ := by
  obtain ⟨c₁, c₂, hc1, _, hbounds⟩ := pyber_bounds
  refine ⟨c₁, hc1, ?_⟩
  -- log c₁ ≤ growthRate n eventually
  have hev : ∀ᶠ n : ℕ in atTop, Real.log c₁ ≤ growthRate n := by
    apply Filter.eventually_atTop.mpr
    refine ⟨1, fun n hn => ?_⟩
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from by omega)
    unfold growthRate
    rw [if_neg (show n ≠ 0 from by omega), le_div_iff₀ hn_pos]
    have hlog : Real.log (c₁ ^ n) ≤ Real.log (h n : ℝ) :=
      Real.log_le_log (by positivity) (hbounds n hn).1
    rw [Real.log_pow, mul_comm] at hlog
    exact hlog
  -- growthRate is cobounded below (its upper bound U witnesses the cobound)
  have hcobdd : (atTop : Filter ℕ).IsCoboundedUnder (· ≥ ·) growthRate := by
    obtain ⟨U, hU⟩ := growthRate_upper_bound
    refine ⟨U, fun a ha => ?_⟩
    rw [Filter.eventually_map] at ha
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ha
    exact le_trans (hN (max N 1) (le_max_left _ _)) (hU (max N 1) (le_max_right _ _))
  unfold growthRateLimInf
  rw [ge_iff_le]
  exact Filter.le_liminf_of_le hcobdd hev

/-- The limsup is at most log(c₂): the symmetric companion of `limInf_ge_log_c1`,
    completing the two-sided bound `log c₁ ≤ liminf ≤ limsup ≤ log c₂` promised by
    Part III. Even without knowing the limit exists, both extreme cluster values of
    `log h(n)/n` are trapped inside Pyber's window. -/
theorem limSup_le_log_c2 :
    ∃ c₂ : ℝ, c₂ > 1 ∧ growthRateLimSup ≤ Real.log c₂ := by
  obtain ⟨c₁, c₂, hc1, hc12, hbounds⟩ := pyber_bounds
  have hc2 : c₂ > 1 := lt_trans hc1 hc12
  refine ⟨c₂, hc2, ?_⟩
  -- growthRate n ≤ log c₂ eventually
  have hev : ∀ᶠ n : ℕ in atTop, growthRate n ≤ Real.log c₂ := by
    apply Filter.eventually_atTop.mpr
    refine ⟨1, fun n hn => ?_⟩
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from by omega)
    unfold growthRate
    rw [if_neg (show n ≠ 0 from by omega), div_le_iff₀ hn_pos]
    have hhn : (1 : ℝ) ≤ (h n : ℝ) := by exact_mod_cast h_pos n hn
    have hlog : Real.log (h n : ℝ) ≤ Real.log (c₂ ^ n) :=
      Real.log_le_log (by linarith) (hbounds n hn).2
    rw [Real.log_pow, mul_comm] at hlog
    exact hlog
  -- growthRate is cobounded above (its lower bound L witnesses the cobound)
  have hcobdd : (atTop : Filter ℕ).IsCoboundedUnder (· ≤ ·) growthRate := by
    obtain ⟨L, _, hL⟩ := growthRate_lower_bound
    refine ⟨L, fun a ha => ?_⟩
    rw [Filter.eventually_map] at ha
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ha
    exact le_trans (hL (max N 1) (le_max_right _ _)) (hN (max N 1) (le_max_left _ _))
  unfold growthRateLimSup
  exact Filter.limsup_le_of_le hcobdd hev

/-- liminf ≤ limsup (always true for bounded sequences) -/
theorem limInf_le_limSup : growthRateLimInf ≤ growthRateLimSup := by
  unfold growthRateLimInf growthRateLimSup
  apply Filter.liminf_le_limsup
  · -- IsBoundedUnder (· ≤ ·): growthRate is eventually ≤ U
    obtain ⟨U, hU⟩ := growthRate_upper_bound
    exact ⟨U, Filter.eventually_atTop.mpr ⟨1, fun n hn => hU n hn⟩⟩
  · -- IsBoundedUnder (· ≥ ·): growthRate is eventually ≥ L
    obtain ⟨L, _, hL⟩ := growthRate_lower_bound
    exact ⟨L, Filter.eventually_atTop.mpr ⟨1, fun n hn => hL n hn⟩⟩

/-
## Part IV: The Open Question

Does the growth rate converge? I.e., does liminf = limsup?
-/

/-- The limit of the growth rate exists (if true) -/
def growthRateConverges : Prop :=
  ∃ L : ℝ, Filter.Tendsto growthRate atTop (nhds L)

/-- Equivalent: liminf = limsup -/
def limInfEqLimSup : Prop :=
  growthRateLimInf = growthRateLimSup

/-- The main open question: does h(n) have a well-defined exponential base? -/
def exponentialBaseExists : Prop :=
  ∃ c : ℝ, c > 1 ∧ Filter.Tendsto growthRate atTop (nhds (Real.log c))

/-- If the limit exists, it determines the exponential base -/
theorem limit_determines_base (L : ℝ) (hL : L > 0)
    (hconv : Filter.Tendsto growthRate atTop (nhds L)) :
    exponentialBaseExists := by
  refine ⟨Real.exp L, Real.one_lt_exp_iff.mpr hL, ?_⟩
  rwa [Real.log_exp]

/-- **The exponential base lies in Pyber's window.** If the growth rate converges to `L`,
    then `log c₁ ≤ L ≤ log c₂` for Pyber's constants — equivalently, the base `exp L`
    satisfies `c₁ ≤ exp L ≤ c₂`. So even though the *existence* of the limit is the open
    question, its *value* (should it exist) is already pinned to the interval Pyber
    established. Proof: pass the eventual two-sided bounds on `growthRate` through
    `ge_of_tendsto` / `le_of_tendsto`. -/
theorem convergent_limit_in_pyber_window (L : ℝ)
    (hconv : Filter.Tendsto growthRate atTop (nhds L)) :
    ∃ c₁ c₂ : ℝ, 1 < c₁ ∧ c₁ < c₂ ∧ Real.log c₁ ≤ L ∧ L ≤ Real.log c₂ := by
  obtain ⟨c₁, c₂, hc1, hc12, hbounds⟩ := pyber_bounds
  refine ⟨c₁, c₂, hc1, hc12, ?_, ?_⟩
  · -- log c₁ ≤ L, from the eventual lower bound log c₁ ≤ growthRate n
    have hev : ∀ᶠ n : ℕ in atTop, Real.log c₁ ≤ growthRate n := by
      apply Filter.eventually_atTop.mpr
      refine ⟨1, fun n hn => ?_⟩
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from by omega)
      unfold growthRate
      rw [if_neg (show n ≠ 0 from by omega), le_div_iff₀ hn_pos]
      have hlog : Real.log (c₁ ^ n) ≤ Real.log (h n : ℝ) :=
        Real.log_le_log (by positivity) (hbounds n hn).1
      rw [Real.log_pow, mul_comm] at hlog
      exact hlog
    exact ge_of_tendsto hconv hev
  · -- L ≤ log c₂, from the eventual upper bound growthRate n ≤ log c₂
    have hev : ∀ᶠ n : ℕ in atTop, growthRate n ≤ Real.log c₂ := by
      apply Filter.eventually_atTop.mpr
      refine ⟨1, fun n hn => ?_⟩
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from by omega)
      unfold growthRate
      rw [if_neg (show n ≠ 0 from by omega), div_le_iff₀ hn_pos]
      have hhn : (1 : ℝ) ≤ (h n : ℝ) := by exact_mod_cast h_pos n hn
      have hlog : Real.log (h n : ℝ) ≤ Real.log (c₂ ^ n) :=
        Real.log_le_log (by linarith) (hbounds n hn).2
      rw [Real.log_pow, mul_comm] at hlog
      exact hlog
    exact le_of_tendsto hconv hev

/-- **A convergent growth-rate limit is automatically positive.** If `growthRate n → L`,
    then `L > 0`. Combining `convergent_limit_in_pyber_window` (which pins `L ≥ log c₁`)
    with `c₁ > 1` (so `log c₁ > 0`) shows the limit inherits the strict positivity of the
    growth rate itself (`growthRate_pos`). Consequently the hypothesis `L > 0` in
    `limit_determines_base` is never a genuine restriction: any limit that exists already
    satisfies it, so the exponential base `exp L` is forced to exceed `1`. -/
theorem convergent_limit_pos (L : ℝ)
    (hconv : Filter.Tendsto growthRate atTop (nhds L)) : 0 < L := by
  obtain ⟨c₁, _, hc1, _, hL1, _⟩ := convergent_limit_in_pyber_window L hconv
  exact lt_of_lt_of_le (Real.log_pos hc1) hL1

/-- Convergence implies exponential behavior:
    for `ε ∈ (0, c)`, eventually `(c-ε)ⁿ ≤ h(n) ≤ (c+ε)ⁿ`.

    The restriction `ε < c` keeps the lower base `c - ε` strictly positive. This is
    not a cosmetic convenience: the unrestricted `∀ ε > 0` form is genuinely *false*.
    For `ε ≥ c` we have `c - ε ≤ 0`, and for even `n` the quantity `(c - ε)ⁿ = (ε - c)ⁿ`
    is positive and grows like `(ε - c)ⁿ`, which exceeds `h(n) ≤ c₂ⁿ` once `ε - c > c₂`.
    So `ε < c` is exactly the hypothesis under which the two-sided power bound is a theorem. -/
def ExponentialBehavior (c : ℝ) : Prop :=
  ∀ ε, 0 < ε → ε < c → ∃ N : ℕ, ∀ n ≥ N,
    (c - ε) ^ n ≤ (h n : ℝ) ∧ (h n : ℝ) ≤ (c + ε) ^ n

/-- If the exponential base is `c`, then `h(n)` has exponential behavior at `c`
    (for every `ε ∈ (0, c)`).

    Proof: turn the limit `log(h n)/n → log c` into two-sided bounds. With
    `δ = min (log(c+ε) − log c) (log c − log(c−ε)) > 0`, convergence puts
    `log(h n)/n` within `δ` of `log c` eventually, hence strictly between
    `log(c−ε)` and `log(c+ε)`. Multiplying by `n` and applying `Real.log_pow`
    gives `log((c−ε)ⁿ) ≤ log(h n) ≤ log((c+ε)ⁿ)`; `exp ∘ log` monotonicity then
    yields the power bounds. -/
theorem base_implies_behavior (c : ℝ) (hc : c > 1)
    (hconv : Filter.Tendsto growthRate atTop (nhds (Real.log c))) :
    ExponentialBehavior c := by
  intro ε hε hεc
  have hcmε : 0 < c - ε := by linarith
  have hcpε : 0 < c + ε := by linarith
  have hδ₁ : 0 < Real.log (c + ε) - Real.log c :=
    sub_pos.mpr (Real.log_lt_log (by linarith) (by linarith))
  have hδ₂ : 0 < Real.log c - Real.log (c - ε) :=
    sub_pos.mpr (Real.log_lt_log hcmε (by linarith))
  set δ := min (Real.log (c + ε) - Real.log c) (Real.log c - Real.log (c - ε)) with hδdef
  have hδ_pos : 0 < δ := lt_min hδ₁ hδ₂
  rw [Metric.tendsto_atTop] at hconv
  obtain ⟨N₀, hN₀⟩ := hconv δ hδ_pos
  refine ⟨max N₀ 1, fun n hn => ?_⟩
  have hn_N₀ : N₀ ≤ n := le_of_max_le_left hn
  have hn_1 : 1 ≤ n := le_of_max_le_right hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hhn_pos : (0 : ℝ) < (h n : ℝ) :=
    Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one (h_pos n hn_1))
  have hgr_eq : growthRate n = Real.log (h n : ℝ) / n := by
    unfold growthRate; rw [if_neg (by omega)]
  have hdist := hN₀ n hn_N₀
  rw [Real.dist_eq, hgr_eq] at hdist
  have hmin_u : δ ≤ Real.log (c + ε) - Real.log c := by rw [hδdef]; exact min_le_left _ _
  have hmin_l : δ ≤ Real.log c - Real.log (c - ε) := by rw [hδdef]; exact min_le_right _ _
  have hlog_u : Real.log (h n : ℝ) ≤ n * Real.log (c + ε) := by
    have hlt : Real.log (h n : ℝ) / n < Real.log (c + ε) := by
      linarith [(abs_lt.mp hdist).2]
    have := (div_lt_iff₀ hn_pos).mp hlt
    linarith [mul_comm (Real.log (c + ε)) (n : ℝ)]
  have hlog_l : n * Real.log (c - ε) ≤ Real.log (h n : ℝ) := by
    have hge : Real.log (c - ε) ≤ Real.log (h n : ℝ) / n := by
      linarith [(abs_lt.mp hdist).1]
    have := (le_div_iff₀ hn_pos).mp hge
    linarith [mul_comm (Real.log (c - ε)) (n : ℝ)]
  have hpow_u : 0 < (c + ε) ^ n := by positivity
  have hpow_l : 0 < (c - ε) ^ n := by positivity
  refine ⟨?_, ?_⟩
  · rw [← Real.exp_log hhn_pos, ← Real.exp_log hpow_l, Real.log_pow]
    exact Real.exp_le_exp.mpr hlog_l
  · rw [← Real.exp_log hhn_pos, ← Real.exp_log hpow_u, Real.log_pow]
    exact Real.exp_le_exp.mpr hlog_u

/-- **Converse of `base_implies_behavior`.** If `h(n)` has exponential behavior at base
    `c > 1`, then the growth rate `log(h n)/n` actually *converges* to `log c`.

    So `base_implies_behavior` is not a one-way street: exponential behavior at `c` is
    equivalent to convergence of the growth rate to `log c` (packaged as
    `exponential_behavior_iff_base` below). Proof: for each target radius `η`, continuity
    of `Real.log` at `c` supplies an `ε ∈ (0, c)` with `log(c±ε)` within `η` of `log c`;
    the behavior bounds `(c-ε)ⁿ ≤ h n ≤ (c+ε)ⁿ` then trap `growthRate n` inside
    `[log(c-ε), log(c+ε)] ⊆ (log c - η, log c + η)` eventually. -/
theorem behavior_implies_base (c : ℝ) (hc : c > 1)
    (hbehav : ExponentialBehavior c) :
    Filter.Tendsto growthRate atTop (nhds (Real.log c)) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  -- Continuity of log at c gives a radius d around c mapping into the η-ball around log c.
  have hcont : ContinuousAt Real.log c := Real.continuousAt_log (ne_of_gt (by linarith))
  obtain ⟨d, hd, hdlog⟩ := Metric.continuousAt_iff.mp hcont η hη
  -- Pick ε small: within d of c (so log c±ε is η-close to log c) and inside (0, c).
  set ε := min (d / 2) (c / 2) with hεdef
  have hε_pos : 0 < ε := lt_min (by linarith) (by linarith)
  have hε_lt_c : ε < c := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hcmε : 0 < c - ε := by linarith
  have hεd : ε < d := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨N, hN⟩ := hbehav ε hε_pos hε_lt_c
  -- The two log-neighbourhood facts, from continuity applied to c ± ε.
  have hdist_u : dist (Real.log (c + ε)) (Real.log c) < η :=
    hdlog (by rw [Real.dist_eq]; have : c + ε - c = ε := by ring
              rw [this, abs_of_pos hε_pos]; exact hεd)
  have hdist_l : dist (Real.log (c - ε)) (Real.log c) < η :=
    hdlog (by rw [Real.dist_eq]; have : c - ε - c = -ε := by ring
              rw [this, abs_neg, abs_of_pos hε_pos]; exact hεd)
  rw [Real.dist_eq] at hdist_u hdist_l
  have hu : Real.log (c + ε) < Real.log c + η := by linarith [(abs_lt.mp hdist_u).2]
  have hl : Real.log c - η < Real.log (c - ε) := by linarith [(abs_lt.mp hdist_l).1]
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn_N : N ≤ n := le_of_max_le_left hn
  have hn_1 : 1 ≤ n := le_of_max_le_right hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  obtain ⟨hlow, hupp⟩ := hN n hn_N
  -- Trap growthRate n between log(c-ε) and log(c+ε).
  have hgr_l : Real.log (c - ε) ≤ growthRate n := by
    unfold growthRate
    rw [if_neg (show n ≠ 0 from by omega), le_div_iff₀ hn_pos]
    have hlog := Real.log_le_log (by positivity) hlow
    rwa [Real.log_pow, mul_comm] at hlog
  have hgr_u : growthRate n ≤ Real.log (c + ε) := by
    unfold growthRate
    rw [if_neg (show n ≠ 0 from by omega), div_le_iff₀ hn_pos]
    have hhn : (1 : ℝ) ≤ (h n : ℝ) := by exact_mod_cast h_pos n hn_1
    have hlog := Real.log_le_log (by linarith) hupp
    rwa [Real.log_pow, mul_comm] at hlog
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith, by linarith⟩

/-- **Exponential behavior at `c` ⟺ growth rate converges to `log c`.** Combining
    `base_implies_behavior` with its converse `behavior_implies_base`, the two notions
    coincide: `h(n) = c^{n + o(n)}` in the two-sided sense of `ExponentialBehavior` exactly
    when `log(h n)/n → log c`. This turns the Part IV implication into a characterization. -/
theorem exponential_behavior_iff_base (c : ℝ) (hc : c > 1) :
    Filter.Tendsto growthRate atTop (nhds (Real.log c)) ↔ ExponentialBehavior c :=
  ⟨base_implies_behavior c hc, behavior_implies_base c hc⟩

/-- **The two open-question formulations coincide.** Part IV states the open problem in two
    apparently different ways — `growthRateConverges` (the growth rate has *some* limit) and
    `exponentialBaseExists` (there is a base `c > 1` with `growthRate → log c`). They are in
    fact equivalent. The reverse direction is immediate (a base gives convergence to `log c`);
    the forward direction is exactly where `convergent_limit_pos` does the work: any limit `L`
    is positive, so `limit_determines_base` upgrades it to the genuine base `exp L > 1`. Hence
    "the growth rate converges" and "`h(n)` has a well-defined exponential base" are one and the
    same open question, not two. -/
theorem exponentialBaseExists_iff_converges :
    exponentialBaseExists ↔ growthRateConverges := by
  constructor
  · rintro ⟨c, _, hconv⟩
    exact ⟨Real.log c, hconv⟩
  · rintro ⟨L, hconv⟩
    exact limit_determines_base L (convergent_limit_pos L hconv) hconv

/-
## Part V: Known Implications

What would the answer tell us?
-/

/-- If the growth rate converges, h is submultiplicative or supermultiplicative
    in some asymptotic sense. This is a structural constraint on covering numbers. -/
def AsymptoticallyMultiplicative : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ ε > 0, ∃ N : ℕ, ∀ m n : ℕ, m ≥ N → n ≥ N →
    (h (m + n) : ℝ) ≤ (1 + ε) * (h m : ℝ) * (c * (h n : ℝ))

/-- If h is submultiplicative (h(m+n) ≤ h(m)·h(n)),
    then Fekete's lemma gives convergence -/
theorem submultiplicative_implies_convergence
    (hsub : ∀ m n : ℕ, h (m + n) ≤ h m * h n) :
    growthRateConverges := by
  -- Use Mathlib4's Subadditive.tendsto_lim (Fekete's lemma) via Mathlib.Analysis.Subadditive
  let f : ℕ → ℝ := fun n => Real.log (h n : ℝ)
  -- Step 0: All h n > 0 (including h 0, derived from submultiplicativity + h_pos)
  have h_all_pos : ∀ n : ℕ, (0 : ℝ) < h n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · -- h 0 > 0: if h 0 = 0 then h(0+1) ≤ 0·h 1 = 0, contradicting h 1 ≥ 1
      have hineq := hsub 0 1
      simp only [zero_add] at hineq
      by_contra hc
      push_neg at hc
      have h0_eq : h 0 = 0 := Nat.le_zero.mp (by exact_mod_cast hc)
      rw [h0_eq, zero_mul] at hineq
      linarith [h_pos 1 le_rfl]
    · exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (h_pos n hn)
  -- Step 1: f = log h is subadditive (Fekete condition)
  have hf_sub : Subadditive f := fun m n => by
    show Real.log (h (m + n) : ℝ) ≤ Real.log (h m : ℝ) + Real.log (h n : ℝ)
    rw [← Real.log_mul (ne_of_gt (h_all_pos m)) (ne_of_gt (h_all_pos n))]
    exact Real.log_le_log (h_all_pos (m + n)) (by exact_mod_cast hsub m n)
  -- Step 2: f n / n is bounded below by 0 (h n ≥ 1 → log(h n) ≥ 0)
  have hbdd : BddBelow (Set.range fun n : ℕ => f n / n) := by
    refine ⟨0, ?_⟩
    rintro x ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp  -- f 0 / 0 = log(h 0) / 0 = 0 in Lean (div by zero = 0)
    · have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hpos
      have hhn : (1 : ℝ) ≤ h n := by exact_mod_cast h_pos n hpos
      exact div_nonneg (Real.log_nonneg hhn) hn_pos.le
  -- Step 3: Apply Fekete's lemma (Mathlib: Subadditive.tendsto_lim)
  -- Conclusion: growthRate n = f n / n for n ≥ 1, so both converge to same limit
  refine ⟨hf_sub.lim, ?_⟩
  apply (hf_sub.tendsto_lim hbdd).congr'
  apply Filter.eventually_atTop.mpr
  exact ⟨1, fun n hn => by
    -- f n / n = Real.log (h n) / n = growthRate n (for n ≥ 1, n ≠ 0)
    unfold growthRate
    rw [if_neg (show n ≠ 0 from by omega)]⟩

/-- The trivial case: h(1) = 1, so the growth rate starts at 0 -/
theorem growthRate_1 (h1 : h 1 = 1) : growthRate 1 = 0 := by
  unfold growthRate
  simp [h1, Real.log_one]

/-- **The growth rate is strictly positive.** For every `n ≥ 1` the normalized
log-growth `log h(n)/n` is `> 0`: the abelian covering number grows genuinely
exponentially, never sub-exponentially. Immediate from the Pyber lower bound
`growthRate n ≥ log c₁ > 0`. -/
theorem growthRate_pos (n : ℕ) (hn : n ≥ 1) : 0 < growthRate n := by
  obtain ⟨L, hL, hbound⟩ := growthRate_lower_bound
  exact lt_of_lt_of_le hL (hbound n hn)

/-- **The liminf is strictly positive.** The lowest cluster value of the growth-rate
sequence is bounded away from `0` by `log c₁ > 0`. Even if the sequence does not
converge, it cannot cluster at a sub-exponential rate — a structural constraint on
the (possibly non-existent) exponential base. From `limInf_ge_log_c1`. -/
theorem growthRateLimInf_pos : 0 < growthRateLimInf := by
  obtain ⟨c₁, hc1, hge⟩ := limInf_ge_log_c1
  exact lt_of_lt_of_le (Real.log_pos hc1) hge

/-- **The limsup is strictly positive.** The highest cluster value of the growth-rate
sequence is likewise bounded away from `0`: since `growthRateLimInf ≤ growthRateLimSup`
(`limInf_le_limSup`) and the liminf is already `> 0` (`growthRateLimInf_pos`), the
limsup is `> 0` a fortiori. The upper companion of `growthRateLimInf_pos`: whether or
not the exponential base exists, both cluster extremes sit strictly inside the positive
Pyber window, so `h(n)` grows at least exponentially in every asymptotic sense. -/
theorem growthRateLimSup_pos : 0 < growthRateLimSup :=
  lt_of_lt_of_le growthRateLimInf_pos limInf_le_limSup

/-- **Uniform two-sided Pyber window.** A single pair of constants `1 < c₁ < c₂`
traps every `growthRate n` (`n ≥ 1`) in the fixed band `[log c₁, log c₂]`. This
consolidates `growthRate_lower_bound` and `growthRate_upper_bound` — which produce
their constants independently — into one statement with *shared* constants, the
uniform band on which the liminf/limsup analysis of Part III rests. -/
theorem growthRate_window :
    ∃ c₁ c₂ : ℝ, 1 < c₁ ∧ c₁ < c₂ ∧
      ∀ n : ℕ, n ≥ 1 → Real.log c₁ ≤ growthRate n ∧ growthRate n ≤ Real.log c₂ := by
  obtain ⟨c₁, c₂, hc1, hc12, hbounds⟩ := pyber_bounds
  refine ⟨c₁, c₂, hc1, hc12, fun n hn => ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from by omega)
  unfold growthRate
  rw [if_neg (show n ≠ 0 from by omega)]
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hn']
    have hlog : Real.log (c₁ ^ n) ≤ Real.log (h n : ℝ) :=
      Real.log_le_log (by positivity) (hbounds n hn).1
    rw [Real.log_pow, mul_comm] at hlog
    exact hlog
  · rw [div_le_iff₀ hn']
    have hhn : (1 : ℝ) ≤ (h n : ℝ) := by exact_mod_cast h_pos n hn
    have hlog : Real.log (h n : ℝ) ≤ Real.log (c₂ ^ n) :=
      Real.log_le_log (by linarith) (hbounds n hn).2
    rw [Real.log_pow, mul_comm] at hlog
    exact hlog

/-- **Both cluster values sit inside a single Pyber window.** A shared pair of constants
    `1 < c₁ < c₂` traps `growthRateLimInf` and `growthRateLimSup` in the *same* band
    `[log c₁, log c₂]`. This is the cluster-value analogue of `growthRate_window`:
    `limInf_ge_log_c1` and `limSup_le_log_c2` each conjure their own constant from
    `pyber_bounds`, so Lean cannot see the two witnesses as equal. Consolidating them with
    shared constants is what makes the oscillation bound below possible. -/
theorem limInfLimSup_window :
    ∃ c₁ c₂ : ℝ, 1 < c₁ ∧ c₁ < c₂ ∧
      Real.log c₁ ≤ growthRateLimInf ∧ growthRateLimSup ≤ Real.log c₂ := by
  obtain ⟨c₁, c₂, hc1, hc12, hbounds⟩ := pyber_bounds
  have hc2 : c₂ > 1 := lt_trans hc1 hc12
  refine ⟨c₁, c₂, hc1, hc12, ?_, ?_⟩
  · -- log c₁ ≤ liminf, with the shared c₁
    have hev : ∀ᶠ n : ℕ in atTop, Real.log c₁ ≤ growthRate n := by
      apply Filter.eventually_atTop.mpr
      refine ⟨1, fun n hn => ?_⟩
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from by omega)
      unfold growthRate
      rw [if_neg (show n ≠ 0 from by omega), le_div_iff₀ hn_pos]
      have hlog : Real.log (c₁ ^ n) ≤ Real.log (h n : ℝ) :=
        Real.log_le_log (by positivity) (hbounds n hn).1
      rw [Real.log_pow, mul_comm] at hlog
      exact hlog
    have hcobdd : (atTop : Filter ℕ).IsCoboundedUnder (· ≥ ·) growthRate := by
      obtain ⟨U, hU⟩ := growthRate_upper_bound
      refine ⟨U, fun a ha => ?_⟩
      rw [Filter.eventually_map] at ha
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ha
      exact le_trans (hN (max N 1) (le_max_left _ _)) (hU (max N 1) (le_max_right _ _))
    unfold growthRateLimInf
    exact Filter.le_liminf_of_le hcobdd hev
  · -- limsup ≤ log c₂, with the shared c₂
    have hev : ∀ᶠ n : ℕ in atTop, growthRate n ≤ Real.log c₂ := by
      apply Filter.eventually_atTop.mpr
      refine ⟨1, fun n hn => ?_⟩
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from by omega)
      unfold growthRate
      rw [if_neg (show n ≠ 0 from by omega), div_le_iff₀ hn_pos]
      have hhn : (1 : ℝ) ≤ (h n : ℝ) := by exact_mod_cast h_pos n hn
      have hlog : Real.log (h n : ℝ) ≤ Real.log (c₂ ^ n) :=
        Real.log_le_log (by linarith) (hbounds n hn).2
      rw [Real.log_pow, mul_comm] at hlog
      exact hlog
    have hcobdd : (atTop : Filter ℕ).IsCoboundedUnder (· ≤ ·) growthRate := by
      obtain ⟨L, _, hL⟩ := growthRate_lower_bound
      refine ⟨L, fun a ha => ?_⟩
      rw [Filter.eventually_map] at ha
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ha
      exact le_trans (hL (max N 1) (le_max_right _ _)) (hN (max N 1) (le_max_left _ _))
    unfold growthRateLimSup
    exact Filter.limsup_le_of_le hcobdd hev

/-- **The growth-rate oscillation is bounded by the log-width of Pyber's window.**
    `growthRateLimSup − growthRateLimInf ≤ log c₂ − log c₁ = log (c₂ / c₁)`. The open
    question is precisely whether this gap is `0` (convergence ⟺ `liminf = limsup`), so
    this is a quantitative near-convergence statement: the growth rate's failure to
    converge is capped by the *fixed* multiplicative slack `c₂ / c₁` between Pyber's two
    constants, uniformly in `n`. Immediate from `limInfLimSup_window`. -/
theorem growthRate_oscillation_le_window :
    ∃ c₁ c₂ : ℝ, 1 < c₁ ∧ c₁ < c₂ ∧
      growthRateLimSup - growthRateLimInf ≤ Real.log c₂ - Real.log c₁ := by
  obtain ⟨c₁, c₂, hc1, hc12, hlo, hhi⟩ := limInfLimSup_window
  exact ⟨c₁, c₂, hc1, hc12, by linarith⟩

/-- The open question stated precisely -/
def erdos117OQ01 : Prop := exponentialBaseExists

#check growthRateConverges
#check exponentialBaseExists
#check ExponentialBehavior
#check erdos117OQ01

end Erdos117OQ01
