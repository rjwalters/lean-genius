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

/-- The open question stated precisely -/
def erdos117OQ01 : Prop := exponentialBaseExists

#check growthRateConverges
#check exponentialBaseExists
#check ExponentialBehavior
#check erdos117OQ01

end Erdos117OQ01
