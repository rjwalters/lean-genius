/-
# Erdős Problem #1014: Ramsey Number Ratio Convergence

For fixed k ≥ 3, prove that R(k, l+1) / R(k, l) → 1 as l → ∞,
where R(k, l) is the Ramsey number.

## Key Results

- Open even for k = 3
- Best known bounds for R(3, l): between c₁ l² / log l and c₂ l² / log l
  (Bohman–Keevash, Shearer, Mattheus–Verstraëte)
- The conjecture would follow from precise enough asymptotics for R(k, l)

## References

- Erdős [Er71], p. 99
- Related: Problem 544 (R(3,k) behavior), Problem 1030 (diagonal)
- <https://erdosproblems.com/1014>
-/

import Mathlib

/- ## Core Definitions -/

/-- The Ramsey number R(k, l): minimum n such that every 2-coloring of
    edges of K_n contains a red K_k or a blue K_l. -/
axiom ramseyNumber (k l : ℕ) : ℕ

/-- Basic property: R(k, l) ≥ 1 for all k, l ≥ 1. -/
axiom ramsey_pos (k l : ℕ) (hk : k ≥ 1) (hl : l ≥ 1) :
  ramseyNumber k l ≥ 1

/-- Symmetry: R(k, l) = R(l, k). -/
axiom ramsey_symm (k l : ℕ) : ramseyNumber k l = ramseyNumber l k

/- ## Classical Bounds -/

/-- Erdős–Szekeres upper bound: R(k, l) ≤ C(k+l-2, k-1). -/
axiom ramsey_upper_erdos_szekeres (k l : ℕ) (hk : k ≥ 2) (hl : l ≥ 2) :
  (ramseyNumber k l : ℝ) ≤ (Nat.choose (k + l - 2) (k - 1) : ℝ)

/-- Monotonicity: R(k, l) ≤ R(k, l+1). -/
axiom ramsey_monotone_right (k l : ℕ) :
  ramseyNumber k l ≤ ramseyNumber k (l + 1)

/-- R(k, l+1) ≤ R(k, l) + R(k-1, l+1) (recurrence). -/
axiom ramsey_recurrence (k l : ℕ) (hk : k ≥ 2) (hl : l ≥ 1) :
  ramseyNumber k (l + 1) ≤ ramseyNumber k l + ramseyNumber (k - 1) (l + 1)

/- ## R(3, l) Bounds -/

/-- Shearer (1983) / Kim (1995): R(3, l) ≥ c · l² / log l. -/
axiom R3_lower (c : ℝ) (hc : c > 0) :
  ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
    (ramseyNumber 3 l : ℝ) ≥ c * (l : ℝ) ^ 2 / Real.log l

/-- Ajtai–Komlós–Szemerédi (1980): R(3, l) ≤ C · l² / log l. -/
axiom R3_upper :
  ∃ C : ℝ, C > 0 ∧ ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
    (ramseyNumber 3 l : ℝ) ≤ C * (l : ℝ) ^ 2 / Real.log l

/- ## Main Conjecture -/

/-- **Erdős Problem #1014** (OPEN): For fixed k ≥ 3,
    R(k, l+1) / R(k, l) → 1 as l → ∞. -/
axiom erdos_1014_conjecture (k : ℕ) (hk : k ≥ 3) :
  ∀ ε : ℝ, ε > 0 → ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
    |(ramseyNumber k (l + 1) : ℝ) / (ramseyNumber k l : ℝ) - 1| < ε

/- ## Growth Ratio Convergence Helpers -/

section GrowthRatioHelpers

open Real Filter Topology

/-- For any fixed a : ℕ, ((n+1)/n)^a → 1 as n → ∞.
    Proof: n⁻¹ → 0, so 1 + n⁻¹ → 1, so (1 + n⁻¹)^a → 1^a = 1. -/
private lemma tendsto_succ_div_pow (a : ℕ) :
    Tendsto (fun n : ℕ => (((n : ℝ) + 1) / (n : ℝ)) ^ a) atTop (nhds 1) := by
  conv_rhs => rw [show (1 : ℝ) = 1 ^ a from (one_pow a).symm]
  apply Tendsto.pow
  have h : Tendsto (fun n : ℕ => 1 + (n : ℝ)⁻¹) atTop (nhds (1 + 0)) :=
    tendsto_const_nhds.add (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  rw [add_zero] at h
  exact h.congr (eventually_atTop.mpr ⟨1, fun n hn => by
    have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega); field_simp⟩)

/-- For any fixed b : ℕ, (log n / log(n+1))^b → 1 as n → ∞.
    Uses squeeze: for n ≥ 2, 1 - 1/(n·log 2) ≤ log n/log(n+1) ≤ 1, and both → 1. -/
private lemma tendsto_log_ratio_pow (b : ℕ) :
    Tendsto (fun n : ℕ => (log (n : ℝ) / log ((n : ℝ) + 1)) ^ b) atTop (nhds 1) := by
  conv_rhs => rw [show (1 : ℝ) = 1 ^ b from (one_pow b).symm]
  apply Tendsto.pow
  -- Squeeze: 1 - (n⁻¹/log 2) ≤ log(n)/log(n+1) ≤ 1, both bounds → 1
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    -- Lower bound → 1
    (show Tendsto (fun n : ℕ => 1 - (n : ℝ)⁻¹ / log 2) atTop (nhds 1) from by
      rw [show (1 : ℝ) = 1 - 0 / log 2 from by simp]
      exact tendsto_const_nhds.sub
        ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).div_const _))
    -- Upper bound → 1
    tendsto_const_nhds
    -- f(n) ≥ lower bound eventually
    (eventually_atTop.mpr ⟨2, fun n hn => by
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hlog2 : (0 : ℝ) < log 2 := log_pos (by norm_num)
      have hlog_n1 : (0 : ℝ) < log ((n : ℝ) + 1) :=
        log_pos (by exact_mod_cast (show 1 < n + 1 by omega))
      have hlog2_le : log 2 ≤ log ((n : ℝ) + 1) :=
        log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ n + 1 by omega))
      -- log(n)/log(n+1) = 1 - (log(n+1)-log(n))/log(n+1)
      have h_eq : log (n : ℝ) / log ((n : ℝ) + 1) =
          1 - (log ((n : ℝ) + 1) - log (n : ℝ)) / log ((n : ℝ) + 1) := by
        rw [sub_div, div_self (ne_of_gt hlog_n1)]; ring
      -- log(n+1) - log(n) = log(1 + 1/n) ≤ 1/n
      have h_log_diff : log ((n : ℝ) + 1) - log (n : ℝ) ≤ (n : ℝ)⁻¹ := by
        rw [← log_div (by positivity) (ne_of_gt hn_pos)]
        have : ((n : ℝ) + 1) / (n : ℝ) = 1 + (n : ℝ)⁻¹ := by field_simp
        rw [this]
        linarith [log_le_sub_one_of_pos (show (0 : ℝ) < 1 + (n : ℝ)⁻¹ from by positivity)]
      -- Combine: diff/log(n+1) ≤ n⁻¹/log(2)
      have h_frac : (log ((n : ℝ) + 1) - log (n : ℝ)) / log ((n : ℝ) + 1) ≤
          (n : ℝ)⁻¹ / log 2 := by
        rw [div_le_div_iff hlog_n1 hlog2]
        calc (log ((n : ℝ) + 1) - log (n : ℝ)) * log 2
            ≤ (n : ℝ)⁻¹ * log 2 := by nlinarith [h_log_diff]
          _ ≤ (n : ℝ)⁻¹ * log ((n : ℝ) + 1) := by nlinarith [hlog2_le]
      rw [h_eq]; linarith⟩)
    -- f(n) ≤ 1 eventually (log is increasing)
    (eventually_atTop.mpr ⟨2, fun n hn => by
      exact div_le_one_of_le
        (log_le_log (by exact_mod_cast (show 0 < n by omega))
          (by exact_mod_cast (show n ≤ n + 1 by omega)))
        (le_of_lt (log_pos (by exact_mod_cast (show 1 < n + 1 by omega))))⟩)

/-- The growth ratio of c·l^a/(log l)^b tends to 1:
    ((l+1)/l)^a · (log l/log(l+1))^b → 1 as l → ∞. -/
private lemma growth_ratio_close (a b : ℕ) (δ : ℝ) (hδ : δ > 0) :
    ∃ L : ℕ, ∀ l : ℕ, l > L →
      |(((l : ℝ) + 1) / (l : ℝ)) ^ a *
       (log (l : ℝ) / log ((l : ℝ) + 1)) ^ b - 1| < δ := by
  have ht : Tendsto (fun n : ℕ =>
      (((n : ℝ) + 1) / (n : ℝ)) ^ a *
      (log (n : ℝ) / log ((n : ℝ) + 1)) ^ b) atTop (nhds 1) := by
    rw [show (1 : ℝ) = 1 * 1 from (mul_one 1).symm]
    exact (tendsto_succ_div_pow a).mul (tendsto_log_ratio_pow b)
  rw [Metric.tendsto_atTop] at ht
  obtain ⟨N, hN⟩ := ht δ hδ
  exact ⟨N, fun l hl => by rwa [Real.dist_eq] at hN l (by omega)⟩

end GrowthRatioHelpers

/- ## Consequences and Implications -/

/-- If R(k, l) ~ c_k · l^(k-1) / (log l)^(k-2) (conjectured asymptotics),
    then R(k, l+1)/R(k, l) → 1. Proved from the growth ratio convergence:
    decompose R(l+1)/R(l) = (R(l+1)/g(l+1))·(g(l+1)/g(l))·(g(l)/R(l)) where
    each factor is close to 1. -/
theorem ratio_from_asymptotics (k : ℕ) (hk : k ≥ 3) :
  (∀ ε : ℝ, ε > 0 → ∃ c : ℝ, c > 0 ∧ ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
    |(ramseyNumber k l : ℝ) / (c * (l : ℝ) ^ (k - 1) / (Real.log l) ^ (k - 2)) - 1| < ε) →
  ∀ ε : ℝ, ε > 0 → ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
    |(ramseyNumber k (l + 1) : ℝ) / (ramseyNumber k l : ℝ) - 1| < ε := by
  intro h_asymp ε hε
  -- Choose δ = min(ε/6, 1/4) for the sandwich
  set δ := min (ε / 6) (1 / 4) with hδ_def
  have hδ : δ > 0 := by positivity
  have hδ14 : δ ≤ 1 / 4 := min_le_right _ _
  have hδε6 : δ ≤ ε / 6 := min_le_left _ _
  -- Get asymptotic constant and threshold
  obtain ⟨c, hc, L₁, hL₁⟩ := h_asymp δ hδ
  -- Get growth ratio threshold
  obtain ⟨L₂, hL₂⟩ := growth_ratio_close (k - 1) (k - 2) δ hδ
  -- Take L large enough for all bounds
  use max (max L₁ L₂) 2
  intro l hl
  have hl1 : l > L₁ := by omega
  have hl2 : l > L₂ := by omega
  -- Positivity setup
  have hl_pos : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (show 0 < l by omega)
  have hl1_pos : (0 : ℝ) < (l : ℝ) + 1 := by linarith
  have hlog_l : 0 < Real.log (l : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < l by omega))
  have hlog_l1 : 0 < Real.log ((l : ℝ) + 1) := Real.log_pos (by linarith)
  -- Define g(l) and g(l+1)
  set g := c * (l : ℝ) ^ (k - 1) / (Real.log (l : ℝ)) ^ (k - 2)
  set g' := c * ((l : ℝ) + 1) ^ (k - 1) / (Real.log ((l : ℝ) + 1)) ^ (k - 2)
  have hg_pos : 0 < g := div_pos (mul_pos hc (pow_pos hl_pos _)) (pow_pos hlog_l _)
  have hg'_pos : 0 < g' := div_pos (mul_pos hc (pow_pos hl1_pos _)) (pow_pos hlog_l1 _)
  -- Three key bounds
  have hα : |(ramseyNumber k (l + 1) : ℝ) / g' - 1| < δ := by
    convert hL₁ (l + 1) (by omega) using 2; push_cast; ring
  have hβ : |g' / g - 1| < δ := by
    convert hL₂ l hl2 using 2
    simp only [g, g']; field_simp; ring
  have hζ : |(ramseyNumber k l : ℝ) / g - 1| < δ := hL₁ l hl1
  -- R(k,l) > 0 from sandwich
  set R := (ramseyNumber k l : ℝ)
  set R' := (ramseyNumber k (l + 1) : ℝ)
  have hRg_lb : R / g > 1 - δ := by linarith [(abs_lt.mp hζ).1]
  have hRg_ub : R / g < 1 + δ := by linarith [(abs_lt.mp hζ).2]
  have hR_pos : 0 < R := by
    by_contra h
    push_neg at h
    have : R / g ≤ 0 := div_nonpos_of_nonpos_of_nonneg h (le_of_lt hg_pos)
    linarith
  -- R'/R = (R'/g') · (g'/g) · (g/R)
  have h_decomp : R' / R = (R' / g') * (g' / g) * (g / R) := by
    field_simp
  -- Set α = R'/g', β = g'/g, γ = g/R
  set α := R' / g'
  set β := g' / g
  set γ := g / R
  -- αβγ - 1 = αβ(γ-1) + α(β-1) + (α-1)
  have h_expand : α * β * γ - 1 = α * β * (γ - 1) + α * (β - 1) + (α - 1) := by ring
  -- Factor bounds
  have hα_abs : |α| ≤ 1 + δ := by
    calc |α| = |α - 1 + 1| := by ring_nf
      _ ≤ |α - 1| + |1| := abs_add _ _
      _ ≤ δ + 1 := by linarith [le_of_lt hα, abs_of_pos (show (0:ℝ) < 1 by norm_num)]
      _ = 1 + δ := by ring
  have hβ_abs : |β| ≤ 1 + δ := by
    calc |β| = |β - 1 + 1| := by ring_nf
      _ ≤ |β - 1| + 1 := by linarith [abs_add (β - 1) 1, abs_of_pos (show (0:ℝ) < 1 by norm_num)]
      _ ≤ δ + 1 := by linarith [le_of_lt hβ]
      _ = 1 + δ := by ring
  have hγ_abs : |γ - 1| ≤ 4 * δ / 3 := by
    -- γ = g/R = 1/(R/g), |1/x - 1| = |x-1|/x when x > 0
    have hRg_pos : 0 < R / g := by linarith
    have hγ_eq : γ - 1 = -(R / g - 1) / (R / g) := by
      simp only [γ]; field_simp
    rw [hγ_eq, abs_div, abs_neg, abs_of_pos hRg_pos]
    -- Need: |R/g-1| / (R/g) ≤ 4δ/3, i.e., |R/g-1| ≤ (4δ/3)·(R/g)
    rw [div_le_iff hRg_pos]
    -- (4δ/3)·(R/g) ≥ (4δ/3)·(3/4) = δ ≥ |R/g-1|
    nlinarith [le_of_lt hζ, hRg_lb, hδ14, hδ]
  -- Final bound: |αβγ - 1| ≤ |α||β||γ-1| + |α||β-1| + |α-1| < 13δ/3 < ε
  rw [h_decomp, h_expand]
  calc |α * β * (γ - 1) + α * (β - 1) + (α - 1)|
      ≤ |α * β * (γ - 1)| + |α * (β - 1)| + |α - 1| := by
        linarith [abs_add (α * β * (γ - 1) + α * (β - 1)) (α - 1),
                  abs_add (α * β * (γ - 1)) (α * (β - 1))]
    _ = |α| * |β| * |γ - 1| + |α| * |β - 1| + |α - 1| := by
        rw [abs_mul, abs_mul, abs_mul]
    _ ≤ (1 + δ) * (1 + δ) * (4 * δ / 3) + (1 + δ) * δ + δ := by
        have := abs_nonneg α; have := abs_nonneg β; have := abs_nonneg (γ - 1)
        have := abs_nonneg (β - 1); have := abs_nonneg (α - 1)
        nlinarith [hα_abs, hβ_abs, hγ_abs, le_of_lt hα, le_of_lt hβ]
    _ ≤ (5/4) * (5/4) * (4 * δ / 3) + (5/4) * δ + δ := by nlinarith
    _ = 52 * δ / 12 := by ring
    _ = 13 * δ / 3 := by ring
    _ ≤ 13 * (ε / 6) / 3 := by nlinarith
    _ = 13 * ε / 18 := by ring
    _ < ε := by nlinarith

/-- The conjecture is equivalent to: R(k, l+1) - R(k, l) = o(R(k, l)).
Proved from monotonicity (R(k,l+1) ≥ R(k,l)) and positivity (R(k,l) ≥ 1):
|x/y - 1| = (x - y)/y when x ≥ y > 0. -/
theorem ratio_equiv_difference (k : ℕ) (hk : k ≥ 3) :
  (∀ ε : ℝ, ε > 0 → ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
    |(ramseyNumber k (l + 1) : ℝ) / (ramseyNumber k l : ℝ) - 1| < ε) ↔
  (∀ ε : ℝ, ε > 0 → ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
    ((ramseyNumber k (l + 1) : ℝ) - (ramseyNumber k l : ℝ)) /
    (ramseyNumber k l : ℝ) < ε) := by
  -- Key facts: R(k,l) ≥ 1 > 0 for l ≥ 1, and R(k,l+1) ≥ R(k,l)
  have abs_eq : ∀ l : ℕ, l ≥ 1 →
      |(ramseyNumber k (l + 1) : ℝ) / (ramseyNumber k l : ℝ) - 1| =
      ((ramseyNumber k (l + 1) : ℝ) - (ramseyNumber k l : ℝ)) /
      (ramseyNumber k l : ℝ) := by
    intro l hl
    set a := (ramseyNumber k (l + 1) : ℝ) with ha_def
    set b := (ramseyNumber k l : ℝ) with hb_def
    have hb_pos : b ≥ 1 := by simp [hb_def]; exact_mod_cast ramsey_pos k l (by omega) hl
    have hb_ne : b ≠ 0 := by linarith
    have hab : b ≤ a := by simp [ha_def, hb_def]; exact_mod_cast ramsey_monotone_right k l
    have h_eq : a / b - 1 = (a - b) / b := by
      rw [eq_comm, sub_div, div_self hb_ne]
    have h_nn : 0 ≤ a / b - 1 := by
      rw [h_eq]; exact div_nonneg (by linarith) (by linarith)
    rw [abs_of_nonneg h_nn]
    exact h_eq
  constructor
  · intro h ε hε
    obtain ⟨L₀, hL⟩ := h ε hε
    exact ⟨L₀, fun l hl => by rw [← abs_eq l (by omega)]; exact hL l hl⟩
  · intro h ε hε
    obtain ⟨L₀, hL⟩ := h ε hε
    exact ⟨L₀, fun l hl => by rw [abs_eq l (by omega)]; exact hL l hl⟩

/- ## Special Cases -/

/-- For k = 2: R(2, l) = l, so R(2, l+1)/R(2, l) = (l+1)/l → 1.
    This is trivial (k = 2 case). -/
axiom ramsey_k2 (l : ℕ) (hl : l ≥ 1) : ramseyNumber 2 l = l

/-- Known small values: R(3,3) = 6, R(3,4) = 9, R(3,5) = 14. -/
axiom R33 : ramseyNumber 3 3 = 6
axiom R34 : ramseyNumber 3 4 = 9
axiom R35 : ramseyNumber 3 5 = 14

/-- For the diagonal case k = l, Erdős–Szekeres gives R(k,k) ≤ C(2k-2,k-1).
    Proved from ramsey_upper_erdos_szekeres with l = k. -/
theorem diagonal_ramsey_upper (k : ℕ) (hk : k ≥ 2) :
    ramseyNumber k k ≤ Nat.choose (2 * k - 2) (k - 1) := by
  have h := ramsey_upper_erdos_szekeres k k hk hk
  have heq : k + k - 2 = 2 * k - 2 := by omega
  rw [heq] at h
  exact_mod_cast h
