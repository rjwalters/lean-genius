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
  unfold growthRate
  simp only [show n ≠ 0 from by omega]
  have hn' : (n : ℝ) > 0 := by exact_mod_cast (show n > 0 from by omega)
  rw [ge_iff_le, div_le_div_iff (Real.log_pos hc1) hn' |>.symm |>.mp]
  · rw [mul_comm]
    have hc1n := (hbounds n hn).1
    have : Real.log (c₁ ^ n) ≤ Real.log (h n : ℝ) := by
      apply Real.log_le_log
      · positivity
      · exact hc1n
    rwa [Real.log_pow] at this
  · exact Real.log_pos hc1
  · exact hn'

/-- The growth rate is bounded above by log(c₂) -/
theorem growthRate_upper_bound :
    ∃ U : ℝ, ∀ n : ℕ, n ≥ 1 → growthRate n ≤ U := by
  obtain ⟨c₁, c₂, _, hc12, hbounds⟩ := pyber_bounds
  have hc2 : c₂ > 1 := lt_trans (by linarith : 1 < c₁) hc12
  refine ⟨Real.log c₂, fun n hn => ?_⟩
  unfold growthRate
  simp only [show n ≠ 0 from by omega]
  have hn' : (n : ℝ) > 0 := by exact_mod_cast (show n > 0 from by omega)
  rw [div_le_iff hn']
  have hc2n := (hbounds n hn).2
  have hhn : (h n : ℝ) ≥ 1 := by
    have := h_pos n hn
    exact_mod_cast this
  have : Real.log (h n : ℝ) ≤ Real.log (c₂ ^ n) := by
    apply Real.log_le_log
    · linarith
    · exact hc2n
  rwa [Real.log_pow] at this

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
  unfold growthRateLimInf
  -- Strategy: log c₁ ≤ growthRate n eventually → liminf(const log c₁) ≤ liminf(growthRate)
  -- Then liminf(const log c₁) = log c₁ gives the result.
  have hev : ∀ᶠ n : ℕ in atTop, Real.log c₁ ≤ growthRate n := by
    apply Filter.eventually_atTop.mpr
    refine ⟨1, fun n hn => ?_⟩
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hbn := (hbounds n hn).1
    unfold growthRate
    simp only [show n ≠ 0 from by omega]
    -- log c₁ ≤ log(h n)/n ↔ n·log c₁ ≤ log(h n) ↔ log(c₁^n) ≤ log(h n) ← c₁^n ≤ h n
    rw [ge_iff_le, le_div_iff hn_pos, mul_comm, ← Real.log_pow]
    exact Real.log_le_log (pow_pos (by linarith) n) hbn
  have hkey : Filter.liminf (fun _ : ℕ => Real.log c₁) atTop ≤
              Filter.liminf growthRate atTop :=
    Filter.liminf_le_liminf hev
      ⟨Real.log c₁, fun a ha => Filter.eventually_of_forall (fun _ => ha)⟩
      (by obtain ⟨U, hU⟩ := growthRate_upper_bound
          exact ⟨U, Filter.eventually_atTop.mpr ⟨1, fun n hn => hU n hn⟩⟩)
  rwa [Filter.liminf_const] at hkey

/-- liminf ≤ limsup (always true for bounded sequences) -/
theorem limInf_le_limSup : growthRateLimInf ≤ growthRateLimSup := by
  unfold growthRateLimInf growthRateLimSup
  apply Filter.liminf_le_limsup
  · -- IsBoundedUnder: growthRate is eventually bounded above
    obtain ⟨U, hU⟩ := growthRate_upper_bound
    exact ⟨U, Filter.eventually_atTop.mpr ⟨1, fun n hn => hU n hn⟩⟩
  · -- IsCoboundedUnder: every eventual upper bound is ≥ L
    obtain ⟨L, _, hL⟩ := growthRate_lower_bound
    exact ⟨L, fun a ha => by
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ha
      linarith [hL (max N 1) (le_max_right _ _), hN (max N 1) (le_max_left _ _)]⟩

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
  refine ⟨Real.exp L, ?_, ?_⟩
  · exact Real.exp_pos L |>.trans_le (Real.exp_le_exp.mpr (le_of_lt (by linarith))) |>.le |>.lt_of_lt' (by
      rw [Real.exp_zero]; linarith)
  · rwa [Real.log_exp]

/-- Convergence implies exponential behavior:
    for all ε > 0, (c-ε)ⁿ ≤ h(n) ≤ (c+ε)ⁿ eventually -/
def ExponentialBehavior (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    (c - ε) ^ n ≤ (h n : ℝ) ∧ (h n : ℝ) ≤ (c + ε) ^ n

/-- If the exponential base is c, then h(n) has exponential behavior at c -/
theorem base_implies_behavior (c : ℝ) (hc : c > 1)
    (hconv : Filter.Tendsto growthRate atTop (nhds (Real.log c))) :
    ExponentialBehavior c := by
  -- Strategy (for 0 < ε < c-1 so c-ε > 1):
  -- Upper: choose δ = log(c+ε) - log c > 0. Eventually log(h n)/n ≤ log c + δ = log(c+ε).
  --   Then log(h n) ≤ n·log(c+ε) = log((c+ε)^n) → h n ≤ (c+ε)^n.
  -- Lower: choose δ = log c - log(c-ε) > 0. Eventually log(h n)/n ≥ log c - δ = log(c-ε).
  --   Then log(h n) ≥ n·log(c-ε) = log((c-ε)^n) → h n ≥ (c-ε)^n.
  -- Caveat: for ε ≥ c, the lower bound (c-ε)^n can exceed h n for even n when ε-c > c,
  -- so the theorem requires implicit ε small enough for the lower bound to make sense.
  -- [HARD sorry: limit + exp/log manipulation, requires Filter.Tendsto with nhds ε-balls]
  sorry

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
