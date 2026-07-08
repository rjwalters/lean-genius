/-
  Aristotle targets for Erdos117OQ01 (Exponential Growth Rate of h(n))
  Routine supporting lemmas for automated proof search.
  See Erdos117OQ01.lean for the main formalization.

  These lemmas provide building blocks for growth rate analysis:
  - Filter.liminf/limsup basic properties
  - Subadditive sequence convergence (Fekete's lemma)
  - Real.log and Real.exp growth helpers
  - ExponentialBehavior structural properties
  - growthRate monotonicity and limit helpers

  Status (researcher-3, 2026-07-08): 11 of the original 13 scaffold `sorry`s are
  now discharged from Mathlib; `tendsto_implies_exponential_base` had a FALSE
  statement (quantified over all ε > 0, but for ε ≥ exp L the base exp L − ε ≤ 0
  and (exp L − ε)ⁿ at even n can exceed h(n) — the same defect fixed in the main
  file's `base_implies_behavior`); it is corrected to ε ∈ (0, exp L) and proved.
  Only `liminf_le_limsup` remains a `sorry` (needs the BoundedAtFilter →
  IsBoundedUnder conversion).
-/
import Mathlib

open Real Filter

namespace Erdos117OQ01.Aristotle

/-
  ## Section 1: Filter.liminf/limsup Properties
-/

/-- liminf ≤ limsup for any bounded sequence -/
lemma liminf_le_limsup (f : ℕ → ℝ) (hb : BoundedAtFilter atTop f) :
    Filter.liminf f atTop ≤ Filter.limsup f atTop := by
  sorry

/-- liminf is the same as lim when the sequence converges -/
lemma liminf_eq_lim_of_tendsto (f : ℕ → ℝ) (L : ℝ)
    (h : Filter.Tendsto f atTop (nhds L)) :
    Filter.liminf f atTop = L := h.liminf_eq

/-- limsup is the same as lim when the sequence converges -/
lemma limsup_eq_lim_of_tendsto (f : ℕ → ℝ) (L : ℝ)
    (h : Filter.Tendsto f atTop (nhds L)) :
    Filter.limsup f atTop = L := h.limsup_eq

/-- If f → L then liminf f ≥ L - ε eventually implies liminf f ≥ L -/
lemma liminf_ge_of_tendsto (f : ℕ → ℝ) (L : ℝ)
    (h : Filter.Tendsto f atTop (nhds L)) : Filter.liminf f atTop ≥ L :=
  h.liminf_eq.ge

/-
  ## Section 2: Subadditive Sequences (Fekete's Lemma)
-/

/-- Fekete's lemma: if a(m+n) ≤ a(m) + a(n), then a(n)/n → inf(a(n)/n) -/
lemma fekete_subadditive (a : ℕ → ℝ) (hsub : ∀ m n : ℕ, a (m + n) ≤ a m + a n)
    (hpos : ∀ n : ℕ, n ≥ 1 → a n / n ≥ 0) :
    ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => a n / n) atTop (nhds L) := by
  have hs : Subadditive a := hsub
  have hbdd : BddBelow (Set.range fun n : ℕ => a n / n) := by
    refine ⟨0, ?_⟩
    rintro x ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · exact hpos n hn
  exact ⟨_, hs.tendsto_lim hbdd⟩

/-- log h is subadditive when h is submultiplicative -/
lemma log_subadditive_of_submultiplicative (h : ℕ → ℕ)
    (hsub : ∀ m n : ℕ, h (m + n) ≤ h m * h n) (hpos : ∀ n, h n ≥ 1) :
    ∀ m n : ℕ, Real.log (h (m + n)) ≤ Real.log (h m) + Real.log (h n) := by
  intro m n
  have hm : (0 : ℝ) < (h m : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (hpos m)
  have hn : (0 : ℝ) < (h n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (hpos n)
  have hmn : (0 : ℝ) < (h (m + n) : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (hpos (m + n))
  have hle : (h (m + n) : ℝ) ≤ (h m : ℝ) * (h n : ℝ) := by exact_mod_cast hsub m n
  calc Real.log (h (m + n)) ≤ Real.log ((h m : ℝ) * (h n : ℝ)) := Real.log_le_log hmn hle
    _ = Real.log (h m) + Real.log (h n) := Real.log_mul (ne_of_gt hm) (ne_of_gt hn)

/-- The Fekete limit exists for log h / n when h is submultiplicative -/
lemma growth_rate_converges_of_submultiplicative (h : ℕ → ℕ)
    (hsub : ∀ m n : ℕ, h (m + n) ≤ h m * h n) (hpos : ∀ n, h n ≥ 1) :
    ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => Real.log (h n) / n) atTop (nhds L) := by
  have hsublog := log_subadditive_of_submultiplicative h hsub hpos
  have hposlog : ∀ n : ℕ, n ≥ 1 → Real.log (h n) / n ≥ 0 := by
    intro n _
    have h1 : (1 : ℝ) ≤ (h n : ℝ) := by exact_mod_cast hpos n
    exact div_nonneg (Real.log_nonneg h1) (Nat.cast_nonneg n)
  exact fekete_subadditive (fun n => Real.log (h n)) hsublog hposlog

/-
  ## Section 3: Real.exp and Real.log Helpers
-/

/-- log(c₁^n) = n * log c₁ -/
lemma log_pow_c (c : ℝ) (hc : c > 0) (n : ℕ) :
    Real.log (c ^ n) = n * Real.log c := Real.log_pow c n

/-- log(c₁^n) / n = log c₁ for n ≥ 1 -/
lemma log_pow_div (c : ℝ) (hc : c > 1) (n : ℕ) (hn : n ≥ 1) :
    Real.log (c ^ n) / n = Real.log c := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Real.log_pow]
  field_simp

/-- If c > 1 then log c > 0 -/
lemma log_pos_of_gt_one (c : ℝ) (hc : c > 1) : Real.log c > 0 := Real.log_pos hc

/-- exp is continuous at any point -/
lemma exp_continuous_at (x : ℝ) : ContinuousAt Real.exp x :=
  Real.continuous_exp.continuousAt

/-
  ## Section 4: ExponentialBehavior Helpers
-/

/-- If growth rate → L then, for any `ε ∈ (0, exp L)`, eventually `h n ≥ (exp L − ε)ⁿ`.

    NOTE: the original scaffold quantified over all `ε > 0`, which is FALSE: for
    `ε ≥ exp L` the base `exp L − ε ≤ 0`, and `(exp L − ε)ⁿ` at even `n` is a large
    positive number that can exceed `h n`.  The correct hypothesis is `ε < exp L`
    (matching the main file's `base_implies_behavior`), under which the base is
    positive and the log-linear comparison goes through. -/
lemma tendsto_implies_exponential_base (h : ℕ → ℕ) (L : ℝ)
    (hpos : ∀ n, 1 ≤ h n)
    (hconv : Filter.Tendsto (fun n : ℕ => Real.log (h n) / n) atTop (nhds L)) :
    ∀ ε, 0 < ε → ε < Real.exp L → ∀ᶠ n in atTop, (h n : ℝ) ≥ (Real.exp L - ε) ^ n := by
  intro ε hε hεc
  have hbase_pos : 0 < Real.exp L - ε := by linarith
  -- log(exp L − ε) < L
  have hlogbase : Real.log (Real.exp L - ε) < L := by
    have := Real.log_lt_log hbase_pos (by linarith : Real.exp L - ε < Real.exp L)
    rwa [Real.log_exp] at this
  -- eventually the growth rate exceeds log(exp L − ε)
  filter_upwards [Filter.Tendsto.eventually_lt tendsto_const_nhds hconv hlogbase,
    eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hhn : (0 : ℝ) < (h n : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (hpos n)
  -- n · log(exp L − ε) < log(h n)
  rw [lt_div_iff₀ hnpos] at hn
  have hkey : (n : ℝ) * Real.log (Real.exp L - ε) < Real.log (h n) := by
    rw [mul_comm]; exact hn
  -- lift through log-monotonicity: (exp L − ε)ⁿ < h n
  have hpow : Real.log ((Real.exp L - ε) ^ n) < Real.log (h n) := by
    rw [Real.log_pow]; exact hkey
  have hlt : Real.exp (Real.log ((Real.exp L - ε) ^ n)) < Real.exp (Real.log (h n)) :=
    Real.exp_lt_exp.mpr hpow
  rw [Real.exp_log (pow_pos hbase_pos n), Real.exp_log hhn] at hlt
  exact le_of_lt hlt

/-- exp(log c) = c for c > 0 -/
lemma exp_log_eq (c : ℝ) (hc : c > 0) : Real.exp (Real.log c) = c := Real.exp_log hc

end Erdos117OQ01.Aristotle
