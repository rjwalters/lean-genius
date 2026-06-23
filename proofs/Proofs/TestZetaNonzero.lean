import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic

set_option maxHeartbeats 400000

noncomputable section

open Complex Real Set Filter Topology Nat ArithmeticFunction

-- Step 1: Even-indexed Bernoulli numbers are nonzero (for index ≥ 2)
-- Proof: ζ(2k) ≠ 0 (since Re(2k) > 1), and ζ(2k) = [stuff] * B_{2k}, so B_{2k} ≠ 0.
lemma bernoulli_two_mul_ne_zero {k : ℕ} (hk : k ≠ 0) :
    bernoulli (2 * k) ≠ 0 := by
  intro h
  have hzeta := riemannZeta_two_mul_nat hk
  have hzero : riemannZeta (2 * (k : ℂ)) = 0 := by
    rw [hzeta]; simp [h]
  have hre : 1 < (2 * (k : ℂ)).re := by
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero]
    exact_mod_cast show 1 < 2 * k by omega
  exact absurd hzero (riemannZeta_ne_zero_of_one_lt_re hre)

-- Step 2: ζ at odd negative integers is nonzero
-- Proof: ζ(-(2k+1)) = (-1)^(2k+1) * B_{2k+2} / (2k+2), and B_{2k+2} ≠ 0.
lemma riemannZeta_neg_odd_ne_zero {n : ℕ} (hn : Odd n) :
    riemannZeta (-(n : ℂ)) ≠ 0 := by
  rw [riemannZeta_neg_nat_eq_bernoulli n]
  obtain ⟨k, hk⟩ := hn
  have hn1 : n + 1 = 2 * (k + 1) := by omega
  have hb : bernoulli (n + 1) ≠ 0 := by
    rw [hn1]; exact bernoulli_two_mul_ne_zero (by omega)
  apply div_ne_zero
  · apply mul_ne_zero
    · exact pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0)
    · exact_mod_cast hb
  · exact_mod_cast show (n : ℤ) + 1 ≠ 0 by omega

-- Step 3: ζ(-n) = 0 implies n is a positive even number (trivial zero)
-- This combines: ζ(0) = -1/2 ≠ 0, ζ(-odd) ≠ 0, ζ(-2m) = 0 for m ≥ 1
lemma riemannZeta_neg_nat_eq_zero_of_zero {n : ℕ} (hn : riemannZeta (-(n : ℂ)) = 0) :
    ∃ m : ℕ, n = 2 * (m + 1) := by
  -- n = 0: ζ(0) = -1/2 ≠ 0
  by_cases hn0 : n = 0
  · subst hn0; simp [riemannZeta_zero] at hn
  -- n ≥ 1
  by_cases hodd : Odd n
  · exact absurd hn (riemannZeta_neg_odd_ne_zero hodd)
  · -- n is even: n = 2*m for some m
    rw [Nat.not_odd_iff_even] at hodd
    obtain ⟨m, hm⟩ := hodd
    -- n = 2*m, and n ≥ 1, so m ≥ 1
    have hm_pos : m ≥ 1 := by omega
    exact ⟨m - 1, by omega⟩

-- Step 4: The main proof for zero_in_strip_of_zero (Re(s) > 0 direction)
-- If ζ(s) = 0 and s is not a trivial zero, then Re(s) > 0.
-- This is needed in the actual RiemannHypothesis.lean file.

-- Define what we need matching the actual file
def criticalStrip' : Set ℂ := {s : ℂ | 0 < s.re ∧ s.re < 1}
def isTrivialZero' (s : ℂ) : Prop := ∃ n : ℕ, s = -2 * (n + 1)

theorem zero_in_strip_of_zero' (s : ℂ)
    (hs : riemannZeta s = 0) (hnt : ¬isTrivialZero' s) :
    s ∈ criticalStrip' := by
  constructor
  · -- Re(s) > 0
    by_contra h_not
    push_neg at h_not
    -- Re(s) ≤ 0. We split on whether s = -↑n for some n : ℕ.
    by_cases h_all : ∀ n : ℕ, s ≠ -↑n
    · -- Case: s ≠ -↑n for all n. Use functional equation.
      have h_ne_one : s ≠ 1 := by
        intro heq
        have : (1 : ℂ).re ≤ 0 := heq ▸ h_not
        simp at this
      have h_fe := riemannZeta_one_sub h_all h_ne_one
      -- ζ(1-s) = 2*(2π)^(-s) * Γ(s) * cos(πs/2) * ζ(s) = 0 (since ζ(s) = 0)
      have h_zero_1ms : riemannZeta (1 - s) = 0 := by
        rw [h_fe]; simp [hs]
      -- But Re(1-s) = 1 - Re(s) ≥ 1 since Re(s) ≤ 0
      have h_re_1ms : 1 ≤ (1 - s).re := by
        simp only [Complex.sub_re, Complex.one_re]; linarith
      -- ζ(1-s) ≠ 0 for Re(1-s) ≥ 1
      exact absurd h_zero_1ms (riemannZeta_ne_zero_of_one_le_re h_re_1ms)
    · -- Case: ∃ n, s = -↑n
      push_neg at h_all
      obtain ⟨n, hn_eq⟩ := h_all
      -- s = -↑n, so ζ(-↑n) = 0
      have h_zeta_n : riemannZeta (-(n : ℂ)) = 0 := by rwa [← hn_eq]
      -- This means n = 2*(m+1) for some m (by our lemma)
      obtain ⟨m, hm⟩ := riemannZeta_neg_nat_eq_zero_of_zero h_zeta_n
      -- So s = -↑(2*(m+1)) = -2*(m+1)
      have : isTrivialZero' s := by
        use m
        rw [hn_eq, hm]
        push_cast
        ring
      exact absurd this hnt
  · -- Re(s) < 1
    by_contra h_not
    push_neg at h_not
    exact absurd hs (riemannZeta_ne_zero_of_one_le_re h_not)
