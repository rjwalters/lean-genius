/-
# Unit n-Ball Volumes Tend to Zero

## Open Question: area-of-circle-oq-01-oq-02-oq-01-oq-01-oq-01

**Question**: Does ω_n → 0 as n → ∞?

**Answer**: YES. The even subsequence ω_{2k} = π^k/k! → 0 (terms of the
convergent series e^π), and ω_{2k+1} ≤ 2·ω_{2k} → 0. Combined, ω_n → 0.

## Proof Strategy

1. **omega_even_formula**: ω(2k) = π^k/k! (induction via ω_{n+2} = 2π/(n+2)·ω_n)
2. **omega_odd_le_two_even**: ω(2k+1) ≤ 2·ω(2k) (induction: arithmetic squeeze)
3. **omega_tendsto_zero**: ω(n) ≤ 2·π^(n/2)/(n/2)! → 0 by squeeze theorem

The bound in step 3 uses: ω(n) ≤ 2·ω(2·(n/2)), with n/2 → ∞ and π^k/k! → 0.

## Parent File

AreaOfCircleOQ01OQ02OQ01OQ01.lean defines ω_n = π^(n/2)/Γ(n/2+1) and proves
the recurrence ω_{n+2} = (2π/(n+2))·ω_n with ω_0 = 1, ω_1 = 2.
-/

import Proofs.AreaOfCircleOQ01OQ02OQ01OQ01
import Mathlib.Analysis.SpecificLimits.Basic

open Real Filter Nat UnitBallRecurrence

namespace BallVolumeTendsto

-- ============================================================
-- PART I: Even Subsequence Formula  ω(2k) = π^k / k!
-- ============================================================

/-- **Even formula**: ω(2k) = π^k / k! for all k : ℕ. -/
theorem omega_even_formula : ∀ k : ℕ, ω (2 * k) = π ^ k / (k ! : ℝ)
  | 0 => by simp [omega_zero]
  | k + 1 => by
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, omega_recurrence (2 * k),
        omega_even_formula k, Nat.factorial_succ]
    push_cast
    have h1 : (2 * (↑k : ℝ) + 2) ≠ 0 := by positivity
    have h2 : (↑(k !) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (factorial_pos k).ne'
    have h3 : (↑k : ℝ) + 1 ≠ 0 := by positivity
    field_simp [h1, h2, h3]
    ring

-- ============================================================
-- PART II: Odd Values Bounded by 2 × Even
-- ============================================================

/-- **Odd bound**: ω(2k+1) ≤ 2·ω(2k) for all k : ℕ.

Induction: base ω(1) = 2 = 2·1. Step: using ω(2n+3) = 2π/(2n+3)·ω(2n+1),
the IH ω(2n+1) ≤ 2·ω(2n), and 1/(2n+3) ≤ 1/(2n+2). -/
theorem omega_odd_le_two_even : ∀ k : ℕ, ω (2 * k + 1) ≤ 2 * ω (2 * k)
  | 0 => by simp [omega_zero, omega_one]
  | k + 1 => by
    rw [show 2 * (k + 1) + 1 = 2 * k + 3 from by ring,
        show 2 * (k + 1) = 2 * k + 2 from by ring]
    -- Get the two recurrences
    have hrec_odd : ω (2 * k + 3) = 2 * π / (↑(2 * k + 1) + 2) * ω (2 * k + 1) := by
      have h := omega_recurrence (2 * k + 1)
      rwa [show 2 * k + 1 + 2 = 2 * k + 3 from by ring] at h
    have hrec_even : ω (2 * k + 2) = 2 * π / (↑(2 * k) + 2) * ω (2 * k) :=
      omega_recurrence (2 * k)
    rw [hrec_odd, hrec_even]
    -- After push_cast: denominators become 2k+3 and 2k+2
    push_cast
    -- Fraction inequality: 2π/(2k+3) ≤ 2π/(2k+2) since 2k+2 ≤ 2k+3
    have hfrac : 2 * π / (2 * (↑k : ℝ) + 3) ≤ 2 * π / (2 * ↑k + 2) :=
      div_le_div_of_le_left (by linarith [pi_pos]) (by positivity) (by linarith)
    -- Chain: 2π/(2k+3)·ω(2k+1) ≤ 2π/(2k+2)·ω(2k+1) ≤ 2π/(2k+2)·2·ω(2k)
    have hIH := omega_odd_le_two_even k
    have hω_pos : 0 < ω (2 * k + 1) := omega_pos _
    calc 2 * π / (2 * ↑k + 3) * ω (2 * k + 1)
        ≤ 2 * π / (2 * ↑k + 2) * ω (2 * k + 1) :=
          mul_le_mul_of_nonneg_right hfrac hω_pos.le
      _ ≤ 2 * π / (2 * ↑k + 2) * (2 * ω (2 * k)) :=
          mul_le_mul_of_nonneg_left hIH (div_nonneg (by linarith [pi_pos]) (by positivity))
      _ = 2 * (2 * π / (2 * ↑k + 2) * ω (2 * k)) := by ring

-- ============================================================
-- PART III: Universal Upper Bound
-- ============================================================

/-- For all n, ω(n) ≤ 2·ω(2·(n/2)).
    Even case: trivial (1 ≤ 2). Odd case: omega_odd_le_two_even. -/
theorem omega_le_two_even_half (n : ℕ) : ω n ≤ 2 * ω (2 * (n / 2)) := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · -- n = 2k: need ω(2k) ≤ 2*ω(2k), i.e., 0 ≤ ω(2k)
    have hdiv : 2 * k / 2 = k := by omega
    rw [hdiv]
    linarith [omega_pos (2 * k)]
  · -- n = 2k+1: ω(2k+1) ≤ 2*ω(2k) from omega_odd_le_two_even
    have hdiv : (2 * k + 1) / 2 = k := by omega
    rw [hdiv]
    exact omega_odd_le_two_even k

-- ============================================================
-- PART IV: Main Theorem — ω_n → 0
-- ============================================================

/-- **Main Theorem**: The unit n-ball volume ω_n → 0 as n → ∞.

Proof sketch: bound ω(n) ≤ 2·π^(n/2)/(n/2)!, then squeeze to 0 since
π^k/k! → 0 (terms of e^π) and n/2 → ∞. -/
theorem omega_tendsto_zero : Tendsto ω atTop (nhds 0) := by
  -- Step 1: π^k / k! → 0
  have hπ : Tendsto (fun k : ℕ => π ^ k / (k ! : ℝ)) atTop (nhds 0) := by
    have := (summable_pow_div_factorial ‖π‖).tendsto_atTop_zero
    apply this.congr
    intro n
    simp only [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  -- Step 2: n/2 → ∞ as n → ∞
  have hdiv : Tendsto (fun n : ℕ => n / 2) atTop atTop :=
    tendsto_atTop_atTop_of_monotone
      (fun _ _ h => Nat.div_le_div_right h)
      (fun b => ⟨2 * b, by omega⟩)
  -- Step 3: π^(n/2) / (n/2)! → 0 (by composition)
  have hcomp : Tendsto (fun n : ℕ => π ^ (n / 2) / ((n / 2) ! : ℝ)) atTop (nhds 0) :=
    hπ.comp hdiv
  -- Step 4: 2 · π^(n/2) / (n/2)! → 0
  have hupper : Tendsto (fun n : ℕ => 2 * (π ^ (n / 2) / ((n / 2) ! : ℝ))) atTop (nhds 0) := by
    have h := hcomp.const_mul 2
    simp only [mul_zero] at h
    exact h
  -- Step 5: Squeeze: 0 ≤ ω(n) ≤ 2·π^(n/2)/(n/2)!
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
  · intro n; exact (omega_pos n).le
  · intro n
    have hbound := omega_le_two_even_half n
    rw [omega_even_formula] at hbound
    exact hbound

-- ============================================================
-- PART V: Corollaries
-- ============================================================

/-- The even subsequence ω_{2k} = π^k/k! → 0. -/
theorem omega_even_tendsto_zero :
    Tendsto (fun k : ℕ => ω (2 * k)) atTop (nhds 0) :=
  omega_tendsto_zero.comp (tendsto_atTop_atTop_of_monotone
    (fun _ _ h => by omega) (fun b => ⟨b, by omega⟩))

/-- The odd subsequence ω_{2k+1} → 0. -/
theorem omega_odd_tendsto_zero :
    Tendsto (fun k : ℕ => ω (2 * k + 1)) atTop (nhds 0) :=
  omega_tendsto_zero.comp (tendsto_atTop_atTop_of_monotone
    (fun _ _ h => by omega) (fun b => ⟨b, by omega⟩))

/-- Eventually, all ball volumes are less than 1. -/
theorem omega_eventually_lt_one : ∀ᶠ n in atTop, ω n < 1 := by
  have h := omega_tendsto_zero
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h 1 one_pos
  exact eventually_atTop.mpr ⟨N, fun n hn => by
    have := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_pos (omega_pos n)] at this
    exact this⟩

end BallVolumeTendsto
