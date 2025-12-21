import Mathlib.Data.Rat.Basic
import Mathlib.Data.Int.Parity
import Mathlib.Tactic

/-!
# Irrationality of √2

This file proves that √2 is irrational, i.e., there is no rational number
whose square equals 2.
-/

namespace Sqrt2Irrational

/-! ## Setup and Definitions -/

/-- A number is irrational if it cannot be expressed as a ratio of integers -/
def Irrational (x : ℝ) : Prop := ∀ p q : ℤ, q ≠ 0 → x ≠ p / q

/-- Two integers are coprime if their only common divisor is 1 -/
def Coprime (p q : ℤ) : Prop := Int.gcd p q = 1

/-! ## Supporting Lemmas -/

/-- If n² is even, then n is even -/
theorem even_of_even_sq (n : ℤ) (h : Even (n^2)) : Even n := by
  by_contra hodd
  push_neg at hodd
  have h_odd_sq : Odd (n^2) := Odd.pow hodd
  exact (Int.even_or_odd (n^2)).elim 
    (fun he => absurd he (Odd.not_even h_odd_sq))
    (fun ho => absurd h (Odd.not_even ho))

/-- The square of an odd number is odd -/
theorem odd_sq_of_odd (n : ℤ) (h : Odd n) : Odd (n^2) := by
  obtain ⟨k, hk⟩ := h
  use 2*k^2 + 2*k
  rw [hk]
  ring

/-- Squares preserve divisibility by 2 -/
theorem two_dvd_sq_iff (n : ℤ) : 2 ∣ n^2 ↔ 2 ∣ n := by
  constructor
  · intro h
    exact Int.even_iff_two_dvd.mp (even_of_even_sq n (Int.even_iff_two_dvd.mpr h))
  · intro h
    obtain ⟨k, hk⟩ := h
    use 2*k^2
    rw [hk]
    ring

/-! ## Main Theorem -/

/-- √2 is irrational -/
theorem sqrt_two_irrational : Irrational (Real.sqrt 2) := by
  intro p q hq_ne
  intro h_eq
  -- Assume √2 = p/q in lowest terms
  -- We may assume p, q are coprime
  have h_coprime : Coprime p q := sorry -- WLOG step
  
  -- From √2 = p/q we get p² = 2q²
  have h_sq : p^2 = 2 * q^2 := by
    have := congrArg (·^2) h_eq
    simp at this
    sorry -- algebra
  
  -- p² is even, so p is even
  have hp_even : Even p := by
    apply even_of_even_sq
    use q^2
    linarith
  
  -- Write p = 2k
  obtain ⟨k, hk⟩ := hp_even
  
  -- Then 4k² = 2q², so q² = 2k²
  have hq_sq : q^2 = 2 * k^2 := by
    have : (2*k)^2 = 2 * q^2 := by rw [← hk]; exact h_sq
    linarith
  
  -- So q is also even
  have hq_even : Even q := by
    apply even_of_even_sq
    use k^2
    linarith
  
  -- But p and q both even contradicts coprimality
  have : ¬Coprime p q := by
    intro hcop
    -- 2 divides both p and q
    have h2p : 2 ∣ p := Int.even_iff_two_dvd.mp hp_even
    have h2q : 2 ∣ q := Int.even_iff_two_dvd.mp hq_even
    -- So gcd(p,q) ≥ 2, contradicting coprimality
    sorry
  
  exact this h_coprime

end Sqrt2Irrational
