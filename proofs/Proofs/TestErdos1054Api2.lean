/-
Test: divisors of 2p for odd prime p
-/
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

open Nat Finset

-- Key structural lemma: divisors of 2p are exactly {1, 2, p, 2p}
theorem div_2p_classification (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) (d : ℕ)
    (hd : d ∣ 2 * p) (hd_pos : d ≥ 1) :
    d = 1 ∨ d = 2 ∨ d = p ∨ d = 2 * p := by
  have hp_odd : ¬ 2 ∣ p := by
    intro h2p
    have := hp.eq_one_or_self_of_dvd 2 h2p
    omega
  by_cases hd_even : 2 ∣ d
  · obtain ⟨e, he⟩ := hd_even
    subst he
    have he_dvd : e ∣ p := by
      have : 2 * e ∣ 2 * p := hd
      exact (Nat.mul_dvd_mul_iff_left (by omega : 2 > 0)).mp this
    rcases hp.eq_one_or_self_of_dvd e he_dvd with h | h
    · right; left; omega
    · right; right; right; omega
  · -- d is odd and divides 2p
    -- Since d is odd and divides 2*p, and gcd(d,2) = 1, we get d | p
    have hcop : Nat.Coprime d 2 := by
      rw [Nat.coprime_comm]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hd_even
    have hd_dvd_p : d ∣ p := by
      rw [mul_comm] at hd
      exact hcop.dvd_of_dvd_mul_right hd
    rcases hp.eq_one_or_self_of_dvd d hd_dvd_p with h | h
    · left; exact h
    · right; right; left; exact h
